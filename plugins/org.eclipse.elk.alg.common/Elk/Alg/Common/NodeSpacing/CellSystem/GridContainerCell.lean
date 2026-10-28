import Elk.Alg.Common.NodeSpacing.CellSystem.ContainerCell
/-!
# `org.eclipse.elk.alg.common.nodespacing.cellsystem.GridContainerCell`

A container that lays out its children in a 3×3 grid, either in tabular mode (column widths
locked across rows) or not (elk-rs `cellsystem::GridContainerCell`). The algorithms take the
recursive child measure as a callback (see `ContainerCell.lean`); use the dispatching
`CellArena.minimumWidth` / `CellArena.layoutChildrenHorizontally` etc. from `CellDispatch.lean`.

Faithfully reproduced quirks (Java and elk-rs agree):
* `applyWidthToColumn` / `applyHeightToRow` apply to every cell of the column/row, so in
  non-tabular mode the widths of the last row (`END`) end up on all rows.
* Neither `layoutChildrenHorizontally` nor `layoutChildrenVertically` recurses into children.

Like Java (and unlike elk-rs, which passes a copy of its `[f64; 3]` to every row): in tabular mode
the same column widths go to `applyWidthsToRow` for every row and that method updates them in
place (gap added to the outer widths, center width enlarged), so later rows see accumulated gaps.
-/
namespace Elk.Alg.Common.NodeSpacing.CellSystem

open Elk Elk.Core.Math Elk.Core.Util

namespace CellArena

variable {L : Type}

/-- `new GridContainerCell(tabular, symmetrical, gap)`: nine empty slots. -/
def createGrid (a : CellArena L) (tabular symmetrical : Bool) (gap : Float) : CellArena L × CellId :=
  a.add { kind := .grid { tabular := tabular, symmetrical := symmetrical, gap := gap } }

/-- The grid data of a grid cell (`none` for other kinds). -/
@[inline] def gridData? (a : CellArena L) (id : CellId) : Option GridCellData :=
  match (a.get id).kind with
  | .grid d => some d
  | _ => none

/-- Updates the grid data of a grid cell (ignored for other kinds). -/
@[inline] def modifyGridData (a : CellArena L) (id : CellId) (f : GridCellData → GridCellData) : CellArena L :=
  a.modify id fun c =>
    match c.kind with
    | .grid d => { c with kind := .grid (f d) }
    | _ => c

/-- `GridContainerCell.getCell(row, col)` (`none` for an empty slot or a non-grid cell). -/
@[inline] def getGridCell (a : CellArena L) (id : CellId) (row col : ContainerArea) : Option CellId :=
  match a.gridData? id with
  | some d => (d.cells[3 * row.index + col.index]?).getD none
  | none => none

/-- `GridContainerCell.setCell(row, col, cell)` (`none` clears the slot). -/
@[inline] def setGridCell (a : CellArena L) (id : CellId) (row col : ContainerArea) (cell : Option CellId) : CellArena L :=
  a.modifyGridData id fun d => { d with cells := d.cells.setIfInBounds (3 * row.index + col.index) cell }

/-- `GridContainerCell.setCenterCellMinimumSize(minimumSize)`. -/
def setCenterCellMinimumSize (a : CellArena L) (id : CellId) (minimumSize : KVector) : CellArena L :=
  a.modifyGridData id fun d => { d with centerCellMinimumSize := some minimumSize }

/-- `GridContainerCell.setOnlyCenterCellContributesToMinimumSize(contribution)`. -/
def setOnlyCenterCellContributesToMinimumSize (a : CellArena L) (id : CellId) (b : Bool) : CellArena L :=
  a.modifyGridData id fun d => { d with onlyCenterCellContributes := b }

/-- `GridContainerCell.getCenterCellRectangle()`: the area left free by the outer rows and
columns, valid once both `layoutChildren*` ran (zero rectangle for non-grid cells). -/
@[inline] def centerCellRectangle (a : CellArena L) (id : CellId) : ElkRectangle :=
  match a.gridData? id with
  | some d => d.centerCellRect
  | none => {}

end CellArena

namespace GridContainerCell

variable {L : Type}

/-! The measures and layouts below are `@[inline]` for the same reason as those of
`StripContainerCell`: instantiated by `CellDispatch`, the child measures become direct calls and
the per-row/column values stay unboxed (`Sizes3`). Rows and columns are visited in `BEGIN`,
`CENTER`, `END` order like the Java loops (a grid always has nine slots). -/

/-- Child at `(row, col)` given as slot indices. -/
@[inline] private def slot (d : GridCellData) (row col : Nat) : Option CellId :=
  (d.cells[3 * row + col]?).getD none

/-- `GridContainerCell.minWidthOfColumn(column, row, respectContributionFlag)`: the maximum
minimum width of the column (slot index `column`) over all rows (`row = none`) or of the given
row's cell; the center column also respects the center cell minimum size. -/
@[inline] def minWidthOfColumn (a : CellArena L) (minWidth : CellMeasure L) (d : GridCellData) (column : Nat)
    (row : Option ContainerArea) (respectContributionFlag : Bool) : Float :=
  let maxMinWidth := match row with
    | none =>
      let w := fmax cellZero (a.minWidthOfCell minWidth (slot d 0 column) respectContributionFlag)
      let w := fmax w (a.minWidthOfCell minWidth (slot d 1 column) respectContributionFlag)
      fmax w (a.minWidthOfCell minWidth (slot d 2 column) respectContributionFlag)
    | some r => a.minWidthOfCell minWidth (slot d r.index column) respectContributionFlag
  if column == 1 then
    match d.centerCellMinimumSize with
    | some minSize => fmax maxMinWidth minSize.x
    | none => maxMinWidth
  else maxMinWidth

/-- `GridContainerCell.minColumnWidths(row, respectContributionFlag)` with symmetry applied. -/
@[inline] def minColumnWidths (a : CellArena L) (minWidth : CellMeasure L) (d : GridCellData)
    (row : Option ContainerArea) (respectContributionFlag : Bool) : Sizes3 :=
  Sizes3.symmetrize d.symmetrical
    ⟨minWidthOfColumn a minWidth d 0 row respectContributionFlag,
     minWidthOfColumn a minWidth d 1 row respectContributionFlag,
     minWidthOfColumn a minWidth d 2 row respectContributionFlag⟩

/-- `GridContainerCell.minHeightOfRow(row, respectContributionFlag)` (row slot index `row`). -/
@[inline] def minHeightOfRow (a : CellArena L) (minHeight : CellMeasure L) (d : GridCellData) (row : Nat)
    (respectContributionFlag : Bool) : Float :=
  let h := fmax cellZero (a.minHeightOfCell minHeight (slot d row 0) respectContributionFlag)
  let h := fmax h (a.minHeightOfCell minHeight (slot d row 1) respectContributionFlag)
  let maxMinHeight := fmax h (a.minHeightOfCell minHeight (slot d row 2) respectContributionFlag)
  if row == 1 then
    match d.centerCellMinimumSize with
    | some minSize => fmax maxMinHeight minSize.y
    | none => maxMinHeight
  else maxMinHeight

/-- `GridContainerCell.minRowHeights(respectContributionFlag)` with symmetry applied. -/
@[inline] def minRowHeights (a : CellArena L) (minHeight : CellMeasure L) (d : GridCellData)
    (respectContributionFlag : Bool) : Sizes3 :=
  Sizes3.symmetrize d.symmetrical
    ⟨minHeightOfRow a minHeight d 0 respectContributionFlag,
     minHeightOfRow a minHeight d 1 respectContributionFlag,
     minHeightOfRow a minHeight d 2 respectContributionFlag⟩

/-- `GridContainerCell.sumWithGaps(values)`: sum of the positive values plus `gap` between each
pair of them. -/
@[inline] def sumWithGaps (d : GridCellData) (values : Sizes3) : Float :=
  values.sumActive d.gap

/-- `GridContainerCell.getMinimumWidth()`. -/
@[specialize] def minimumWidth (a : CellArena L) (minWidth : CellMeasure L) (padding : ElkPadding) (d : GridCellData) :
    Float :=
  let width :=
    if d.onlyCenterCellContributes then
      -- Check if an explicit minimum size for the center cell was set
      match d.centerCellMinimumSize with
      | some minSize => minSize.x
      | none =>
        match slot d 1 1 with
        | some c => minWidth a c
        | none => cellZero
    else if d.tabular then
      -- Use aggregated widths
      sumWithGaps d (minColumnWidths a minWidth d none true)
    else
      -- Use maximum width over each row
      let w := fmax cellZero (sumWithGaps d (minColumnWidths a minWidth d (some .begin) true))
      let w := fmax w (sumWithGaps d (minColumnWidths a minWidth d (some .center) true))
      fmax w (sumWithGaps d (minColumnWidths a minWidth d (some .«end») true))
  if width > cellZero then width + padding.left + padding.right else cellZero

/-- `GridContainerCell.getMinimumHeight()`. -/
@[specialize] def minimumHeight (a : CellArena L) (minHeight : CellMeasure L) (padding : ElkPadding) (d : GridCellData) :
    Float :=
  let height :=
    if d.onlyCenterCellContributes then
      match d.centerCellMinimumSize with
      | some minSize => minSize.y
      | none =>
        match slot d 1 1 with
        | some c => minHeight a c
        | none => cellZero
    else
      -- Minimum height of the different rows (independent of tabular mode)
      sumWithGaps d (minRowHeights a minHeight d true)
  if height > cellZero then height + padding.top + padding.bottom else cellZero

/-- `GridContainerCell.applyWidthToColumn(column, x, colWidths)`: every cell of the column. -/
@[inline] def applyWidthToColumn (a : CellArena L) (d : GridCellData) (column : Nat) (x width : Float) :
    CellArena L :=
  let a := a.applyHorizontalLayout (slot d 0 column) x width
  let a := a.applyHorizontalLayout (slot d 1 column) x width
  a.applyHorizontalLayout (slot d 2 column) x width

/-- `GridContainerCell.applyHeightToRow(row, y, rowHeights)`: every cell of the row. -/
@[inline] def applyHeightToRow (a : CellArena L) (d : GridCellData) (row : Nat) (y height : Float) :
    CellArena L :=
  let a := a.applyVerticalLayout (slot d row 0) y height
  let a := a.applyVerticalLayout (slot d row 1) y height
  a.applyVerticalLayout (slot d row 2) y height

/-- `GridContainerCell.applyWidthsToRow(row, colWidths)`: horizontal coordinates for the columns
(applied to all cells of each column); for the center row also the x/width of the center cell
rectangle. The three column widths are passed unboxed; like Java, which updates its `colWidths`
array in place (the outer widths get the gap added when positive, the center width is raised to the
free content area width), the updated widths are returned with the arena. -/
def applyWidthsToRowW (a : CellArena L) (id : CellId) (d : GridCellData) (row : ContainerArea)
    (colWidth0 colWidth1 colWidth2 : Float) : CellArena L × Float × Float × Float := Id.run do
  let cellRectangle := a.cellRectangle id
  let cellPadding := a.padding id
  let mut w0 := colWidth0
  let mut w1 := colWidth1
  let mut w2 := colWidth2
  let mut a := a
  -- Left column is left-aligned with our content area, right column is right-aligned
  a := applyWidthToColumn a d 0 (cellRectangle.x + cellPadding.left) w0
  a := applyWidthToColumn a d 2 (cellRectangle.x + cellRectangle.width - cellPadding.right - w2) w2
  -- Size of the content area and size of the available space in the content area
  let mut freeContentAreaWidth := cellRectangle.width - cellPadding.left - cellPadding.right
  if w0 > cellZero then
    w0 := w0 + d.gap
    freeContentAreaWidth := freeContentAreaWidth - w0
  if w2 > cellZero then
    w2 := w2 + d.gap
    freeContentAreaWidth := freeContentAreaWidth - w2
  -- Compute how wide the center cell can be
  let centerWidth := fmax cellZero freeContentAreaWidth
  -- If the available space is larger than the current size of the center cell, enlarge it
  w1 := fmax w1 freeContentAreaWidth
  -- Place the center cell, possibly enlarging it in the process
  a := applyWidthToColumn a d 1
    (cellRectangle.x + cellPadding.left + w0 - (w1 - freeContentAreaWidth) / cellTwo) w1
  -- If this is the center row, remember the center cell's data for the center cell rectangle
  if row == .center then
    let x := cellRectangle.x + cellPadding.left + (centerWidth - freeContentAreaWidth) / cellTwo
    a := a.modifyGridData id fun g =>
      { g with centerCellRect := { g.centerCellRect with width := centerWidth, x := x } }
  return (a, w0, w1, w2)

/-- `GridContainerCell.applyWidthsToRow(row, colWidths)` without the updated widths. -/
@[inline] def applyWidthsToRow (a : CellArena L) (id : CellId) (d : GridCellData) (row : ContainerArea)
    (colWidth0 colWidth1 colWidth2 : Float) : CellArena L :=
  (applyWidthsToRowW a id d row colWidth0 colWidth1 colWidth2).1

/-- `GridContainerCell.layoutChildrenHorizontally()`: column widths for all rows at once
(tabular) or per row; does not recurse into children. -/
@[specialize] def layoutChildrenHorizontally (a : CellArena L) (id : CellId) (minWidth : CellMeasure L) :
    CellArena L :=
  match a.gridData? id with
  | none => a
  | some d =>
    if d.tabular then
      -- Java hands the same `colWidths` array to every row and `applyWidthsToRow` updates it in
      -- place, so the later rows see the widths (gaps added, center enlarged) of the earlier ones
      let w := minColumnWidths a minWidth d none false
      let (a, w0, w1, w2) := applyWidthsToRowW a id d .begin w.v0 w.v1 w.v2
      let (a, w0, w1, w2) := applyWidthsToRowW a id d .center w0 w1 w2
      applyWidthsToRow a id d .«end» w0 w1 w2
    else
      let w := minColumnWidths a minWidth d (some .begin) false
      let a := applyWidthsToRow a id d .begin w.v0 w.v1 w.v2
      let w := minColumnWidths a minWidth d (some .center) false
      let a := applyWidthsToRow a id d .center w.v0 w.v1 w.v2
      let w := minColumnWidths a minWidth d (some .«end») false
      applyWidthsToRow a id d .«end» w.v0 w.v1 w.v2

/-- `GridContainerCell.layoutChildrenVertically()`: row heights and the y/height of the center
cell rectangle; does not recurse into children. -/
@[specialize] def layoutChildrenVertically (a : CellArena L) (id : CellId) (minHeight : CellMeasure L) :
    CellArena L := Id.run do
  let some d := a.gridData? id | return a
  let cellRectangle := a.cellRectangle id
  let cellPadding := a.padding id
  let hs := minRowHeights a minHeight d false
  let mut h0 := hs.v0
  let mut h1 := hs.v1
  let mut h2 := hs.v2
  let mut a := a
  -- Top row is top-aligned with our content area, bottom row is bottom-aligned
  a := applyHeightToRow a d 0 (cellRectangle.y + cellPadding.top) h0
  a := applyHeightToRow a d 2 (cellRectangle.y + cellRectangle.height - cellPadding.bottom - h2) h2
  -- Size of the content area and size of the available space in the content area
  let mut freeContentAreaHeight := cellRectangle.height - cellPadding.top - cellPadding.bottom
  if h0 > cellZero then
    h0 := h0 + d.gap
    freeContentAreaHeight := freeContentAreaHeight - h0
  if h2 > cellZero then
    h2 := h2 + d.gap
    freeContentAreaHeight := freeContentAreaHeight - h2
  -- Compute the center cell rectangle
  let centerHeight := fmax cellZero freeContentAreaHeight
  let centerY := cellRectangle.y + cellPadding.top + (centerHeight - freeContentAreaHeight) / cellTwo
  a := a.modifyGridData id fun g =>
    { g with centerCellRect := { g.centerCellRect with height := centerHeight, y := centerY } }
  -- If the available space is larger than the current size of the center cell, enlarge it
  h1 := fmax h1 freeContentAreaHeight
  -- Place the center cell, possibly enlarging it in the process
  a := applyHeightToRow a d 1
    (cellRectangle.y + cellPadding.top + h0 - (h1 - freeContentAreaHeight) / cellTwo) h1
  return a

end GridContainerCell

end Elk.Alg.Common.NodeSpacing.CellSystem
