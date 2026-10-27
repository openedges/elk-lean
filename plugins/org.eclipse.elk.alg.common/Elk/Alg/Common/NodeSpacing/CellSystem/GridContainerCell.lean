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

Deviation from Java (following elk-rs): in tabular mode Java passes the same `colWidths` array
to `applyWidthsToRow` for every row and that method adds the gap to it in place, so later rows
see accumulated gaps. elk-rs passes a copy (`[f64; 3]` is `Copy`) to every row; the port does
the same.
-/
namespace Elk.Alg.Common.NodeSpacing.CellSystem

open Elk Elk.Core.Math Elk.Core.Util

namespace CellArena

variable {L : Type}

/-- `new GridContainerCell(tabular, symmetrical, gap)`: nine empty slots. -/
def createGrid (a : CellArena L) (tabular symmetrical : Bool) (gap : Float) : CellArena L × CellId :=
  a.add { kind := .grid { tabular := tabular, symmetrical := symmetrical, gap := gap } }

/-- The grid data of a grid cell (`none` for other kinds). -/
def gridData? (a : CellArena L) (id : CellId) : Option GridCellData :=
  match (a.get id).kind with
  | .grid d => some d
  | _ => none

/-- Updates the grid data of a grid cell (ignored for other kinds). -/
def modifyGridData (a : CellArena L) (id : CellId) (f : GridCellData → GridCellData) : CellArena L :=
  a.modify id fun c =>
    match c.kind with
    | .grid d => { c with kind := .grid (f d) }
    | _ => c

/-- `GridContainerCell.getCell(row, col)` (`none` for an empty slot or a non-grid cell). -/
def getGridCell (a : CellArena L) (id : CellId) (row col : ContainerArea) : Option CellId :=
  match a.gridData? id with
  | some d => (d.cells[3 * row.index + col.index]?).getD none
  | none => none

/-- `GridContainerCell.setCell(row, col, cell)` (`none` clears the slot). -/
def setGridCell (a : CellArena L) (id : CellId) (row col : ContainerArea) (cell : Option CellId) : CellArena L :=
  a.modifyGridData id fun d => { d with cells := d.cells.setIfInBounds (3 * row.index + col.index) cell }

/-- `GridContainerCell.setCenterCellMinimumSize(minimumSize)`. -/
def setCenterCellMinimumSize (a : CellArena L) (id : CellId) (minimumSize : KVector) : CellArena L :=
  a.modifyGridData id fun d => { d with centerCellMinimumSize := some minimumSize }

/-- `GridContainerCell.setOnlyCenterCellContributesToMinimumSize(contribution)`. -/
def setOnlyCenterCellContributesToMinimumSize (a : CellArena L) (id : CellId) (b : Bool) : CellArena L :=
  a.modifyGridData id fun d => { d with onlyCenterCellContributes := b }

/-- `GridContainerCell.getCenterCellRectangle()`: the area left free by the outer rows and
columns, valid once both `layoutChildren*` ran (zero rectangle for non-grid cells). -/
def centerCellRectangle (a : CellArena L) (id : CellId) : ElkRectangle :=
  match a.gridData? id with
  | some d => d.centerCellRect
  | none => {}

end CellArena

namespace GridContainerCell

variable {L : Type}

/-- Child at `(row, col)` given as slot indices. -/
@[inline] private def slot (d : GridCellData) (row col : Nat) : Option CellId :=
  (d.cells[3 * row + col]?).getD none

/-- `GridContainerCell.minWidthOfColumn(column, row, respectContributionFlag)`: the maximum
minimum width of the column over all rows (`row = none`) or of the given row's cell; the center
column also respects the center cell minimum size. -/
def minWidthOfColumn (a : CellArena L) (minWidth : CellMeasure L) (d : GridCellData) (column : ContainerArea)
    (row : Option ContainerArea) (respectContributionFlag : Bool) : Float := Id.run do
  let mut maxMinWidth := 0.0
  match row with
  | none =>
    for rowIndex in [0:3] do
      maxMinWidth := fmax maxMinWidth (a.minWidthOfCell minWidth (slot d rowIndex column.index) respectContributionFlag)
  | some r =>
    maxMinWidth := a.minWidthOfCell minWidth (slot d r.index column.index) respectContributionFlag
  if column == .center then
    if let some minSize := d.centerCellMinimumSize then
      maxMinWidth := fmax maxMinWidth minSize.x
  return maxMinWidth

/-- `GridContainerCell.minColumnWidths(row, respectContributionFlag)` with symmetry applied. -/
def minColumnWidths (a : CellArena L) (minWidth : CellMeasure L) (d : GridCellData) (row : Option ContainerArea)
    (respectContributionFlag : Bool) : Float × Float × Float :=
  let w0 := minWidthOfColumn a minWidth d .begin row respectContributionFlag
  let w1 := minWidthOfColumn a minWidth d .center row respectContributionFlag
  let w2 := minWidthOfColumn a minWidth d .«end» row respectContributionFlag
  if d.symmetrical then
    let w0 := fmax w0 w2
    (w0, w1, w0)
  else (w0, w1, w2)

/-- `GridContainerCell.minHeightOfRow(row, respectContributionFlag)`. -/
def minHeightOfRow (a : CellArena L) (minHeight : CellMeasure L) (d : GridCellData) (row : ContainerArea)
    (respectContributionFlag : Bool) : Float := Id.run do
  let mut maxMinHeight := 0.0
  for column in [0:3] do
    maxMinHeight := fmax maxMinHeight (a.minHeightOfCell minHeight (slot d row.index column) respectContributionFlag)
  if row == .center then
    if let some minSize := d.centerCellMinimumSize then
      maxMinHeight := fmax maxMinHeight minSize.y
  return maxMinHeight

/-- `GridContainerCell.minRowHeights(respectContributionFlag)` with symmetry applied. -/
def minRowHeights (a : CellArena L) (minHeight : CellMeasure L) (d : GridCellData)
    (respectContributionFlag : Bool) : Float × Float × Float :=
  let h0 := minHeightOfRow a minHeight d .begin respectContributionFlag
  let h1 := minHeightOfRow a minHeight d .center respectContributionFlag
  let h2 := minHeightOfRow a minHeight d .«end» respectContributionFlag
  if d.symmetrical then
    let h0 := fmax h0 h2
    (h0, h1, h0)
  else (h0, h1, h2)

/-- `GridContainerCell.sumWithGaps(values)`: sum of the positive values plus `gap` between each
pair of them. -/
def sumWithGaps (d : GridCellData) (values : Float × Float × Float) : Float := Id.run do
  let (v0, v1, v2) := values
  let mut sum := 0.0
  let mut activeComponents : Nat := 0
  for v in #[v0, v1, v2] do
    if v > 0.0 then
      sum := sum + v
      activeComponents := activeComponents + 1
  if activeComponents > 1 then
    sum := sum + d.gap * (activeComponents - 1).toFloat
  return sum

/-- `GridContainerCell.getMinimumWidth()`. -/
def minimumWidth (a : CellArena L) (minWidth : CellMeasure L) (padding : ElkPadding) (d : GridCellData) :
    Float := Id.run do
  let mut width := 0.0
  if d.onlyCenterCellContributes then
    -- Check if an explicit minimum size for the center cell was set
    if let some minSize := d.centerCellMinimumSize then
      width := minSize.x
    else if let some c := slot d 1 1 then
      width := minWidth a c
  else if d.tabular then
    -- Use aggregated widths
    width := sumWithGaps d (minColumnWidths a minWidth d none true)
  else
    -- Use maximum width over each row
    for area in ContainerArea.values do
      width := fmax width (sumWithGaps d (minColumnWidths a minWidth d (some area) true))
  return if width > 0.0 then width + padding.left + padding.right else 0.0

/-- `GridContainerCell.getMinimumHeight()`. -/
def minimumHeight (a : CellArena L) (minHeight : CellMeasure L) (padding : ElkPadding) (d : GridCellData) :
    Float := Id.run do
  let mut height := 0.0
  if d.onlyCenterCellContributes then
    if let some minSize := d.centerCellMinimumSize then
      height := minSize.y
    else if let some c := slot d 1 1 then
      height := minHeight a c
  else
    -- Minimum height of the different rows (independent of tabular mode)
    height := sumWithGaps d (minRowHeights a minHeight d true)
  return if height > 0.0 then height + padding.top + padding.bottom else 0.0

/-- `GridContainerCell.applyWidthToColumn(column, x, colWidths)`: every cell of the column. -/
def applyWidthToColumn (a : CellArena L) (d : GridCellData) (column : ContainerArea) (x width : Float) :
    CellArena L := Id.run do
  let mut a := a
  for row in [0:3] do
    a := a.applyHorizontalLayout (slot d row column.index) x width
  return a

/-- `GridContainerCell.applyHeightToRow(row, y, rowHeights)`: every cell of the row. -/
def applyHeightToRow (a : CellArena L) (d : GridCellData) (row : ContainerArea) (y height : Float) :
    CellArena L := Id.run do
  let mut a := a
  for column in [0:3] do
    a := a.applyVerticalLayout (slot d row.index column) y height
  return a

/-- `GridContainerCell.applyWidthsToRow(row, colWidths)`: horizontal coordinates for the columns
(applied to all cells of each column); for the center row also the x/width of the center cell
rectangle. -/
def applyWidthsToRow (a : CellArena L) (id : CellId) (d : GridCellData) (row : ContainerArea)
    (colWidths : Float × Float × Float) : CellArena L := Id.run do
  let cellRectangle := a.cellRectangle id
  let cellPadding := a.padding id
  let (w0, w1, w2) := colWidths
  let mut w0 := w0
  let mut w1 := w1
  let mut w2 := w2
  let mut a := a
  -- Left column is left-aligned with our content area, right column is right-aligned
  a := applyWidthToColumn a d .begin (cellRectangle.x + cellPadding.left) w0
  a := applyWidthToColumn a d .«end» (cellRectangle.x + cellRectangle.width - cellPadding.right - w2) w2
  -- Size of the content area and size of the available space in the content area
  let mut freeContentAreaWidth := cellRectangle.width - cellPadding.left - cellPadding.right
  if w0 > 0.0 then
    w0 := w0 + d.gap
    freeContentAreaWidth := freeContentAreaWidth - w0
  if w2 > 0.0 then
    w2 := w2 + d.gap
    freeContentAreaWidth := freeContentAreaWidth - w2
  -- Compute how wide the center cell can be
  let centerWidth := fmax 0.0 freeContentAreaWidth
  -- If the available space is larger than the current size of the center cell, enlarge it
  w1 := fmax w1 freeContentAreaWidth
  -- Place the center cell, possibly enlarging it in the process
  a := applyWidthToColumn a d .center
    (cellRectangle.x + cellPadding.left + w0 - (w1 - freeContentAreaWidth) / 2.0) w1
  -- If this is the center row, remember the center cell's data for the center cell rectangle
  if row == .center then
    let x := cellRectangle.x + cellPadding.left + (centerWidth - freeContentAreaWidth) / 2.0
    a := a.modifyGridData id fun g =>
      { g with centerCellRect := { g.centerCellRect with width := centerWidth, x := x } }
  return a

/-- `GridContainerCell.layoutChildrenHorizontally()`: column widths for all rows at once
(tabular) or per row; does not recurse into children. -/
def layoutChildrenHorizontally (a : CellArena L) (id : CellId) (minWidth : CellMeasure L) : CellArena L := Id.run do
  let some d := a.gridData? id | return a
  let mut a := a
  if d.tabular then
    let colWidths := minColumnWidths a minWidth d none false
    for row in ContainerArea.values do
      a := applyWidthsToRow a id d row colWidths
  else
    for row in ContainerArea.values do
      let colWidths := minColumnWidths a minWidth d (some row) false
      a := applyWidthsToRow a id d row colWidths
  return a

/-- `GridContainerCell.layoutChildrenVertically()`: row heights and the y/height of the center
cell rectangle; does not recurse into children. -/
def layoutChildrenVertically (a : CellArena L) (id : CellId) (minHeight : CellMeasure L) : CellArena L := Id.run do
  let some d := a.gridData? id | return a
  let cellRectangle := a.cellRectangle id
  let cellPadding := a.padding id
  let (h0, h1, h2) := minRowHeights a minHeight d false
  let mut h0 := h0
  let mut h1 := h1
  let mut h2 := h2
  let mut a := a
  -- Top row is top-aligned with our content area, bottom row is bottom-aligned
  a := applyHeightToRow a d .begin (cellRectangle.y + cellPadding.top) h0
  a := applyHeightToRow a d .«end» (cellRectangle.y + cellRectangle.height - cellPadding.bottom - h2) h2
  -- Size of the content area and size of the available space in the content area
  let mut freeContentAreaHeight := cellRectangle.height - cellPadding.top - cellPadding.bottom
  if h0 > 0.0 then
    h0 := h0 + d.gap
    freeContentAreaHeight := freeContentAreaHeight - h0
  if h2 > 0.0 then
    h2 := h2 + d.gap
    freeContentAreaHeight := freeContentAreaHeight - h2
  -- Compute the center cell rectangle
  let centerHeight := fmax 0.0 freeContentAreaHeight
  let centerY := cellRectangle.y + cellPadding.top + (centerHeight - freeContentAreaHeight) / 2.0
  a := a.modifyGridData id fun g =>
    { g with centerCellRect := { g.centerCellRect with height := centerHeight, y := centerY } }
  -- If the available space is larger than the current size of the center cell, enlarge it
  h1 := fmax h1 freeContentAreaHeight
  -- Place the center cell, possibly enlarging it in the process
  a := applyHeightToRow a d .center
    (cellRectangle.y + cellPadding.top + h0 - (h1 - freeContentAreaHeight) / 2.0) h1
  return a

end GridContainerCell

end Elk.Alg.Common.NodeSpacing.CellSystem
