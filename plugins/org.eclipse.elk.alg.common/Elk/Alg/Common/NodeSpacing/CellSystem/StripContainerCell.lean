import Elk.Alg.Common.NodeSpacing.CellSystem.ContainerCell
/-!
# `org.eclipse.elk.alg.common.nodespacing.cellsystem.StripContainerCell`

A container that lays out up to three children along a strip: a `VERTICAL` strip's children are
rows, a `HORIZONTAL` strip's children are columns (elk-rs `cellsystem::StripContainerCell`).
The algorithms take the recursive child measure/layout as callbacks (see `ContainerCell.lean`);
use `CellArena.minimumWidth` / `CellArena.layoutChildrenHorizontally` etc. from
`CellDispatch.lean`.
-/
namespace Elk.Alg.Common.NodeSpacing.CellSystem

open Elk Elk.Core.Math Elk.Core.Util

namespace CellArena

variable {L : Type}

/-- `new StripContainerCell(mode, symmetrical, gap)`: three empty slots. -/
def createStrip (a : CellArena L) (mode : Strip) (symmetrical : Bool) (gap : Float) : CellArena L × CellId :=
  a.add { kind := .strip { containerMode := mode, symmetrical := symmetrical, gap := gap } }

/-- The strip data of a strip cell (`none` for other kinds). -/
def stripData? (a : CellArena L) (id : CellId) : Option StripCellData :=
  match (a.get id).kind with
  | .strip d => some d
  | _ => none

/-- Updates the strip data of a strip cell (ignored for other kinds). -/
def modifyStripData (a : CellArena L) (id : CellId) (f : StripCellData → StripCellData) : CellArena L :=
  a.modify id fun c =>
    match c.kind with
    | .strip d => { c with kind := .strip (f d) }
    | _ => c

/-- `StripContainerCell.getCell(area)` (`none` for an empty slot or a non-strip cell). -/
def getCell (a : CellArena L) (id : CellId) (area : ContainerArea) : Option CellId :=
  match a.stripData? id with
  | some d => (d.cells[area.index]?).getD none
  | none => none

/-- `StripContainerCell.setCell(area, cell)` (`none` clears the slot). -/
def setCell (a : CellArena L) (id : CellId) (area : ContainerArea) (cell : Option CellId) : CellArena L :=
  a.modifyStripData id fun d => { d with cells := d.cells.setIfInBounds area.index cell }

/-- `StripContainerCell.getContainerMode()` (`VERTICAL` for non-strip cells). -/
def containerMode (a : CellArena L) (id : CellId) : Strip :=
  match a.stripData? id with
  | some d => d.containerMode
  | none => .vertical

end CellArena

namespace StripContainerCell

variable {L : Type}

/-- Child in slot `i` (0..2). -/
@[inline] private def slot (d : StripCellData) (i : Nat) : Option CellId := (d.cells[i]?).getD none

/-- `StripContainerCell.minCellWidths(respectContributionFlag)`: widths of the three slots, with
symmetry applied (outer slots get the larger of their widths). -/
def minCellWidths (a : CellArena L) (minWidth : CellMeasure L) (d : StripCellData)
    (respectContributionFlag : Bool) : Float × Float × Float :=
  let w0 := a.minWidthOfCell minWidth (slot d 0) respectContributionFlag
  let w1 := a.minWidthOfCell minWidth (slot d 1) respectContributionFlag
  let w2 := a.minWidthOfCell minWidth (slot d 2) respectContributionFlag
  if d.symmetrical then
    let w0 := fmax w0 w2
    (w0, w1, w0)
  else (w0, w1, w2)

/-- `StripContainerCell.minCellHeights(respectContributionFlag)`. -/
def minCellHeights (a : CellArena L) (minHeight : CellMeasure L) (d : StripCellData)
    (respectContributionFlag : Bool) : Float × Float × Float :=
  let h0 := a.minHeightOfCell minHeight (slot d 0) respectContributionFlag
  let h1 := a.minHeightOfCell minHeight (slot d 1) respectContributionFlag
  let h2 := a.minHeightOfCell minHeight (slot d 2) respectContributionFlag
  if d.symmetrical then
    let h0 := fmax h0 h2
    (h0, h1, h0)
  else (h0, h1, h2)

/-- Sum of the positive values plus `gap` between each pair of them (the active-cell loop of
`getMinimumWidth()` / `getMinimumHeight()`). -/
private def sumActive (gap : Float) (values : Float × Float × Float) : Float := Id.run do
  let (v0, v1, v2) := values
  let mut sum := 0.0
  let mut activeCells : Nat := 0
  for v in #[v0, v1, v2] do
    if v > 0.0 then
      sum := sum + v
      activeCells := activeCells + 1
  if activeCells > 1 then
    sum := sum + gap * (activeCells - 1).toFloat
  return sum

/-- `StripContainerCell.getMinimumWidth()`: vertical strips take the maximum minimum width of
their contributing children, horizontal strips sum their slot widths (with gaps). Padding is
added only to a positive width. -/
def minimumWidth (a : CellArena L) (minWidth : CellMeasure L) (padding : ElkPadding) (d : StripCellData) :
    Float := Id.run do
  let mut width := 0.0
  if d.containerMode == .vertical then
    for cell in d.cells do
      if let some c := cell then
        if a.isContributingToMinimumWidth c then
          width := fmax width (minWidth a c)
  else
    width := sumActive d.gap (minCellWidths a minWidth d true)
  return if width > 0.0 then width + padding.left + padding.right else 0.0

/-- `StripContainerCell.getMinimumHeight()`. -/
def minimumHeight (a : CellArena L) (minHeight : CellMeasure L) (padding : ElkPadding) (d : StripCellData) :
    Float := Id.run do
  let mut height := 0.0
  if d.containerMode == .vertical then
    height := sumActive d.gap (minCellHeights a minHeight d true)
  else
    for cell in d.cells do
      if let some c := cell then
        if a.isContributingToMinimumHeight c then
          height := fmax height (minHeight a c)
  return if height > 0.0 then height + padding.top + padding.bottom else 0.0

/-- `StripContainerCell.layoutChildrenHorizontally()`: computes x coordinates and widths of the
children from the strip's cell rectangle, then lays out container children recursively
(`layoutChild`). -/
def layoutChildrenHorizontally (a : CellArena L) (id : CellId) (minWidth : CellMeasure L)
    (layoutChild : CellLayout L) : CellArena L := Id.run do
  let some d := a.stripData? id | return a
  let cellRectangle := a.cellRectangle id
  let cellPadding := a.padding id
  let mut a := a
  if d.containerMode == .vertical then
    -- Each child cell begins at our left border (plus padding) and is as large as our content area
    let xPos := cellRectangle.x + cellPadding.left
    let width := cellRectangle.width - cellPadding.left - cellPadding.right
    for childCell in d.cells do
      a := a.applyHorizontalLayout childCell xPos width
  else
    let (w0, w1, w2) := minCellWidths a minWidth d false
    let mut w0 := w0
    let mut w1 := w1
    -- Left cell is left-aligned with our content area, right cell is right-aligned
    a := a.applyHorizontalLayout (slot d 0) (cellRectangle.x + cellPadding.left) w0
    a := a.applyHorizontalLayout (slot d 2)
      (cellRectangle.x + cellRectangle.width - cellPadding.right - w2) w2
    -- Size of the content area and size of the available space in the content area
    let mut freeContentAreaWidth := cellRectangle.width - cellPadding.left - cellPadding.right
    if w0 > 0.0 then
      freeContentAreaWidth := freeContentAreaWidth - (w0 + d.gap)
      -- We add the gap here because that will spare us to check if w0 is zero later on
      w0 := w0 + d.gap
    if w2 > 0.0 then
      freeContentAreaWidth := freeContentAreaWidth - (w2 + d.gap)
    -- If the available space is larger than the current size of the center cell, enlarge it
    w1 := fmax w1 freeContentAreaWidth
    -- Place the center cell, possibly enlarging it in the process
    a := a.applyHorizontalLayout (slot d 1)
      (cellRectangle.x + cellPadding.left + w0 - (w1 - freeContentAreaWidth) / 2.0) w1
  -- Layout container cells recursively
  for childCell in d.cells do
    if let some c := childCell then
      a := layoutChild a c
  return a

/-- `StripContainerCell.layoutChildrenVertically()`: computes y coordinates and heights of the
children, then lays out container children recursively (`layoutChild`). -/
def layoutChildrenVertically (a : CellArena L) (id : CellId) (minHeight : CellMeasure L)
    (layoutChild : CellLayout L) : CellArena L := Id.run do
  let some d := a.stripData? id | return a
  let cellRectangle := a.cellRectangle id
  let cellPadding := a.padding id
  let mut a := a
  if d.containerMode == .vertical then
    let (h0, h1, h2) := minCellHeights a minHeight d false
    let mut h0 := h0
    let mut h1 := h1
    -- Top cell is top-aligned with our content area, bottom cell is bottom-aligned
    a := a.applyVerticalLayout (slot d 0) (cellRectangle.y + cellPadding.top) h0
    a := a.applyVerticalLayout (slot d 2)
      (cellRectangle.y + cellRectangle.height - cellPadding.bottom - h2) h2
    -- Size of the content area and size of the available space in the content area
    let mut contentAreaFreeHeight := cellRectangle.height - cellPadding.top - cellPadding.bottom
    if h0 > 0.0 then
      -- We add the gap here because that will spare us to check if h0 is zero later on
      h0 := h0 + d.gap
      contentAreaFreeHeight := contentAreaFreeHeight - h0
    if h2 > 0.0 then
      contentAreaFreeHeight := contentAreaFreeHeight - (h2 + d.gap)
    -- If the available space is larger than the current size of the center cell, enlarge it
    h1 := fmax h1 contentAreaFreeHeight
    -- Place the center cell, possibly enlarging it in the process
    a := a.applyVerticalLayout (slot d 1)
      (cellRectangle.y + cellPadding.top + h0 - (h1 - contentAreaFreeHeight) / 2.0) h1
  else
    -- Each child cell begins at our top border (plus padding) and is as large as our content area
    let yPos := cellRectangle.y + cellPadding.top
    let height := cellRectangle.height - cellPadding.top - cellPadding.bottom
    for childCell in d.cells do
      a := a.applyVerticalLayout childCell yPos height
  -- Layout container cells recursively
  for childCell in d.cells do
    if let some c := childCell then
      a := layoutChild a c
  return a

end StripContainerCell

end Elk.Alg.Common.NodeSpacing.CellSystem
