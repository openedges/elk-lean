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
@[inline] def stripData? (a : CellArena L) (id : CellId) : Option StripCellData :=
  match (a.get id).kind with
  | .strip d => some d
  | _ => none

/-- Updates the strip data of a strip cell (ignored for other kinds). -/
@[inline] def modifyStripData (a : CellArena L) (id : CellId) (f : StripCellData → StripCellData) : CellArena L :=
  a.modify id fun c =>
    match c.kind with
    | .strip d => { c with kind := .strip (f d) }
    | _ => c

/-- `StripContainerCell.getCell(area)` (`none` for an empty slot or a non-strip cell). -/
@[inline] def getCell (a : CellArena L) (id : CellId) (area : ContainerArea) : Option CellId :=
  match a.stripData? id with
  | some d => (d.cells[area.index]?).getD none
  | none => none

/-- `StripContainerCell.setCell(area, cell)` (`none` clears the slot). -/
@[inline] def setCell (a : CellArena L) (id : CellId) (area : ContainerArea) (cell : Option CellId) : CellArena L :=
  a.modifyStripData id fun d => { d with cells := d.cells.setIfInBounds area.index cell }

/-- `StripContainerCell.getContainerMode()` (`VERTICAL` for non-strip cells). -/
@[inline] def containerMode (a : CellArena L) (id : CellId) : Strip :=
  match a.stripData? id with
  | some d => d.containerMode
  | none => .vertical

end CellArena

namespace StripContainerCell

variable {L : Type}

/-! The measures and layouts below are `@[inline]`: `CellDispatch` instantiates them with its own
recursive functions, so the child measures become direct calls (no closure call, no boxed
`Float` result) and the per-slot values stay unboxed (`Sizes3`). The three slots are visited in
`BEGIN`, `CENTER`, `END` order like the Java loops over `cells` (a strip always has three
slots). -/

/-- Child in slot `i` (0..2). -/
@[inline] private def slot (d : StripCellData) (i : Nat) : Option CellId := (d.cells[i]?).getD none

/-- `StripContainerCell.minCellWidths(respectContributionFlag)`: widths of the three slots, with
symmetry applied (outer slots get the larger of their widths). -/
@[inline] def minCellWidths (a : CellArena L) (minWidth : CellMeasure L) (d : StripCellData)
    (respectContributionFlag : Bool) : Sizes3 :=
  Sizes3.symmetrize d.symmetrical
    ⟨a.minWidthOfCell minWidth (slot d 0) respectContributionFlag,
     a.minWidthOfCell minWidth (slot d 1) respectContributionFlag,
     a.minWidthOfCell minWidth (slot d 2) respectContributionFlag⟩

/-- `StripContainerCell.minCellHeights(respectContributionFlag)`. -/
@[inline] def minCellHeights (a : CellArena L) (minHeight : CellMeasure L) (d : StripCellData)
    (respectContributionFlag : Bool) : Sizes3 :=
  Sizes3.symmetrize d.symmetrical
    ⟨a.minHeightOfCell minHeight (slot d 0) respectContributionFlag,
     a.minHeightOfCell minHeight (slot d 1) respectContributionFlag,
     a.minHeightOfCell minHeight (slot d 2) respectContributionFlag⟩

/-- One step of the contributing-children maximum of `getMinimumWidth()` (vertical strips). -/
@[inline] private def maxContributingWidth (a : CellArena L) (minWidth : CellMeasure L) (cell : Option CellId)
    (acc : Float) : Float :=
  match cell with
  | some c => if a.isContributingToMinimumWidth c then fmax acc (minWidth a c) else acc
  | none => acc

/-- One step of the contributing-children maximum of `getMinimumHeight()` (horizontal strips). -/
@[inline] private def maxContributingHeight (a : CellArena L) (minHeight : CellMeasure L) (cell : Option CellId)
    (acc : Float) : Float :=
  match cell with
  | some c => if a.isContributingToMinimumHeight c then fmax acc (minHeight a c) else acc
  | none => acc

/-- `StripContainerCell.getMinimumWidth()`: vertical strips take the maximum minimum width of
their contributing children, horizontal strips sum their slot widths (with gaps). Padding is
added only to a positive width. -/
@[specialize] def minimumWidth (a : CellArena L) (minWidth : CellMeasure L) (padding : ElkPadding) (d : StripCellData) :
    Float :=
  let width :=
    if d.containerMode == .vertical then
      maxContributingWidth a minWidth (slot d 2) <|
        maxContributingWidth a minWidth (slot d 1) <|
          maxContributingWidth a minWidth (slot d 0) cellZero
    else
      (minCellWidths a minWidth d true).sumActive d.gap
  if width > cellZero then width + padding.left + padding.right else cellZero

/-- `StripContainerCell.getMinimumHeight()`. -/
@[specialize] def minimumHeight (a : CellArena L) (minHeight : CellMeasure L) (padding : ElkPadding) (d : StripCellData) :
    Float :=
  let height :=
    if d.containerMode == .vertical then
      (minCellHeights a minHeight d true).sumActive d.gap
    else
      maxContributingHeight a minHeight (slot d 2) <|
        maxContributingHeight a minHeight (slot d 1) <|
          maxContributingHeight a minHeight (slot d 0) cellZero
  if height > cellZero then height + padding.top + padding.bottom else cellZero

/-- Lays out the container children of the three slots recursively (`layoutChild`, a no-op on
other cells), in slot order. -/
@[inline] private def layoutSlots (a : CellArena L) (d : StripCellData) (layoutChild : CellLayout L) :
    CellArena L :=
  let a := match slot d 0 with | some c => layoutChild a c | none => a
  let a := match slot d 1 with | some c => layoutChild a c | none => a
  match slot d 2 with | some c => layoutChild a c | none => a

/-- `StripContainerCell.layoutChildrenHorizontally()`: computes x coordinates and widths of the
children from the strip's cell rectangle, then lays out container children recursively
(`layoutChild`). -/
@[specialize] def layoutChildrenHorizontally (a : CellArena L) (id : CellId) (minWidth : CellMeasure L)
    (layoutChild : CellLayout L) : CellArena L := Id.run do
  let some d := a.stripData? id | return a
  let cellRectangle := a.cellRectangle id
  let cellPadding := a.padding id
  let mut a := a
  if d.containerMode == .vertical then
    -- Each child cell begins at our left border (plus padding) and is as large as our content area
    let xPos := cellRectangle.x + cellPadding.left
    let width := cellRectangle.width - cellPadding.left - cellPadding.right
    a := a.applyHorizontalLayout (slot d 0) xPos width
    a := a.applyHorizontalLayout (slot d 1) xPos width
    a := a.applyHorizontalLayout (slot d 2) xPos width
  else
    let ws := minCellWidths a minWidth d false
    let mut w0 := ws.v0
    let mut w1 := ws.v1
    let w2 := ws.v2
    -- Left cell is left-aligned with our content area, right cell is right-aligned
    a := a.applyHorizontalLayout (slot d 0) (cellRectangle.x + cellPadding.left) w0
    a := a.applyHorizontalLayout (slot d 2)
      (cellRectangle.x + cellRectangle.width - cellPadding.right - w2) w2
    -- Size of the content area and size of the available space in the content area
    let mut freeContentAreaWidth := cellRectangle.width - cellPadding.left - cellPadding.right
    if w0 > cellZero then
      freeContentAreaWidth := freeContentAreaWidth - (w0 + d.gap)
      -- We add the gap here because that will spare us to check if w0 is zero later on
      w0 := w0 + d.gap
    if w2 > cellZero then
      freeContentAreaWidth := freeContentAreaWidth - (w2 + d.gap)
    -- If the available space is larger than the current size of the center cell, enlarge it
    w1 := fmax w1 freeContentAreaWidth
    -- Place the center cell, possibly enlarging it in the process
    a := a.applyHorizontalLayout (slot d 1)
      (cellRectangle.x + cellPadding.left + w0 - (w1 - freeContentAreaWidth) / cellTwo) w1
  -- Layout container cells recursively
  return layoutSlots a d layoutChild

/-- `StripContainerCell.layoutChildrenVertically()`: computes y coordinates and heights of the
children, then lays out container children recursively (`layoutChild`). -/
@[specialize] def layoutChildrenVertically (a : CellArena L) (id : CellId) (minHeight : CellMeasure L)
    (layoutChild : CellLayout L) : CellArena L := Id.run do
  let some d := a.stripData? id | return a
  let cellRectangle := a.cellRectangle id
  let cellPadding := a.padding id
  let mut a := a
  if d.containerMode == .vertical then
    let hs := minCellHeights a minHeight d false
    let mut h0 := hs.v0
    let mut h1 := hs.v1
    let h2 := hs.v2
    -- Top cell is top-aligned with our content area, bottom cell is bottom-aligned
    a := a.applyVerticalLayout (slot d 0) (cellRectangle.y + cellPadding.top) h0
    a := a.applyVerticalLayout (slot d 2)
      (cellRectangle.y + cellRectangle.height - cellPadding.bottom - h2) h2
    -- Size of the content area and size of the available space in the content area
    let mut contentAreaFreeHeight := cellRectangle.height - cellPadding.top - cellPadding.bottom
    if h0 > cellZero then
      -- We add the gap here because that will spare us to check if h0 is zero later on
      h0 := h0 + d.gap
      contentAreaFreeHeight := contentAreaFreeHeight - h0
    if h2 > cellZero then
      contentAreaFreeHeight := contentAreaFreeHeight - (h2 + d.gap)
    -- If the available space is larger than the current size of the center cell, enlarge it
    h1 := fmax h1 contentAreaFreeHeight
    -- Place the center cell, possibly enlarging it in the process
    a := a.applyVerticalLayout (slot d 1)
      (cellRectangle.y + cellPadding.top + h0 - (h1 - contentAreaFreeHeight) / cellTwo) h1
  else
    -- Each child cell begins at our top border (plus padding) and is as large as our content area
    let yPos := cellRectangle.y + cellPadding.top
    let height := cellRectangle.height - cellPadding.top - cellPadding.bottom
    a := a.applyVerticalLayout (slot d 0) yPos height
    a := a.applyVerticalLayout (slot d 1) yPos height
    a := a.applyVerticalLayout (slot d 2) yPos height
  -- Layout container cells recursively
  return layoutSlots a d layoutChild

end StripContainerCell

end Elk.Alg.Common.NodeSpacing.CellSystem
