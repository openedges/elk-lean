import Elk.Alg.Common.NodeSpacing.CellSystem.Cell
/-!
# `org.eclipse.elk.alg.common.nodespacing.cellsystem.ContainerCell`

Shared helpers of the container cells (`StripContainerCell`, `GridContainerCell`); elk-rs
`cellsystem::{min_width_of_cell, min_height_of_cell, apply_horizontal_layout,
apply_vertical_layout}`.

The container algorithms need the minimum size of their children, which is the virtual
`Cell.getMinimumWidth()` / `getMinimumHeight()`. To keep one module per Java class despite
that cross-class recursion, the helpers take the recursive measure as a `CellMeasure`
callback; `CellDispatch.lean` ties the knot (`CellArena.minimumWidth` etc.).
-/
namespace Elk.Alg.Common.NodeSpacing.CellSystem

open Elk Elk.Core.Math Elk.Core.Util

/-- A recursive cell measure (`Cell.getMinimumWidth()` or `getMinimumHeight()`). -/
abbrev CellMeasure (L : Type) := CellArena L → CellId → Float

/-- A recursive container layout (`ContainerCell.layoutChildrenHorizontally()` or
`layoutChildrenVertically()`); a no-op on non-container cells. -/
abbrev CellLayout (L : Type) := CellArena L → CellId → CellArena L

namespace CellArena

variable {L : Type}

/-- `ContainerCell.minWidthOfCell(cell, respectContributionFlag)`: `0` for an empty slot, for a
non-contributing cell (if the flag is respected) and for an atomic cell without content width;
otherwise the cell's minimum width. -/
def minWidthOfCell (a : CellArena L) (minWidth : CellMeasure L) (cell : Option CellId)
    (respectContributionFlag : Bool) : Float :=
  match cell with
  | none => 0.0
  | some c =>
    let cl := a.get c
    if respectContributionFlag && !cl.contributesToMinimumWidth then 0.0
    else match cl.kind with
      | .atomic s => if s.x == 0.0 then 0.0 else minWidth a c
      | _ => minWidth a c

/-- `ContainerCell.minHeightOfCell(cell, respectContributionFlag)`. -/
def minHeightOfCell (a : CellArena L) (minHeight : CellMeasure L) (cell : Option CellId)
    (respectContributionFlag : Bool) : Float :=
  match cell with
  | none => 0.0
  | some c =>
    let cl := a.get c
    if respectContributionFlag && !cl.contributesToMinimumHeight then 0.0
    else match cl.kind with
      | .atomic s => if s.y == 0.0 then 0.0 else minHeight a c
      | _ => minHeight a c

/-- `ContainerCell.applyHorizontalLayout(cell, x, width)` (no-op for an empty slot). -/
def applyHorizontalLayout (a : CellArena L) (cell : Option CellId) (x width : Float) : CellArena L :=
  match cell with
  | none => a
  | some c => a.modifyCellRectangle c fun r => { r with x := x, width := width }

/-- `ContainerCell.applyVerticalLayout(cell, y, height)` (no-op for an empty slot). -/
def applyVerticalLayout (a : CellArena L) (cell : Option CellId) (y height : Float) : CellArena L :=
  match cell with
  | none => a
  | some c => a.modifyCellRectangle c fun r => { r with y := y, height := height }

/-- `StripContainerCell.getGap()` / `GridContainerCell.getGap()` (`0` for other kinds). -/
def gap (a : CellArena L) (id : CellId) : Float :=
  match (a.get id).kind with
  | .strip d => d.gap
  | .grid d => d.gap
  | _ => 0.0

end CellArena

end Elk.Alg.Common.NodeSpacing.CellSystem
