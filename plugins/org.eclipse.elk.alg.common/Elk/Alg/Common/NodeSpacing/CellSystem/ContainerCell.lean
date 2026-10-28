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

/-- `0.0` as a global constant for the container algorithms (also `StripContainerCell` and
`GridContainerCell`): once those are specialized, literal `0.0`s were evaluated at run time
(`FastFloat.ofScientificImpl`) because common-subexpression elimination shared their arguments
with other constants (PLAN §7.1 item 8). -/
def cellZero : Float := 0.0

/-- `2.0` as a global constant (see `cellZero`). -/
def cellTwo : Float := 2.0

/-- The three per-area values of a strip or a grid row/column (Java `double[3]`, indexed by
`ContainerArea` ordinal). A structure with unboxed `Float` fields instead of a tuple, so that the
measures of `StripContainerCell` / `GridContainerCell` allocate nothing once they are inlined. -/
structure Sizes3 where
  /-- `BEGIN`. -/
  v0 : Float
  /-- `CENTER`. -/
  v1 : Float
  /-- `END`. -/
  v2 : Float

namespace Sizes3

/-- The values with symmetry applied when `symmetrical` (the outer values get the larger of the
two, `Math.max`/`f64::max`). -/
@[inline] def symmetrize (symmetrical : Bool) (v : Sizes3) : Sizes3 :=
  if symmetrical then
    let o := fmax v.v0 v.v2
    ⟨o, v.v1, o⟩
  else v

/-- Sum of the positive values plus `gap` between each pair of them (the active-cell loop of
`StripContainerCell.getMinimumWidth()` / `GridContainerCell.sumWithGaps`, visiting `BEGIN`,
`CENTER`, `END` in that order). -/
@[inline] def sumActive (gap : Float) (v : Sizes3) : Float := Id.run do
  let mut sum := cellZero
  let mut activeCells : Nat := 0
  if v.v0 > cellZero then
    sum := sum + v.v0
    activeCells := activeCells + 1
  if v.v1 > cellZero then
    sum := sum + v.v1
    activeCells := activeCells + 1
  if v.v2 > cellZero then
    sum := sum + v.v2
    activeCells := activeCells + 1
  if activeCells > 1 then
    sum := sum + gap * (activeCells - 1).toFloat
  return sum

end Sizes3

namespace CellArena

variable {L : Type}

/-- `ContainerCell.minWidthOfCell(cell, respectContributionFlag)`: `0` for an empty slot, for a
non-contributing cell (if the flag is respected) and for an atomic cell without content width;
otherwise the cell's minimum width. -/
@[inline] def minWidthOfCell (a : CellArena L) (minWidth : CellMeasure L) (cell : Option CellId)
    (respectContributionFlag : Bool) : Float :=
  match cell with
  | none => cellZero
  | some c =>
    let cl := a.get c
    if respectContributionFlag && !cl.contributesToMinimumWidth then cellZero
    else match cl.kind with
      | .atomic s => if s.x == cellZero then cellZero else minWidth a c
      | _ => minWidth a c

/-- `ContainerCell.minHeightOfCell(cell, respectContributionFlag)`. -/
@[inline] def minHeightOfCell (a : CellArena L) (minHeight : CellMeasure L) (cell : Option CellId)
    (respectContributionFlag : Bool) : Float :=
  match cell with
  | none => cellZero
  | some c =>
    let cl := a.get c
    if respectContributionFlag && !cl.contributesToMinimumHeight then cellZero
    else match cl.kind with
      | .atomic s => if s.y == cellZero then cellZero else minHeight a c
      | _ => minHeight a c

/-- `ContainerCell.applyHorizontalLayout(cell, x, width)` (no-op for an empty slot). -/
@[inline] def applyHorizontalLayout (a : CellArena L) (cell : Option CellId) (x width : Float) : CellArena L :=
  match cell with
  | none => a
  | some c => a.modifyCellRectangle c fun r => { r with x := x, width := width }

/-- `ContainerCell.applyVerticalLayout(cell, y, height)` (no-op for an empty slot). -/
@[inline] def applyVerticalLayout (a : CellArena L) (cell : Option CellId) (y height : Float) : CellArena L :=
  match cell with
  | none => a
  | some c => a.modifyCellRectangle c fun r => { r with y := y, height := height }

/-- `StripContainerCell.getGap()` / `GridContainerCell.getGap()` (`0` for other kinds). -/
def gap (a : CellArena L) (id : CellId) : Float :=
  match (a.get id).kind with
  | .strip d => d.gap
  | .grid d => d.gap
  | _ => cellZero

end CellArena

end Elk.Alg.Common.NodeSpacing.CellSystem
