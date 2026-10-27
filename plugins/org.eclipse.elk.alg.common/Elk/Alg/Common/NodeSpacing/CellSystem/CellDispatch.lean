import Elk.Alg.Common.NodeSpacing.CellSystem.AtomicCell
import Elk.Alg.Common.NodeSpacing.CellSystem.LabelCell
import Elk.Alg.Common.NodeSpacing.CellSystem.StripContainerCell
import Elk.Alg.Common.NodeSpacing.CellSystem.GridContainerCell
/-!
# Virtual dispatch of the cell system

The abstract Java methods `Cell.getMinimumWidth()`, `Cell.getMinimumHeight()`,
`ContainerCell.layoutChildrenHorizontally()` and `ContainerCell.layoutChildrenVertically()`
(elk-rs `CellChild::{minimum_width, minimum_height, layout_children_horizontally,
layout_children_vertically}`) over the closed `CellKind`. They recurse through the arena,
hence `partial def`. This is not a Java class of its own; it exists so that every
subclass keeps its own module while the recursion is tied here.
-/
namespace Elk.Alg.Common.NodeSpacing.CellSystem

open Elk Elk.Core.Math

namespace CellArena

variable {L : Type}

/-- `Cell.getMinimumWidth()`: the minimum width of the cell including its padding. -/
partial def minimumWidth (a : CellArena L) (id : CellId) : Float :=
  let c := a.get id
  match c.kind with
  | .atomic s => AtomicCell.minimumWidth s c.padding
  | .label d => LabelCell.minimumWidth d c.padding
  | .strip d => StripContainerCell.minimumWidth a minimumWidth c.padding d
  | .grid d => GridContainerCell.minimumWidth a minimumWidth c.padding d

/-- `Cell.getMinimumHeight()`: the minimum height of the cell including its padding. -/
partial def minimumHeight (a : CellArena L) (id : CellId) : Float :=
  let c := a.get id
  match c.kind with
  | .atomic s => AtomicCell.minimumHeight s c.padding
  | .label d => LabelCell.minimumHeight d c.padding
  | .strip d => StripContainerCell.minimumHeight a minimumHeight c.padding d
  | .grid d => GridContainerCell.minimumHeight a minimumHeight c.padding d

/-- `ContainerCell.layoutChildrenHorizontally()`: computes x coordinates and widths of the
cell's children from its cell rectangle (strips recurse into their children, grids do not).
A no-op for atomic and label cells (elk-rs `CellChild::layout_children_horizontally`). -/
partial def layoutChildrenHorizontally (a : CellArena L) (id : CellId) : CellArena L :=
  match (a.get id).kind with
  | .strip _ => StripContainerCell.layoutChildrenHorizontally a id minimumWidth layoutChildrenHorizontally
  | .grid _ => GridContainerCell.layoutChildrenHorizontally a id minimumWidth
  | _ => a

/-- `ContainerCell.layoutChildrenVertically()`: computes y coordinates and heights of the cell's
children (strips recurse into their children, grids do not). A no-op for atomic and label
cells. -/
partial def layoutChildrenVertically (a : CellArena L) (id : CellId) : CellArena L :=
  match (a.get id).kind with
  | .strip _ => StripContainerCell.layoutChildrenVertically a id minimumHeight layoutChildrenVertically
  | .grid _ => GridContainerCell.layoutChildrenVertically a id minimumHeight
  | _ => a

/-- elk-rs `CellChild::minimum_width` on a possibly empty slot (`0` for `none`). -/
def minimumWidthOpt (a : CellArena L) (id : Option CellId) : Float :=
  match id with | some c => a.minimumWidth c | none => 0.0

/-- elk-rs `CellChild::minimum_height` on a possibly empty slot (`0` for `none`). -/
def minimumHeightOpt (a : CellArena L) (id : Option CellId) : Float :=
  match id with | some c => a.minimumHeight c | none => 0.0

end CellArena

end Elk.Alg.Common.NodeSpacing.CellSystem
