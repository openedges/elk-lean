import Elk.Alg.Common.NodeSpacing.CellSystem.Cell
/-!
# `org.eclipse.elk.alg.common.nodespacing.cellsystem.AtomicCell`

A cell without children that only reserves a minimum content area (elk-rs `cellsystem::AtomicCell`).
The data is the `minimumContentAreaSize` of `CellKind.atomic`.
-/
namespace Elk.Alg.Common.NodeSpacing.CellSystem

open Elk Elk.Core.Math

namespace AtomicCell

/-- `AtomicCell.getMinimumWidth()` for the given content size and padding. -/
@[inline] def minimumWidth (minimumContentAreaSize : KVector) (padding : ElkPadding) : Float :=
  minimumContentAreaSize.x + padding.left + padding.right

/-- `AtomicCell.getMinimumHeight()` for the given content size and padding. -/
@[inline] def minimumHeight (minimumContentAreaSize : KVector) (padding : ElkPadding) : Float :=
  minimumContentAreaSize.y + padding.top + padding.bottom

end AtomicCell

namespace CellArena

variable {L : Type}

/-- `new AtomicCell()`: zero padding, zero content size, no size contributions. -/
def createAtomic (a : CellArena L) : CellArena L × CellId :=
  a.add { kind := .atomic {} }

/-- `AtomicCell.getMinimumContentAreaSize()` (zero for non-atomic cells). -/
def minimumContentAreaSize (a : CellArena L) (id : CellId) : KVector :=
  match (a.get id).kind with
  | .atomic s => s
  | _ => {}

/-- elk-rs `AtomicCell::minimum_content_area_size_mut`: updates the content size of an atomic
cell (ignored for other kinds). -/
def modifyMinimumContentAreaSize (a : CellArena L) (id : CellId) (f : KVector → KVector) : CellArena L :=
  a.modify id fun c =>
    match c.kind with
    | .atomic s => { c with kind := .atomic (f s) }
    | _ => c

/-- `AtomicCell.setMinimumContentAreaSize(size, includesPadding)`: if `includesPadding`, the
cell's current padding is subtracted from `size` first. -/
def setMinimumContentAreaSize (a : CellArena L) (id : CellId) (size : KVector) (includesPadding : Bool) :
    CellArena L :=
  a.modify id fun c =>
    match c.kind with
    | .atomic _ =>
      let s := if includesPadding then
          KVector.mk' (size.x - c.padding.left - c.padding.right) (size.y - c.padding.top - c.padding.bottom)
        else size
      { c with kind := .atomic s }
    | _ => c

end CellArena

end Elk.Alg.Common.NodeSpacing.CellSystem
