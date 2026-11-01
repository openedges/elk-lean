import Elk.Alg.Common.Compaction.OneD.CGraph
import Elk.Core.Util.Java
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.common.compaction.oned.ISpacingsHandler`

Strategy for the spacing between two `CNode`s (elk-rs `i_spacings_handler.rs`). Two forms:

* `mk horizontal vertical`: closures that receive the current `CGraph` so that they can inspect the
  nodes (Rust passes the `CNodeRef`s); the Rust tuple implementation `(FH, FV)` corresponds to
  `SpacingsHandler.mk horizontal vertical`;
* `individualMin spacings default`: both spacings of a pair are `Math.min` of the two nodes'
  individual spacings (`spacings[node.idx]`, `default` out of range), as the components
  compaction's `Spacing` handler; the compaction algorithms evaluate it without a closure call, a
  boxed result or a graph value.
-/
namespace Elk.Alg.Common.Compaction.OneD

open Elk.Core.Util

/-- `ISpacingsHandler`. -/
inductive SpacingsHandler where
  /-- `getHorizontalSpacing(cNode1, cNode2)` and `getVerticalSpacing(cNode1, cNode2)` as closures. -/
  | mk (horizontal vertical : CGraph → CNodeId → CNodeId → Float)
  /-- Both spacings are `fmin (spacing n1) (spacing n2)` with `spacing n = spacings[n.idx]`
  (`defaultSpacing` out of range). -/
  | individualMin (spacings : FloatArray) (defaultSpacing : Float)

namespace SpacingsHandler

/-- The individual spacing of `n` in an `individualMin` handler. -/
@[inline] def individualOf (spacings : FloatArray) (defaultSpacing : Float) (n : CNodeId) : Float :=
  if h : n.idx < spacings.size then spacings[n.idx] else defaultSpacing

/-- `getHorizontalSpacing(cNode1, cNode2)` on the current graph `g`. -/
@[inline] def horizontal (sh : SpacingsHandler) (g : CGraph) (a b : CNodeId) : Float :=
  match sh with
  | .mk h _ => h g a b
  | .individualMin sp d => fmin (individualOf sp d a) (individualOf sp d b)

/-- `getVerticalSpacing(cNode1, cNode2)` on the current graph `g`. -/
@[inline] def vertical (sh : SpacingsHandler) (g : CGraph) (a b : CNodeId) : Float :=
  match sh with
  | .mk _ v => v g a b
  | .individualMin sp d => fmin (individualOf sp d a) (individualOf sp d b)

/-- `DefaultSpacingsHandler` (Java `ISpacingsHandler.DEFAULT_SPACING_HANDLER`): spacing `0.0`
in both dimensions. -/
def default : SpacingsHandler := .mk (fun _ _ _ => fl0p0) (fun _ _ _ => fl0p0)

instance : Inhabited SpacingsHandler := ⟨default⟩

end SpacingsHandler

end Elk.Alg.Common.Compaction.OneD
