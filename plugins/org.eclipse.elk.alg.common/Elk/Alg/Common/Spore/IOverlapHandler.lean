import Elk.Alg.Common.Spore.Node
/-!
# `org.eclipse.elk.alg.common.spore.IOverlapHandler`

Interface for an overlap handling function used in the `ScanlineOverlapCheck`
(elk-rs `spore/i_overlap_handler.rs`, a trait over `Fn(&Node, &Node)`).

Representation: the only consumer (`OverlapRemovalLayoutProvider` and its test)
uses the handler to *collect* `TEdge(n1.originalVertex, n2.originalVertex)` into
a set behind an `Arc<Mutex<_>>`. The Lean handler is therefore a pure
accumulator over a caller-chosen state `σ`, threaded through
`ScanlineOverlapCheck.sweep` in call order; no `IO` is needed.
-/
namespace Elk.Alg.Common.Spore

/-- `IOverlapHandler.handle(n1, n2)` as a pure accumulation step. -/
structure IOverlapHandler (σ : Type) where
  /-- This is what is done with overlapping nodes `n1` (the node being inserted) and `n2`. -/
  handle : Node → Node → σ → σ

end Elk.Alg.Common.Spore
