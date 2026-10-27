import Elk.Graph
/-!
# `org.eclipse.elk.alg.radial.intermediate.optimization.IEvaluation`

Port of `i_evaluation.rs` (elk-rs).
-/
namespace Elk.Alg.Radial.Intermediate.Optimization

open Elk.Graph

/-- `IEvaluation`: rates the layout below the root of the tree (smaller is better). -/
structure IEvaluation where
  /-- `evaluate(graph)`: the value of the layout of the tree rooted at the given node. -/
  evaluate : NodeId → ElkM Float

end Elk.Alg.Radial.Intermediate.Optimization
