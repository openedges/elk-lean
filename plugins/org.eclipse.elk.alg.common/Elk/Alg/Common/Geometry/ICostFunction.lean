import Elk.Alg.Common.Geometry.TEdge
/-!
# `org.eclipse.elk.alg.common.ICostFunction`

Interface for a cost function used in the processing order phase
(elk-rs `i_cost_function.rs`, a trait with a blanket impl over `Fn(&TEdge) -> f64`).
-/
namespace Elk.Alg.Common

/-- `ICostFunction.cost(TEdge)`: the cost associated with an edge created in the
structure phase. -/
abbrev ICostFunction := TEdge → Float

end Elk.Alg.Common
