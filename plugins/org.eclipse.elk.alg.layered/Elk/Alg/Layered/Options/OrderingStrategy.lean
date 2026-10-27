import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.OrderingStrategy`

Port of `options/ordering_strategy.rs` (elk-rs) and `OrderingStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.OrderingStrategy`: Strategy to order nodes and ports before
crossing minimization. -/
elk_enum OrderingStrategy := none nodesAndEdges preferEdges preferNodes

end Elk.Alg.Layered.Options
