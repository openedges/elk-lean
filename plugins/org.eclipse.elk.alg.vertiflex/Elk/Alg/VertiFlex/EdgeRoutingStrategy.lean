import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.vertiflex.EdgeRoutingStrategy`

Port of `edge_routing_strategy.rs` (elk-rs): the value of the `layoutStrategy` option, i.e.
whether edges are drawn as straight lines or with a possible bend.
-/
namespace Elk.Alg.VertiFlex

/-- `EdgeRoutingStrategy`: `STRAIGHT` (default) or `BEND`. -/
elk_enum EdgeRoutingStrategy := straight bend

end Elk.Alg.VertiFlex
