import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.mrtree.options.EdgeRoutingMode`

Port of `options/edge_routing_mode.rs` (elk-rs) and `EdgeRoutingMode.java` (same constants, same ordinal order).
-/
namespace Elk.Alg.MrTree.Options

/-- `org.eclipse.elk.alg.mrtree.options.EdgeRoutingMode`: the edge routing algorithm of `P4_EDGE_ROUTING`. -/
elk_enum EdgeRoutingMode := none middleToMiddle avoidOverlap

end Elk.Alg.MrTree.Options
