import Elk.Graph
import Elk.Alg.Radial.InternalProperties
/-!
# `org.eclipse.elk.alg.radial.p2routing.IRadialEdgeRouter`

Port of `i_radial_edge_router.rs` (elk-rs).
-/
namespace Elk.Alg.Radial.P2Routing

open Elk.Graph

/-- `IRadialEdgeRouter`. -/
structure IRadialEdgeRouter where
  /-- `route_edges(node)`: routes the edges of the subtree below `node`. -/
  routeEdges : NodeId → ElkM Unit

end Elk.Alg.Radial.P2Routing
