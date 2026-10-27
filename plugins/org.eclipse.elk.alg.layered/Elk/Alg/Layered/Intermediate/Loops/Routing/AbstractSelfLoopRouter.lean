import Elk.Alg.Layered.Intermediate.Loops.Ops
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.routing.AbstractSelfLoopRouter`

Java's abstract base class of the self-loop routers (`routeSelfLoops(slHolder)`). elk-rs has no
router classes: `intermediate/self_loop_router.rs` routes every loop orthogonally (`route_node`) and
then matches on `EdgeRouting` in `modify_bend_points` (polyline corner cutting, spline control
points, or the orthogonal points unchanged).

The Lean port keeps the Java class structure as a structure of closures: a router is its Java
simple class name plus `routeSelfLoops`, and the edge-routing specific part of the Rust
`modify_bend_points` is the `BendPointModifier` hook (Java `OrthogonalSelfLoopRouter.modifyBendPoints`,
overridden by `PolylineSelfLoopRouter` and `SplineSelfLoopRouter`). `SelfLoopRouter.routerFor` picks
the router by `EdgeRouting` (Java `routerForGraph`, Rust `modify_bend_points`' match).
-/
namespace Elk.Alg.Layered.Intermediate.Loops.Routing

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Alg.Layered.Graph

/-- The spacings the self-loop router reads from the graph (elk-rs `SelfLoopRouter::process`:
`SPACING_EDGE_EDGE` (10), `SPACING_EDGE_LABEL` (2), `SPACING_NODE_SELF_LOOP` (10)).

Rust/Java difference (Rust followed): Java reads them per node with
`LGraphUtil.getIndividualOrInherited`; Rust reads them once from the graph. -/
structure SelfLoopRoutingSpacings where
  /-- `edge_edge_distance`. -/
  edgeEdge : Float := 10.0
  /-- `edge_label_distance`. -/
  edgeLabel : Float := 2.0
  /-- `node_self_loop_distance`. -/
  nodeSelfLoop : Float := 10.0
  deriving Inhabited, Repr

/-- The arguments of the Rust `modify_bend_points` (Java `modifyBendPoints(slEdge, routingDirection,
bendPoints)`): the local anchors of the edge's source and target port (`local_port_anchor`), the
orthogonal bend points, the source side, the routing direction and the edge-label spacing. -/
structure BendPointModification where
  /-- `local_port_anchor(source_port)`: port position plus anchor. -/
  sourceAnchor : KVector
  /-- `local_port_anchor(target_port)`. -/
  targetAnchor : KVector
  /-- The orthogonal bend points (`compute_orthogonal_bend_points`). -/
  bendPoints : Array KVector
  /-- `source_side` (the routing side of the source port). -/
  sourceSide : PortSide
  /-- `clockwise` (`compute_edge_routing_direction`). -/
  clockwise : Bool
  /-- `edge_label_distance`. -/
  edgeLabelDistance : Float
  deriving Inhabited

/-- `modifyBendPoints` hook: turns the orthogonal bend points into the router's style. `Except`
carries the Rust `assert!` failures (thrown as `IllegalStateException` by the caller). -/
abbrev BendPointModifier := BendPointModification → Except String (Array KVector)

/-- `AbstractSelfLoopRouter`. -/
structure AbstractSelfLoopRouter where
  /-- Java simple class name of the router. -/
  name : String
  /-- `routeSelfLoops(slHolder)`: routes the loops of the holder stored on the node. -/
  routeSelfLoops : LNodeId → SelfLoopRoutingSpacings → LayeredM Unit

instance : Inhabited AbstractSelfLoopRouter := ⟨{ name := "", routeSelfLoops := fun _ _ => pure () }⟩

end Elk.Alg.Layered.Intermediate.Loops.Routing
