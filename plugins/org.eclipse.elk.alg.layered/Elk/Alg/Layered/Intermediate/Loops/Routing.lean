import Elk.Alg.Layered.Intermediate.Loops.Routing.AbstractSelfLoopRouter
import Elk.Alg.Layered.Intermediate.Loops.Routing.RoutingDirector
import Elk.Alg.Layered.Intermediate.Loops.Routing.RoutingSlotAssigner
import Elk.Alg.Layered.Intermediate.Loops.Routing.LabelPlacer
import Elk.Alg.Layered.Intermediate.Loops.Routing.OrthogonalSelfLoopRouter
import Elk.Alg.Layered.Intermediate.Loops.Routing.PolylineSelfLoopRouter
import Elk.Alg.Layered.Intermediate.Loops.Routing.SplineSelfLoopRouter
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.routing`

Aggregator of the self-loop routing package (elk-rs `intermediate/loops/routing/mod.rs`:
`label_placer`, `polyline_self_loop_router`, `routing_director`, `routing_slot_assigner`). The Java
router classes (`AbstractSelfLoopRouter`, `OrthogonalSelfLoopRouter`, `SplineSelfLoopRouter`) hold
the routing code elk-rs keeps in `intermediate/self_loop_router.rs` (`route_node`,
`modify_bend_points`).
-/
