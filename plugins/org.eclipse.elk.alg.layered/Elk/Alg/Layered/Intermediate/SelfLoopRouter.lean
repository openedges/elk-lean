import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.Intermediate.Loops.Routing
/-!
# `org.eclipse.elk.alg.layered.intermediate.SelfLoopRouter`

Port of elk-rs `intermediate/self_loop_router.rs` (`SelfLoopRouter::process`): computes the bend
points of all self loops and places their labels. For every normal node with a `SelfLoopHolder`
(nodes of all layers, in order):
1. `RoutingDirector.determineLoopRoutes` (port ids, leftmost/rightmost ports, occupied sides);
2. `LabelPlacer.prepareLabels` (label sides and alignments; Rust comment: "Java parity:
   side/alignment + label management must happen before slot assignment");
3. `RoutingSlotAssigner.assignRoutingSlots` with the graph's random generator;
4. the router for the graph's `EDGE_ROUTING` (`routerFor`; Rust `route_node` + `modify_bend_points`).

Graph options (Rust `get_property(…).unwrap_or(…)`): `EDGE_ROUTING` (`ORTHOGONAL`), `SPACING_EDGE_EDGE`
(10), `SPACING_EDGE_LABEL` (2), `SPACING_NODE_SELF_LOOP` (10).

Random numbers: Rust clones the graph's `RANDOM` (an `Arc`-shared state, so the draws advance the
graph's generator) or uses a fresh `Random::default()` (seed 0, not stored) when it is missing; the
port threads one generator through all nodes and writes it back at the end only in the first case
(as `OrthogonalRoutingGenerator.routeEdges`).

TODO(core-labels): `LABEL_MANAGER` is not read (no label manager in Lean; see `LabelPlacer`).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Options Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate.Loops Elk.Alg.Layered.Intermediate.Loops.Routing LayeredM

namespace SelfLoopRouter

/-- Java `routerForGraph(graph)` / the Rust `modify_bend_points` match: `POLYLINE` → polyline,
`SPLINES` → spline, anything else → orthogonal. -/
def routerFor : EdgeRouting → AbstractSelfLoopRouter
  | .polyline => PolylineSelfLoopRouter.router
  | .splines => SplineSelfLoopRouter.router
  | _ => OrthogonalSelfLoopRouter.router

/-- `process_node(holder, …)` (Java `processNode`): director, label preparation, slot assignment,
routing. Returns the advanced random generator. -/
def processNode (n : LNodeId) (router : AbstractSelfLoopRouter) (spacings : SelfLoopRoutingSpacings)
    (random : Random) : LayeredM Random := do
  RoutingDirector.determineLoopRoutes n
  LabelPlacer.prepareLabels n
  let random ← RoutingSlotAssigner.assignRoutingSlotsOf n random
  router.routeSelfLoops n spacings
  return random

/-- `process(graph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let edgeRouting := (gr.props.get LayeredOptions.EDGE_ROUTING).getD .orthogonal
  let graphRandom ← LayeredM.graphRandom? graph
  let spacings : SelfLoopRoutingSpacings :=
    { edgeEdge := (gr.props.get LayeredOptions.SPACING_EDGE_EDGE).getD 10.0
      edgeLabel := (gr.props.get LayeredOptions.SPACING_EDGE_LABEL).getD 2.0
      nodeSelfLoop := (gr.props.get LayeredOptions.SPACING_NODE_SELF_LOOP).getD 10.0 }
  let router := routerFor edgeRouting
  let mut nodes : Array LNodeId := #[]
  for layer in gr.layers do
    nodes := nodes ++ (← getLayer layer).nodes
  let mut random := graphRandom.getD (Random.ofInt 0)
  for n in nodes do
    let nd ← getNode n
    if nd.type != .normal || nd.internal.selfLoopHolder.isNone then continue
    random ← processNode n router spacings random
  if graphRandom.isSome then
    LayeredM.setGraphRandom graph random

/-- The `SelfLoopRouter` intermediate processor. -/
def processor : LayeredProcessor :=
  { name := "SelfLoopRouter"
    process := fun graph monitor => do
      let _ ← monitor.begin "Self-Loop routing" 1.0
      run graph
      monitor.done }

end SelfLoopRouter

builtin_initialize registerSelfLoopRouter : Unit ←
  IntermediateProcessorStrategy.register .selfLoopRouter SelfLoopRouter.processor

end Elk.Alg.Layered.Intermediate
