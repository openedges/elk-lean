import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Alg.Layered.Options.CycleBreakingStrategy
/-!
# `org.eclipse.elk.alg.layered.p1cycles.InteractiveCycleBreaker`

Port of elk-rs `p1cycles/interactive_cycle_breaker.rs`. Phase 1 reverses every edge whose target
reference x coordinate (`INTERACTIVE_REFERENCE_POINT`: centre or top-left) is left of its source's;
phase 2 runs a DFS (node ids as marks: `1` unvisited, `-1` on the stack, `0` finished) to reverse
the remaining back edges (nodes with equal x coordinates). Both phases reverse with port adaptation.

Like Rust, the DFS is iterative: each stack entry caches the node's outgoing (non-self-loop) edges
with their target nodes when it is pushed. Like Rust (and Java), the graph's `CYCLIC` flag is not set.
-/
namespace Elk.Alg.Layered.P1Cycles

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace InteractiveCycleBreaker

/-- `INTERMEDIATE_PROCESSING_CONFIGURATION`: `INTERACTIVE_EXTERNAL_PORT_POSITIONER` before P1,
`REVERSED_EDGE_RESTORER` after P5. -/
def intermediateProcessingConfiguration : LayeredProcessorConfiguration :=
  ((LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p1CycleBreaking .interactiveExternalPortPositioner)
    |>.addAfter .p5EdgeRouting .reversedEdgeRestorer

/-- Rust `reference_x`: the x coordinate of the node's reference point. -/
def referenceX (node : LNodeId) (reference : InteractiveReferencePoint) : LayeredM Float := do
  let nd ← getNode node
  return match reference with
    | .center => nd.position.x + nd.size.x / 2.0
    | .topLeft => nd.position.x

/-- Rust `get_outgoing`: the node's outgoing edges (node-level, port order) with their target
nodes, self loops and dangling edges skipped. -/
def getOutgoing (node : LNodeId) : LayeredM (Array (LEdgeId × LNodeId)) := do
  let mut result := #[]
  for edge in (← withArena (·.nodeOutgoingEdges node)) do
    let some targetPort := (← getEdge edge).target | continue
    let some target := (← getPort targetPort).owner | continue
    if target == node then continue
    result := result.push (edge, target)
  return result

/-- `findCycles(node1, revEdges)` (Rust `find_cycles`, iterative). -/
def findCycles (start : LNodeId) (revEdges : Array LEdgeId) : LayeredM (Array LEdgeId) := do
  let mut revEdges := revEdges
  let startEdges ← getOutgoing start
  modifyNode start fun n => { n with id := -1 }
  let mut stack : Array (LNodeId × Array (LEdgeId × LNodeId) × Nat) := #[(start, startEdges, 0)]
  while true do
    let some (node, edges, idx) := stack.back? | break
    if idx >= edges.size then
      modifyNode node fun n => { n with id := 0 }
      stack := stack.pop
      continue
    stack := stack.modify (stack.size - 1) fun (n, es, i) => (n, es, i + 1)
    let (edge, target) := edges[idx]!
    let targetId := (← getNode target).id
    if targetId < 0 then
      revEdges := revEdges.push edge
    else if targetId > 0 then
      let targetEdges ← getOutgoing target
      modifyNode target fun n => { n with id := -1 }
      stack := stack.push (target, targetEdges, 0)
  return revEdges

/-- `process(layeredGraph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let nodes := (← getGraph graph).layerlessNodes
  let referencePoint := (← getGraph graph).props.getD LayeredOptions.INTERACTIVE_REFERENCE_POINT .center
  let mut revEdges : Array LEdgeId := #[]
  for node in nodes do
    modifyNode node fun n => { n with id := 1 }
  for source in nodes do
    let sourceX ← referenceX source referencePoint
    for edge in (← withArena (·.nodeOutgoingEdges source)) do
      let some targetPort := (← getEdge edge).target | continue
      let some target := (← getPort targetPort).owner | continue
      if source == target then continue
      let targetX ← referenceX target referencePoint
      if targetX < sourceX then
        revEdges := revEdges.push edge
  for edge in revEdges do
    LGraphUtil.reverseEdge edge graph true
  -- phase 2: DFS for the remaining cycles
  revEdges := #[]
  for node in nodes do
    modifyNode node fun n => { n with id := 1 }
  for node in nodes do
    if (← getNode node).id > 0 then
      revEdges ← findCycles node revEdges
  for edge in revEdges do
    LGraphUtil.reverseEdge edge graph true

/-- The `InteractiveCycleBreaker` phase. -/
def phase : LayeredPhase :=
  { name := "InteractiveCycleBreaker"
    process := fun graph monitor => do
      let _ ← monitor.begin "Interactive cycle breaking" 1.0
      run graph
      monitor.done
    getLayoutProcessorConfiguration := fun _ => pure (some intermediateProcessingConfiguration) }

end InteractiveCycleBreaker

builtin_initialize registerInteractiveCycleBreaker : Unit ←
  LayeredPhases.registerPhase .p1CycleBreaking (ElkEnum.ordinal CycleBreakingStrategy.interactive)
    (pure InteractiveCycleBreaker.phase)

end Elk.Alg.Layered.P1Cycles
