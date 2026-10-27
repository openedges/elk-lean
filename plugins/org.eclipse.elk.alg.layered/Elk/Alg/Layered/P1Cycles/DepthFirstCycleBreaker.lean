import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Alg.Layered.Options.CycleBreakingStrategy
/-!
# `org.eclipse.elk.alg.layered.p1cycles.DepthFirstCycleBreaker`

Port of elk-rs `p1cycles/depth_first_cycle_breaker.rs`. A DFS starting at the source nodes (no
incoming edges), then at every still unvisited node in layerless order, collects the back edges
(edges to an active node; self loops skipped) and reverses them with port adaptation.

Node indices are written to `LNode.id` (Rust `graph_element().id`) and read back from there. The
Rust struct fields (`visited`, `active`, `edges_to_reverse`) are the phase-local `State`.
-/
namespace Elk.Alg.Layered.P1Cycles

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace DepthFirstCycleBreaker

/-- `INTERMEDIATE_PROCESSING_CONFIGURATION`: `REVERSED_EDGE_RESTORER` after P5. -/
def intermediateProcessingConfiguration : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration).addAfter .p5EdgeRouting .reversedEdgeRestorer

/-- Rust `DepthFirstCycleBreaker` fields. -/
structure State where
  visited : Array Bool := #[]
  active : Array Bool := #[]
  edgesToReverse : Array LEdgeId := #[]

/-- Phase-local monad. -/
abbrev DfsM := StateT State LayeredM

/-- `idx as usize < len`. -/
@[inline] private def inRange (i : Int) (size : Nat) : Option Nat :=
  if i >= 0 && i < (size : Int) then some i.toNat else none

/-- `dfs(node)`: visits the node's outgoing edges (node-level, port order). -/
partial def dfs (node : LNodeId) : DfsM Unit := do
  let some index := inRange (← getNode node).id (← get).visited.size | return
  if (← get).visited[index]! then return
  modify fun s => { s with visited := s.visited.set! index true, active := s.active.set! index true }
  let outgoing ← withArena (·.nodeOutgoingEdges node)
  for edge in outgoing do
    if ← withArena (·.edgeIsSelfLoop edge) then continue
    let some targetPort := (← getEdge edge).target | continue
    let some targetNode := (← getPort targetPort).owner | continue
    let active := (← get).active
    let targetActive := match inRange (← getNode targetNode).id active.size with
      | some t => active[t]!
      | none => false
    if targetActive then
      modify fun s => { s with edgesToReverse := s.edgesToReverse.push edge }
    else
      dfs targetNode
  modify fun s => { s with active := s.active.set! index false }

/-- `process(graph, monitor)` body. -/
def run (graph : LGraphId) : DfsM Unit := do
  let nodes := (← getGraph graph).layerlessNodes
  let nodeCount := nodes.size
  set ({ visited := Array.replicate nodeCount false, active := Array.replicate nodeCount false } : State)
  let mut sources : Array LNodeId := #[]
  let mut index : Nat := 0
  for node in nodes do
    modifyNode node fun n => { n with id := (index : Int) }
    if (← withArena (·.nodeIncomingEdges node)).isEmpty then
      sources := sources.push node
    index := index + 1
  for source in sources do
    dfs source
  for node in nodes do
    if let some i := inRange (← getNode node).id nodeCount then
      if !(← get).visited[i]! then
        dfs node
  for edge in (← get).edgesToReverse do
    LGraphUtil.reverseEdge edge graph true
    modifyGraph graph fun g => { g with internal := { g.internal with cyclic := true } }
  modify fun s => { s with edgesToReverse := #[] }

/-- The `DepthFirstCycleBreaker` phase. -/
def phase : LayeredPhase :=
  { name := "DepthFirstCycleBreaker"
    process := fun graph monitor => do
      let _ ← monitor.begin "Depth-first cycle removal" 1.0
      let _ ← (run graph).run {}
      monitor.done
    getLayoutProcessorConfiguration := fun _ => pure (some intermediateProcessingConfiguration) }

end DepthFirstCycleBreaker

builtin_initialize registerDepthFirstCycleBreaker : Unit ←
  LayeredPhases.registerPhase .p1CycleBreaking (ElkEnum.ordinal CycleBreakingStrategy.depthFirst)
    (pure DepthFirstCycleBreaker.phase)

end Elk.Alg.Layered.P1Cycles
