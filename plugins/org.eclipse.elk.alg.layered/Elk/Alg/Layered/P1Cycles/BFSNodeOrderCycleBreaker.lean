import Std.Data.HashSet
import Elk.Alg.Layered.P1Cycles.DFSNodeOrderCycleBreaker
/-!
# `org.eclipse.elk.alg.layered.p1cycles.BFSNodeOrderCycleBreaker`

Port of elk-rs `p1cycles/bfs_node_order_cycle_breaker.rs` (`BfsNodeOrderCycleBreaker`). A BFS from
each source node (in layerless order; then from the first unvisited node until all are visited)
visits the outgoing edge groups of a node in ascending target model order (see
`DFSNodeOrderCycleBreaker.modelOrderEdgeGroups`). A group whose target is already visited is
reversed unless the current node is a source or the target is a sink; otherwise the target is queued.

The Rust `BTreeSet<NodeRefKey>` source/sink sets are only used for membership tests (`Std.HashSet`).
Node indices are written to `LNode.id` and read back from there. The phase name is the Rust
`type_name` `BfsNodeOrderCycleBreaker`.
-/
namespace Elk.Alg.Layered.P1Cycles

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace BFSNodeOrderCycleBreaker

/-- `INTERMEDIATE_PROCESSING_CONFIGURATION`: `REVERSED_EDGE_RESTORER` after P5. -/
def intermediateProcessingConfiguration : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration).addAfter .p5EdgeRouting .reversedEdgeRestorer

/-- Rust `BfsNodeOrderCycleBreaker` fields. `bfsQueue` (`VecDeque`) pends `bfsQueue[queueHead:]`. -/
structure State where
  sources : Std.HashSet LNodeId := {}
  sinks : Std.HashSet LNodeId := {}
  visited : Array Bool := #[]
  bfsQueue : Array LNodeId := #[]
  queueHead : Nat := 0
  edgesToBeReversed : Array LEdgeId := #[]

/-- Phase-local monad. -/
abbrev BfsM := StateT State LayeredM

/-- `idx as usize < len`. -/
@[inline] private def inRange (i : Int) (size : Nat) : Option Nat :=
  if i >= 0 && i < (size : Int) then some i.toNat else none

private def enqueue (node : LNodeId) : BfsM Unit :=
  modify fun s => { s with bfsQueue := s.bfsQueue.push node }

/-- `bfs(node)`. -/
def bfs (graph : LGraphId) (node : LNodeId) : BfsM Unit := do
  let some index := inRange (← getNode node).id (← get).visited.size | return
  if (← get).visited[index]! then return
  modify fun s => { s with visited := s.visited.set! index true }
  let groups ← DFSNodeOrderCycleBreaker.modelOrderEdgeGroups graph node
  for edges in groups do
    let some representative := edges[0]? | continue
    if ← withArena (·.edgeIsSelfLoop representative) then continue
    let some targetPort := (← getEdge representative).target | continue
    let some targetNode := (← getPort targetPort).owner | continue
    let s ← get
    let targetVisited := match inRange (← getNode targetNode).id s.visited.size with
      | some t => s.visited[t]!
      | none => false
    let nodeIsSource := s.sources.contains node
    let targetIsSink := s.sinks.contains targetNode
    if targetVisited && !nodeIsSource && !targetIsSink then
      modify fun s => { s with edgesToBeReversed := s.edgesToBeReversed ++ edges }
    else
      enqueue targetNode

/-- `bfsLoop()`: pops the queue until it is empty. -/
def bfsLoop (graph : LGraphId) : BfsM Unit := do
  while true do
    let s ← get
    let some node := s.bfsQueue[s.queueHead]? | break
    set { s with queueHead := s.queueHead + 1 }
    bfs graph node

/-- `process(graph, monitor)` body. -/
def run (graph : LGraphId) : BfsM Unit := do
  let nodes := (← getGraph graph).layerlessNodes
  set ({ visited := Array.replicate nodes.size false } : State)
  let mut sourcesInOrder : Array LNodeId := #[]
  let mut index : Nat := 0
  for node in nodes do
    modifyNode node fun n => { n with id := (index : Int) }
    let isSource := (← withArena (·.nodeIncomingEdges node)).isEmpty
    let isSink := (← withArena (·.nodeOutgoingEdges node)).isEmpty
    if isSource then
      modify fun s => { s with sources := s.sources.insert node }
      sourcesInOrder := sourcesInOrder.push node
    if isSink then
      modify fun s => { s with sinks := s.sinks.insert node }
    index := index + 1
  for source in sourcesInOrder do
    enqueue source
    bfsLoop graph
  bfsLoop graph
  let mut changed := true
  while changed do
    changed := false
    let visited := (← get).visited
    for i in [0:visited.size] do
      if !visited[i]! then
        enqueue nodes[i]!
        changed := true
        break
    bfsLoop graph
  for edge in (← get).edgesToBeReversed do
    LGraphUtil.reverseEdge edge graph true
    modifyGraph graph fun g => { g with internal := { g.internal with cyclic := true } }
  modify fun s => { s with edgesToBeReversed := #[] }

/-- The `BFSNodeOrderCycleBreaker` phase (`CycleBreakingStrategy.BFS_NODE_ORDER`). -/
def phase : LayeredPhase :=
  { name := "BfsNodeOrderCycleBreaker"
    process := fun graph monitor => do
      let _ ← monitor.begin "Breadth-first cycle removal" 1.0
      let _ ← (run graph).run {}
      monitor.done
    getLayoutProcessorConfiguration := fun _ => pure (some intermediateProcessingConfiguration) }

end BFSNodeOrderCycleBreaker

builtin_initialize registerBFSNodeOrderCycleBreaker : Unit ←
  LayeredPhases.registerPhase .p1CycleBreaking (ElkEnum.ordinal CycleBreakingStrategy.bfsNodeOrder)
    (pure BFSNodeOrderCycleBreaker.phase)

end Elk.Alg.Layered.P1Cycles
