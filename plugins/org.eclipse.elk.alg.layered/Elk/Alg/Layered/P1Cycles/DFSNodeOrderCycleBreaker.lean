import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Alg.Layered.Options.CycleBreakingStrategy
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.p1cycles.DFSNodeOrderCycleBreaker`

Port of elk-rs `p1cycles/dfs_node_order_cycle_breaker.rs` (`DfsNodeOrderCycleBreaker`). Like
`DepthFirstCycleBreaker`, but the outgoing edges of a node are grouped by the (group) model order of
their target and visited in ascending model order (Rust `BTreeMap<i32, Vec<LEdge>>`); the first edge
of a group decides (self loop → skip the group, active target → reverse the whole group, else
recurse). Edges to targets without `MODEL_ORDER` get the key `i32::MAX - <number of groups so far>`.

Node indices are written to `LNode.id` and read back from there (Rust `graph_element().id`). The
phase name is the Rust `type_name` `DfsNodeOrderCycleBreaker`.
-/
namespace Elk.Alg.Layered.P1Cycles

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace DFSNodeOrderCycleBreaker

/-- `INTERMEDIATE_PROCESSING_CONFIGURATION`: `REVERSED_EDGE_RESTORER` after P5. -/
def intermediateProcessingConfiguration : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration).addAfter .p5EdgeRouting .reversedEdgeRestorer

/-- The Rust `model_order_map` of a node (shared with `BFSNodeOrderCycleBreaker`, which duplicates
this loop in Rust): the node's outgoing edges (node-level, port order) grouped by target model
order (`MAX_MODEL_ORDER_NODES * GROUP_MODEL_ORDER_CYCLE_BREAKING_ID + MODEL_ORDER` when the graph's
`GROUP_MODEL_ORDER_CB_GROUP_ORDER_STRATEGY` is `ENFORCED`), groups sorted by ascending key,
edges in insertion order. -/
def modelOrderEdgeGroups (graph : LGraphId) (node : LNodeId) : LayeredM (Array (Array LEdgeId)) := do
  let gr ← getGraph graph
  let enforceGroupModelOrder :=
    gr.props.getD LayeredOptions.GROUP_MODEL_ORDER_CB_GROUP_ORDER_STRATEGY .onlyWithinGroup == .enforced
  let maxModelOrderNodes := gr.internal.maxModelOrderNodes
  let outgoing ← withArena (·.nodeOutgoingEdges node)
  let mut groups : Array (Int × Array LEdgeId) := #[]
  for edge in outgoing do
    let some targetPort := (← getEdge edge).target | continue
    let some targetNode := (← getPort targetPort).owner | continue
    let target ← getNode targetNode
    -- Java reads `MAX_MODEL_ORDER_NODES` (as `int`) for every target with a model order when enforced
    if enforceGroupModelOrder && target.internal.modelOrder.isSome && gr.internal.maxModelOrderNodesNull then
      throw (IO.userError maxModelOrderNodesNullError)
    let key : Int := match target.internal.modelOrder with
      | none => 2147483647 - (groups.size : Int)
      | some modelOrder =>
        if enforceGroupModelOrder then
          maxModelOrderNodes * target.props.getD LayeredOptions.GROUP_MODEL_ORDER_CYCLE_BREAKING_ID 0 + modelOrder
        else modelOrder
    match groups.findIdx? (·.1 == key) with
    | some i => groups := groups.modify i fun (k, es) => (k, es.push edge)
    | none => groups := groups.push (key, #[edge])
  return (stableSort groups fun a b => compare a.1 b.1).map (·.2)

/-- Rust `DfsNodeOrderCycleBreaker` fields. -/
structure State where
  visited : Array Bool := #[]
  active : Array Bool := #[]
  edgesToBeReversed : Array LEdgeId := #[]

/-- Phase-local monad. -/
abbrev DfsM := StateT State LayeredM

/-- `idx as usize < len`. -/
@[inline] private def inRange (i : Int) (size : Nat) : Option Nat :=
  if i >= 0 && i < (size : Int) then some i.toNat else none

/-- `dfs(node)`. -/
partial def dfs (graph : LGraphId) (node : LNodeId) : DfsM Unit := do
  let some index := inRange (← getNode node).id (← get).visited.size | return
  if (← get).visited[index]! then return
  modify fun s => { s with visited := s.visited.set! index true, active := s.active.set! index true }
  let groups ← modelOrderEdgeGroups graph node
  for edges in groups do
    let some representative := edges[0]? | continue
    if ← withArena (·.edgeIsSelfLoop representative) then continue
    let some targetPort := (← getEdge representative).target | continue
    let some targetNode := (← getPort targetPort).owner | continue
    let active := (← get).active
    let targetActive := match inRange (← getNode targetNode).id active.size with
      | some t => active[t]!
      | none => false
    if targetActive then
      modify fun s => { s with edgesToBeReversed := s.edgesToBeReversed ++ edges }
    else
      dfs graph targetNode
  modify fun s => { s with active := s.active.set! index false }

/-- `process(graph, monitor)` body. -/
def run (graph : LGraphId) : DfsM Unit := do
  let nodes := (← getGraph graph).layerlessNodes
  set ({ visited := Array.replicate nodes.size false, active := Array.replicate nodes.size false } : State)
  let mut sources : Array LNodeId := #[]
  let mut index : Nat := 0
  for node in nodes do
    modifyNode node fun n => { n with id := (index : Int) }
    if (← withArena (·.nodeIncomingEdges node)).isEmpty then
      sources := sources.push node
    index := index + 1
  for source in sources do
    dfs graph source
  for node in nodes do
    if let some i := inRange (← getNode node).id (← get).visited.size then
      if !(← get).visited[i]! then
        dfs graph node
  for edge in (← get).edgesToBeReversed do
    LGraphUtil.reverseEdge edge graph true
    modifyGraph graph fun g => { g with internal := { g.internal with cyclic := true } }
  modify fun s => { s with edgesToBeReversed := #[] }

/-- The `DFSNodeOrderCycleBreaker` phase (`CycleBreakingStrategy.DFS_NODE_ORDER`). -/
def phase : LayeredPhase :=
  { name := "DfsNodeOrderCycleBreaker"
    process := fun graph monitor => do
      let _ ← monitor.begin "Depth-first cycle removal" 1.0
      let _ ← (run graph).run {}
      monitor.done
    getLayoutProcessorConfiguration := fun _ => pure (some intermediateProcessingConfiguration) }

end DFSNodeOrderCycleBreaker

builtin_initialize registerDFSNodeOrderCycleBreaker : Unit ←
  LayeredPhases.registerPhase .p1CycleBreaking (ElkEnum.ordinal CycleBreakingStrategy.dfsNodeOrder)
    (pure DFSNodeOrderCycleBreaker.phase)

end Elk.Alg.Layered.P1Cycles
