import Std.Data.HashSet
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.PartitionPreprocessor`

Port of elk-rs `intermediate/partition_preprocessor.rs`. Reverses the outgoing edges of partitioned nodes
(`PARTITIONING_PARTITION` set) that point against the partition order: edges to a node with a lower
partition, and edges to unpartitioned nodes from which a partitioned node with a lower partition than the
source is reachable (breadth-first search over outgoing edges starting at the edge's source node). The
edges are collected first (layerless order, node-level outgoing edges) and then reversed with port
adaptation; each reversed edge gets `PRIORITY_DIRECTION := 1000 + PRIORITY_DIRECTION` (default `0`).

The BFS `visited` list (Rust `Vec` with linear lookup) and the lower-partition list membership tests are
`Std.HashSet` lookups; the queue order is the Rust order.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Options Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace PartitionPreprocessor

/-- `PARTITION_CONSTRAINT_EDGE_PRIORITY`. -/
def PARTITION_CONSTRAINT_EDGE_PRIORITY : Int := 1000

/-- Rust `node_partition`: the node's `PARTITIONING_PARTITION` (no default). -/
def nodePartition (node : LNodeId) : LayeredM (Option Int) := do
  return (← getNode node).props.get CoreOptions.PARTITIONING_PARTITION

/-- Owner node of an optional port. -/
def portOwner (port : Option LPortId) : LayeredM (Option LNodeId) := do
  let some p := port | return none
  return (← getPort p).owner

/-- Breadth-first search from `start` over outgoing edges: whether a node of `targets` is reachable
(including `start` itself). -/
def reachesAny (start : LNodeId) (targets : Std.HashSet LNodeId) : LayeredM Bool := do
  let mut queue : Array LNodeId := #[start]
  let mut visited : Std.HashSet LNodeId := ({} : Std.HashSet LNodeId).insert start
  let mut head := 0
  while head < queue.size do
    let current := queue[head]!
    head := head + 1
    if targets.contains current then return true
    for outgoing in (← withArena (·.nodeOutgoingEdges current)) do
      let some target ← portOwner (← getEdge outgoing).target | continue
      if visited.contains target then continue
      visited := visited.insert target
      queue := queue.push target
  return false

/-- `mustBeReversed(edge, partitionedNodes)`. -/
def mustBeReversed (edge : LEdgeId) (sourcePartition : Int) (partitionedNodes : Array LNodeId) :
    LayeredM Bool := do
  let ed ← getEdge edge
  let some targetNode ← portOwner ed.target | return false
  if let some targetPartition ← nodePartition targetNode then
    return sourcePartition > targetPartition
  let mut lowerPartitionNodes : Std.HashSet LNodeId := {}
  for node in partitionedNodes do
    if let some partition ← nodePartition node then
      if partition < sourcePartition then lowerPartitionNodes := lowerPartitionNodes.insert node
  if lowerPartitionNodes.isEmpty then return false
  let some sourceNode ← portOwner ed.source | return false
  reachesAny sourceNode lowerPartitionNodes

/-- Rust `reverse_edge`: reverses with port adaptation in the source node's graph (skipped when the
source has no graph) and raises `PRIORITY_DIRECTION` by `PARTITION_CONSTRAINT_EDGE_PRIORITY`. -/
def reverseEdge (edge : LEdgeId) : LayeredM Unit := do
  let some sourceNode ← portOwner (← getEdge edge).source | return
  let some graph ← nodeGraph sourceNode | return
  LGraphUtil.reverseEdge edge graph true
  modifyEdge edge fun e =>
    let priority := PARTITION_CONSTRAINT_EDGE_PRIORITY + (e.props.get LayeredOptions.PRIORITY_DIRECTION).getD 0
    { e with props := e.props.set LayeredOptions.PRIORITY_DIRECTION priority }

/-- `process(lGraph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let mut partitionedNodes : Array LNodeId := #[]
  for node in (← getGraph graph).layerlessNodes do
    if (← nodePartition node).isSome then partitionedNodes := partitionedNodes.push node
  let mut edgesToReverse : Array LEdgeId := #[]
  for node in partitionedNodes do
    let some sourcePartition ← nodePartition node | continue
    for edge in (← withArena (·.nodeOutgoingEdges node)) do
      if ← mustBeReversed edge sourcePartition partitionedNodes then
        edgesToReverse := edgesToReverse.push edge
  for edge in edgesToReverse do
    reverseEdge edge

/-- The `PartitionPreprocessor` processor. -/
def processor : LayeredProcessor :=
  { name := "PartitionPreprocessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Partition preprocessing" 1.0
      run graph
      monitor.done }

end PartitionPreprocessor

builtin_initialize registerPartitionPreprocessor : Unit ←
  IntermediateProcessorStrategy.register .partitionPreprocessor PartitionPreprocessor.processor

end Elk.Alg.Layered.Intermediate
