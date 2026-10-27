import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.intermediate.PartitionMidprocessor`

Port of elk-rs `intermediate/partition_midprocessor.rs`. Before layering, every node of a partition is
connected to every node of the next (non-empty, ascending) partition by a dummy edge (Rust `BTreeMap`
partition order; nodes in layerless order): one new `EAST` source port per node of the first partition
and, per pair, a new `WEST` target port on the node of the second partition and a new edge. Ports and edges
are flagged `PARTITION_DUMMY` and removed again by `PartitionPostprocessor`.

The flag on the dummy **ports** is kept in the port's `props` (`PORT_PARTITION_DUMMY`, same id as
`InternalProperties.PARTITION_DUMMY`) because `LPortInternals` has no `partitionDummy` field yet (TODO:
move it to a typed field; the edge flag already is `LEdgeInternals.partitionDummy`).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Options Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace PartitionMidprocessor

/-- `InternalProperties.PARTITION_DUMMY` (`partitionDummy`, default `false`) as set on dummy ports.
Temporary stand-in for a typed `LPortInternals.partitionDummy` field (see the module doc). -/
def PORT_PARTITION_DUMMY : Property Bool := Property.withDefault "partitionDummy" false

/-- Marks a port as a partition dummy port (`port.setProperty(PARTITION_DUMMY, true)`). -/
def setPortPartitionDummy (port : LPortId) : LayeredM Unit :=
  setPortProp port PORT_PARTITION_DUMMY true

/-- `port.getProperty(PARTITION_DUMMY)` on a port value. -/
def portIsPartitionDummy (port : LPort) : Bool := port.props.getD PORT_PARTITION_DUMMY false

/-- `port.getProperty(PARTITION_DUMMY)`. -/
def isPortPartitionDummy (port : LPortId) : LayeredM Bool := do
  return portIsPartitionDummy (← getPort port)

/-- `connectPartitions(firstPartition, secondPartition)`. -/
def connectPartitions (firstPartition secondPartition : Array LNodeId) : LayeredM Unit := do
  for node in firstPartition do
    let sourcePort ← createPort
    modifyPort sourcePort fun p => p.setSide .east
    setPortPartitionDummy sourcePort
    setPortNode sourcePort (some node)
    for otherNode in secondPartition do
      let targetPort ← createPort
      modifyPort targetPort fun p => p.setSide .west
      setPortPartitionDummy targetPort
      setPortNode targetPort (some otherNode)
      let edge ← createEdge
      modifyEdge edge fun e => { e with internal := { e.internal with partitionDummy := true } }
      setEdgeSource edge (some sourcePort)
      setEdgeTarget edge (some targetPort)

/-- The partitions of the layerless nodes in ascending partition order (Rust `BTreeMap`), each with its
nodes in layerless order. -/
def collectPartitions (graph : LGraphId) : LayeredM (Array (Int × Array LNodeId)) := do
  let mut partitions : Array (Int × Array LNodeId) := #[]
  for node in (← getGraph graph).layerlessNodes do
    let some partition := (← getNode node).props.get CoreOptions.PARTITIONING_PARTITION | continue
    match partitions.findIdx? (·.1 == partition) with
    | some i => partitions := partitions.modify i fun (k, ns) => (k, ns.push node)
    | none => partitions := partitions.push (partition, #[node])
  return stableSort partitions fun a b => compare a.1 b.1

/-- `process(lGraph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let partitions ← collectPartitions graph
  for i in [1:partitions.size] do
    connectPartitions partitions[i - 1]!.2 partitions[i]!.2

/-- The `PartitionMidprocessor` processor. -/
def processor : LayeredProcessor :=
  { name := "PartitionMidprocessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Partition midprocessing" 1.0
      run graph
      monitor.done }

end PartitionMidprocessor

builtin_initialize registerPartitionMidprocessor : Unit ←
  IntermediateProcessorStrategy.register .partitionMidprocessor PartitionMidprocessor.processor

end Elk.Alg.Layered.Intermediate
