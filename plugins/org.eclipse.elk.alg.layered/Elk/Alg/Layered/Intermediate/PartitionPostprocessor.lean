import Elk.Alg.Layered.Intermediate.PartitionMidprocessor
/-!
# `org.eclipse.elk.alg.layered.intermediate.PartitionPostprocessor`

Port of elk-rs `intermediate/partition_postprocessor.rs`. After layering, the dummy ports created by
`PartitionMidprocessor` (flag `PARTITION_DUMMY`, see `PartitionMidprocessor.PORT_PARTITION_DUMMY`) are
removed: each connected edge (incoming, then outgoing) is detached from the port and the port from its
node. Nodes are visited in layer order; layerless nodes are not visited.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace PartitionPostprocessor

/-- Rust `detach_partition_port(port)`. -/
def detachPartitionPort (port : LPortId) : LayeredM Unit := do
  for edge in (← getPort port).connectedEdges do
    if (← getEdge edge).source == some port then setEdgeSource edge none
    if (← getEdge edge).target == some port then setEdgeTarget edge none
  setPortNode port none

/-- `process(lGraph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  for layer in (← getGraph graph).layers do
    for node in (← getLayer layer).nodes do
      let mut partitionPorts : Array LPortId := #[]
      for port in (← getNode node).ports do
        if ← PartitionMidprocessor.isPortPartitionDummy port then partitionPorts := partitionPorts.push port
      for port in partitionPorts do
        detachPartitionPort port

/-- The `PartitionPostprocessor` processor. -/
def processor : LayeredProcessor :=
  { name := "PartitionPostprocessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Partition postprocessing" 1.0
      run graph
      monitor.done }

end PartitionPostprocessor

builtin_initialize registerPartitionPostprocessor : Unit ←
  IntermediateProcessorStrategy.register .partitionPostprocessor PartitionPostprocessor.processor

end Elk.Alg.Layered.Intermediate
