import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.PortSideProcessor`

Port of elk-rs `intermediate/port_side_processor.rs`. Assigns port sides: nodes whose port
constraints fix the sides only get sides for their `UNDEFINED` ports; all other nodes get sides
for every port and `FIXED_SIDE` port constraints. A port's side is its port dummy's
`EXT_PORT_SIDE` (hierarchical ports), else `EAST` for ports with more outgoing than incoming edges
and `WEST` otherwise.

Iteration order (Rust): the layerless nodes, then the nodes of each layer.

`setPortSide` is public, as in Rust.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace PortSideProcessor

/-- `set_port_side(port)` (Java `setPortSide`). -/
def setPortSide (port : LPortId) : LayeredM Unit := do
  let pt ← getPort port
  let side ← match pt.internal.portDummy with
    | some dummy => pure (← getNode dummy).internal.extPortSide
    | none => pure (if pt.netFlow < 0 then PortSide.east else PortSide.west)
  modifyPort port (·.setSide side)

/-- `process_node(node)` (Java `process(LNode)`). -/
def processNode (node : LNodeId) : LayeredM Unit := do
  let nd ← getNode node
  let constraints := (if nd.props.has LayeredOptions.PORT_CONSTRAINTS then
    nd.props.get LayeredOptions.PORT_CONSTRAINTS else none).getD PortConstraints.undefined
  if constraints.isSideFixed then
    for port in nd.ports do
      if (← getPort port).side == .undefined then setPortSide port
  else
    for port in nd.ports do
      setPortSide port
    setNodeProp node LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedSide

/-- `process(layered_graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Port side processing" 1.0
  for node in (← getGraph graph).layerlessNodes do
    processNode node
  for layer in (← getGraph graph).layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      processNode node
  monitor.done

/-- The `PortSideProcessor` processor. -/
def processor : LayeredProcessor := { name := "PortSideProcessor", process := process }

end PortSideProcessor

builtin_initialize registerPortSideProcessor : Unit ←
  IntermediateProcessorStrategy.register .portSideProcessor PortSideProcessor.processor

end Elk.Alg.Layered.Intermediate
