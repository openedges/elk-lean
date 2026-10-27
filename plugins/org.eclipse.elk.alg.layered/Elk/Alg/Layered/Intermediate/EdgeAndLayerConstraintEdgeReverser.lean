import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.EdgeAndLayerConstraintEdgeReverser`

Port of elk-rs `intermediate/edge_and_layer_constraint_edge_reverser.rs`. Before layering, the edges of
nodes with a `FIRST`/`FIRST_SEPARATE` layer constraint are turned into outgoing edges and those of
`LAST`/`LAST_SEPARATE` nodes into incoming edges (`LEdge.reverse(graph, true)`). Remaining nodes with
fixed port sides whose ports all look reversed (eastern ports with positive net flow, western ports with
negative net flow) get all their edges reversed ("feedback node").

Rust/Java parity notes:
- Like Java (and elk-rs), `EDGE_CONSTRAINT` is set to `OUTGOING_ONLY` for every constrained node, even for
  `LAST`/`LAST_SEPARATE` ones (whose computed edge constraint is `INCOMING_ONLY`).
- `handleInnerNodes` re-reads the layer constraint of the remaining nodes (always `NONE` there) and stops
  the port scan at the first violation (Java only breaks the inner edge loop; the result is the same).
- The reversal graph is the node's graph (`LNode.getGraph()`), falling back to the processed graph
  (Rust: `unwrap_or_default`).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Options Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace EdgeAndLayerConstraintEdgeReverser

/-- Rust `layer_constraint_of`: the node's `LAYERING_LAYER_CONSTRAINT` if set, else `NONE`. -/
def layerConstraintOf (node : LNodeId) : LayeredM LayerConstraint := do
  let props := (← getNode node).props
  return if props.has LayeredOptions.LAYERING_LAYER_CONSTRAINT then
      props.getD LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.none
    else LayerConstraint.none

/-- Rust `edge_constraint_for`: `OUTGOING_ONLY` for `FIRST*`, `INCOMING_ONLY` for `LAST*`. -/
def edgeConstraintFor : LayerConstraint → Option EdgeConstraint
  | .first | .firstSeparate => some .outgoingOnly
  | .last | .lastSeparate => some .incomingOnly
  | .none => none

/-- The port type whose edges `reverseEdges` turns around for an edge constraint
(`INCOMING_ONLY` → `INPUT`, `OUTGOING_ONLY` → `OUTPUT`). -/
def portTypeFor : EdgeConstraint → PortType
  | .incomingOnly => .input
  | .outgoingOnly => .output
  | .none => .undefined

/-- `canReverseOutgoingEdge(sourceConstraint, edge)`: not yet reversed, not into a label dummy when the
source is `LAST`, and not into a `LAST_SEPARATE` node. -/
def canReverseOutgoingEdge (sourceConstraint : LayerConstraint) (edge : LEdgeId) : LayeredM Bool := do
  let ed ← getEdge edge
  if ed.internal.reversed then return false
  let some targetPort := ed.target | return false
  let some targetNode := (← getPort targetPort).owner | return false
  if sourceConstraint == .last then
    if (← getNode targetNode).type == .label then return false
  return (← layerConstraintOf targetNode) != .lastSeparate

/-- `canReverseIncomingEdge(targetConstraint, edge)`: not yet reversed, not from a label dummy when the
target is `FIRST`, and not from a `FIRST_SEPARATE` node. -/
def canReverseIncomingEdge (targetConstraint : LayerConstraint) (edge : LEdgeId) : LayeredM Bool := do
  let ed ← getEdge edge
  if ed.internal.reversed then return false
  let some sourcePort := ed.source | return false
  let some sourceNode := (← getPort sourcePort).owner | return false
  if targetConstraint == .first then
    if (← getNode sourceNode).type == .label then return false
  return (← layerConstraintOf sourceNode) != .firstSeparate

/-- `reverseEdges(graph, node, nodeLayerConstraint, targetPortType)`: per port (snapshot of the node's
ports) the outgoing edges (for `INPUT`/`UNDEFINED`), then the incoming edges (for `OUTPUT`/`UNDEFINED`,
read after the outgoing reversals) are reversed with port adaptation where allowed. -/
def reverseEdges (fallbackGraph : LGraphId) (node : LNodeId) (nodeLayerConstraint : LayerConstraint)
    (targetPortType : PortType) : LayeredM Unit := do
  let graph := (← nodeGraph node).getD fallbackGraph
  let ports := (← getNode node).ports
  for port in ports do
    if targetPortType == .input || targetPortType == .undefined then
      for edge in (← getPort port).outgoingEdges do
        if ← canReverseOutgoingEdge nodeLayerConstraint edge then
          LGraphUtil.reverseEdge edge graph true
    if targetPortType == .output || targetPortType == .undefined then
      for edge in (← getPort port).incomingEdges do
        if ← canReverseIncomingEdge nodeLayerConstraint edge then
          LGraphUtil.reverseEdge edge graph true

/-- Sets `EDGE_CONSTRAINT := OUTGOING_ONLY` (Java parity, see the module doc) and reverses the edges of a
node with a `FIRST*`/`LAST*` layer constraint. -/
def handleConstrainedNode (graph : LGraphId) (node : LNodeId) (layerConstraint : LayerConstraint)
    (edgeConstraint : EdgeConstraint) : LayeredM Unit := do
  modifyNode node fun n => { n with internal := { n.internal with edgeConstraint := .outgoingOnly } }
  reverseEdges graph node layerConstraint (portTypeFor edgeConstraint)

/-- `handleOuterNodes(graph)`: handles the layerless nodes with a layer constraint and returns the
others (in layerless order). -/
def handleOuterNodes (graph : LGraphId) : LayeredM (Array LNodeId) := do
  let nodes := (← getGraph graph).layerlessNodes
  let mut remaining : Array LNodeId := #[]
  for node in nodes do
    let layerConstraint ← layerConstraintOf node
    match edgeConstraintFor layerConstraint with
    | some edgeConstraint => handleConstrainedNode graph node layerConstraint edgeConstraint
    | none => remaining := remaining.push node
  return remaining

/-- Constraint of the node owning a port (`NONE` when the port or its owner is missing). -/
def portOwnerConstraint (port : Option LPortId) : LayeredM LayerConstraint := do
  let some p := port | return .none
  let some owner := (← getPort p).owner | return .none
  layerConstraintOf owner

/-- The "all ports reversed" scan of `handleInnerNodes`: every port is an eastern port with positive net
flow or a western port with negative net flow, no outgoing edge ends at a `LAST*` node and no incoming
edge starts at a `FIRST*` node. Stops at the first violation (Rust `break`). -/
def allPortsReversed (ports : Array LPortId) : LayeredM Bool := do
  for port in ports do
    let pt ← getPort port
    let looksReversed := (pt.side == .east && pt.netFlow > 0) || (pt.side == .west && pt.netFlow < 0)
    if !looksReversed then return false
    for edge in pt.outgoingEdges do
      let targetConstraint ← portOwnerConstraint (← getEdge edge).target
      if targetConstraint == .last || targetConstraint == .lastSeparate then return false
    for edge in pt.incomingEdges do
      let sourceConstraint ← portOwnerConstraint (← getEdge edge).source
      if sourceConstraint == .first || sourceConstraint == .firstSeparate then return false
  return true

/-- `handleInnerNodes(graph, remainingNodes)`: feedback-node detection for nodes with fixed port sides. -/
def handleInnerNodes (graph : LGraphId) (remainingNodes : Array LNodeId) : LayeredM Unit := do
  for node in remainingNodes do
    let layerConstraint ← layerConstraintOf node
    if let some edgeConstraint := edgeConstraintFor layerConstraint then
      handleConstrainedNode graph node layerConstraint edgeConstraint
      continue
    let nd ← getNode node
    let ports := nd.ports
    if ports.isEmpty then continue
    let portConstraints := if nd.props.has LayeredOptions.PORT_CONSTRAINTS then
        nd.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
      else PortConstraints.undefined
    if !portConstraints.isSideFixed then continue
    if ← allPortsReversed ports then
      reverseEdges graph node layerConstraint .undefined

/-- `process(layeredGraph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let remainingNodes ← handleOuterNodes graph
  handleInnerNodes graph remainingNodes

/-- The `EdgeAndLayerConstraintEdgeReverser` processor. -/
def processor : LayeredProcessor :=
  { name := "EdgeAndLayerConstraintEdgeReverser"
    process := fun graph monitor => do
      let _ ← monitor.begin "Edge and layer constraint edge reversal" 1.0
      run graph
      monitor.done }

end EdgeAndLayerConstraintEdgeReverser

builtin_initialize registerEdgeAndLayerConstraintEdgeReverser : Unit ←
  IntermediateProcessorStrategy.register .edgeAndLayerConstraintEdgeReverser
    EdgeAndLayerConstraintEdgeReverser.processor

end Elk.Alg.Layered.Intermediate
