import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.InvertedPortProcessor`

Port of elk-rs `intermediate/inverted_port_processor.rs`. Inserts a `LONG_EDGE` dummy node in the
node's own layer for every edge entering an eastern input port or leaving a western output port
of a normal node with fixed port sides (self loops are skipped), so that the edge can be routed
around the node: the original edge is cut at the dummy's western input port and a new edge (all
properties copied except `JUNCTION_POINTS`, `HEAD` labels moved) continues from the dummy's
eastern output port.

Rust behaviour followed here (deviations from Java): the dummies are appended to the layer as they
are created (Java collects them and appends them after the layer's nodes, which yields the same
order); `LONG_EDGE_SOURCE`/`LONG_EDGE_TARGET` are **not** set on the dummies (Java
`setLongEdgeSourceAndTarget`) and moved head labels do not get `END_LABEL_EDGE`.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace InvertedPortProcessor

/-- `create_dummy_node(layer, origin_edge)`: a `LONG_EDGE` dummy (`ORIGIN = edge`, `FIXED_POS`)
appended to `layer`. -/
def createDummyNode (layer : LayerId) (originEdge : LEdgeId) : LayeredM LNodeId := do
  let graph := (← getLayer layer).owner
  let dummy ← createNode graph { type := .longEdge }
  modifyNode dummy fun n => { n with
    internal := { n.internal with origin := some (.lEdge originEdge) },
    props := n.props.set LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedPos }
  setNodeLayer dummy (some layer)
  return dummy

/-- `create_dummy_port(dummy, side)`. -/
def createDummyPort (dummy : LNodeId) (side : PortSide) : LayeredM LPortId := do
  let port ← LayeredM.createPort
  modifyPort port (·.setSide side)
  setPortNode port (some dummy)
  return port

/-- `move_head_labels(old_edge, new_edge)`: moves the `HEAD` labels (no `END_LABEL_EDGE`). -/
def moveHeadLabels (oldEdge newEdge : LEdgeId) : LayeredM Unit := do
  for label in (← getEdge oldEdge).labels do
    let lb ← getLabel label
    let placement := (if lb.props.has LayeredOptions.EDGE_LABELS_PLACEMENT then
      lb.props.get LayeredOptions.EDGE_LABELS_PLACEMENT else none).getD EdgeLabelPlacement.center
    if placement != .head then continue
    modifyEdge oldEdge fun e => { e with labels := e.labels.filter (· != label) }
    modifyEdge newEdge fun e => { e with labels := e.labels.push label }

/-- The part shared by both Rust functions: cuts `edge` at a new dummy and connects the dummy's
output port to `newTarget` with a new edge (the eastern port, or the edge's original target). -/
private def insertDummy (layer : LayerId) (edge : LEdgeId) (newTarget : Option LPortId) : LayeredM Unit := do
  let dummy ← createDummyNode layer edge
  let dummyInput ← createDummyPort dummy .west
  let dummyOutput ← createDummyPort dummy .east
  setEdgeTarget edge (some dummyInput)
  let old ← getEdge edge
  -- `copy_properties` into the empty map of the new edge = all public and internal properties
  let dummyEdge ← createEdge { props := old.props.remove LayeredOptions.JUNCTION_POINTS, internal := old.internal }
  setEdgeSource dummyEdge (some dummyOutput)
  setEdgeTarget dummyEdge newTarget
  moveHeadLabels edge dummyEdge

/-- Whether both nodes exist and are the same node (self loop). -/
private def sameNode (a b : Option LNodeId) : Bool :=
  match a, b with
  | some x, some y => x == y
  | _, _ => false

/-- `create_east_port_side_dummy(layer, east_port, edge)` (Java `createEastPortSideDummies`). -/
def createEastPortSideDummy (layer : LayerId) (eastPort : LPortId) (edge : LEdgeId) : LayeredM Unit := do
  let sourceNode ← match (← getEdge edge).source with
    | some s => pure (← getPort s).owner
    | none => pure none
  let targetNode := (← getPort eastPort).owner
  if sameNode sourceNode targetNode then return
  insertDummy layer edge (some eastPort)

/-- `create_west_port_side_dummy(layer, west_port, edge)` (Java `createWestPortSideDummies`). -/
def createWestPortSideDummy (layer : LayerId) (westPort : LPortId) (edge : LEdgeId) : LayeredM Unit := do
  let sourceNode := (← getPort westPort).owner
  let originalTarget := (← getEdge edge).target
  let targetNode ← match originalTarget with
    | some t => pure (← getPort t).owner
    | none => pure none
  if sameNode sourceNode targetNode then return
  insertDummy layer edge originalTarget

/-- `process(layered_graph, monitor)`: per layer over a copy of its node list; normal nodes with
an explicitly set side-fixing `PORT_CONSTRAINTS` only. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Inverted port preprocessing" 1.0
  for layer in (← getGraph graph).layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      let nd ← getNode node
      let skip := nd.type != .normal || !nd.props.has LayeredOptions.PORT_CONSTRAINTS
        || !(nd.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined).isSideFixed
      if skip then continue
      let eastInputPorts ← withArena (·.nodePortsByTypeAndSide node .input .east)
      for eastPort in eastInputPorts do
        for edge in (← getPort eastPort).incomingEdges do
          createEastPortSideDummy layer eastPort edge
      let westOutputPorts ← withArena (·.nodePortsByTypeAndSide node .output .west)
      for westPort in westOutputPorts do
        for edge in (← getPort westPort).outgoingEdges do
          createWestPortSideDummy layer westPort edge
  monitor.done

/-- The `InvertedPortProcessor` processor. -/
def processor : LayeredProcessor := { name := "InvertedPortProcessor", process := process }

end InvertedPortProcessor

builtin_initialize registerInvertedPortProcessor : Unit ←
  IntermediateProcessorStrategy.register .invertedPortProcessor InvertedPortProcessor.processor

end Elk.Alg.Layered.Intermediate
