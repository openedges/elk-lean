import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.LongEdgeSplitter`

Port of elk-rs `intermediate/long_edge_splitter.rs`. Splits the long edges of the layered graph
to obtain a proper layering: for each edge that connects two nodes more than one layer apart, a
`LONG_EDGE` dummy node is created in the next layer and the edge is split there. The dummy nodes
keep the original long edge's source and target ports (`LONG_EDGE_SOURCE`/`LONG_EDGE_TARGET`).

Iteration order (Rust): layers `0 .. n-2` of the layer list taken at the start; per layer the node
list read when the layer is visited (so dummies appended to layer `i + 1` while visiting layer `i`
are split further when layer `i + 1` is visited); per node its ports, per port its outgoing edges
(copies). The `rust-long-split` debug trace is omitted.

`splitEdge` is public, as in Java/Rust, for other processors that split edges.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace LongEdgeSplitter

/-- `create_dummy_node(target_layer, edge_to_split)` (Java `createDummyNode`): a `LONG_EDGE` dummy
with `ORIGIN = edge` and `FIXED_POS` port constraints, appended to `targetLayer`. -/
def createDummyNode (targetLayer : LayerId) (edgeToSplit : LEdgeId) : LayeredM LNodeId := do
  let graph := (← getLayer targetLayer).owner
  let dummy ← createNode graph { type := .longEdge }
  modifyNode dummy fun n => { n with
    internal := { n.internal with origin := some (.lEdge edgeToSplit) },
    props := n.props.set LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedPos }
  setNodeLayer dummy (some targetLayer)
  return dummy

/-- `target_layer_index(edge, layers)`: index of the target node's layer in `layers` (`0` when
the target has no layer or the layer is not in the list, as in Rust). -/
def targetLayerIndex (edge : LEdgeId) (layers : Array LayerId) : LayeredM Nat := do
  let some target := (← getEdge edge).target | return 0
  let some node := (← getPort target).owner | return 0
  let some layer := (← getNode node).layer | return 0
  return (layers.findIdx? (· == layer)).getD 0

/-- `move_head_labels(old_edge, new_edge)` (Java `moveHeadLabels`): moves the `HEAD` labels of the
old edge to the new edge and records the old edge as their `END_LABEL_EDGE` (unless set). -/
def moveHeadLabels (oldEdge newEdge : LEdgeId) : LayeredM Unit := do
  for label in (← getEdge oldEdge).labels do
    let lb ← getLabel label
    let placement := (if lb.props.has LayeredOptions.EDGE_LABELS_PLACEMENT then
      lb.props.get LayeredOptions.EDGE_LABELS_PLACEMENT else none).getD EdgeLabelPlacement.center
    if placement != .head then continue
    modifyEdge oldEdge fun e => { e with labels := e.labels.filter (· != label) }
    modifyEdge newEdge fun e => { e with labels := e.labels.push label }
    modifyLabel label fun l =>
      if l.internal.endLabelEdge.isSome then l
      else { l with internal := { l.internal with endLabelEdge := some oldEdge } }

/-- `set_dummy_node_properties(dummy_node, in_edge, out_edge)` (Java `setDummyNodeProperties`):
copies `LONG_EDGE_SOURCE`/`LONG_EDGE_TARGET` (and `LONG_EDGE_HAS_LABEL_DUMMIES`) from a preceding
long edge or label dummy, or from a succeeding label dummy; otherwise the in-edge's source and the
out-edge's target become the long edge's end ports. -/
def setDummyNodeProperties (dummyNode : LNodeId) (inEdge outEdge : LEdgeId) : LayeredM Unit := do
  let inEdgeSource := (← getEdge inEdge).source
  let outEdgeTarget := (← getEdge outEdge).target
  let inEdgeSourceNode ← match inEdgeSource with
    | some p => pure (← getPort p).owner
    | none => pure none
  let outEdgeTargetNode ← match outEdgeTarget with
    | some p => pure (← getPort p).owner
    | none => pure none
  let inSourceType ← match inEdgeSourceNode with
    | some n => pure (some (← getNode n).type)
    | none => pure none
  let outTargetType ← match outEdgeTargetNode with
    | some n => pure (some (← getNode n).type)
    | none => pure none
  if inSourceType == some NodeType.longEdge then
    if let some source := inEdgeSourceNode then
      let src := (← getNode source).internal
      modifyNode dummyNode fun d => { d with internal := { d.internal with
        longEdgeSource := src.longEdgeSource, longEdgeTarget := src.longEdgeTarget,
        longEdgeHasLabelDummies := src.longEdgeHasLabelDummies } }
  else if inSourceType == some NodeType.label then
    if let some source := inEdgeSourceNode then
      let src := (← getNode source).internal
      modifyNode dummyNode fun d => { d with internal := { d.internal with
        longEdgeSource := src.longEdgeSource, longEdgeTarget := src.longEdgeTarget,
        longEdgeHasLabelDummies := true } }
  else if outTargetType == some NodeType.label then
    if let some target := outEdgeTargetNode then
      let tgt := (← getNode target).internal
      modifyNode dummyNode fun d => { d with internal := { d.internal with
        longEdgeSource := tgt.longEdgeSource, longEdgeTarget := tgt.longEdgeTarget,
        longEdgeHasLabelDummies := true } }
  else
    modifyNode dummyNode fun d => { d with internal := { d.internal with
      longEdgeSource := inEdgeSource, longEdgeTarget := outEdgeTarget } }

/-- `LongEdgeSplitter::split_edge(edge, dummy_node)` (Java `splitEdge`): reroutes `edge` into a
new western input port of `dummyNode` and connects a new eastern output port to the old target
with a new edge that copies all properties of `edge` except `JUNCTION_POINTS`. The dummy's height
is the edge thickness (negative thicknesses are clamped to `0` and written back); both ports sit
at `floor(thickness / 2)`. Returns the new edge. -/
def splitEdge (edge : LEdgeId) (dummyNode : LNodeId) : LayeredM LEdgeId := do
  let oldEdgeTarget := (← getEdge edge).target
  let ed ← getEdge edge
  let mut thickness := (if ed.props.has CoreOptions.EDGE_THICKNESS then
    ed.props.get CoreOptions.EDGE_THICKNESS else none).getD 1.0
  if thickness < 0.0 then
    thickness := 0.0
    setEdgeProp edge CoreOptions.EDGE_THICKNESS 0.0
  let height := thickness
  modifyNode dummyNode fun n => { n with size := { n.size with y := height } }
  let portPos := Float.floor (thickness / 2.0)
  let dummyInput ← LayeredM.createPort
  modifyPort dummyInput fun p =>
    let p := p.setSide .west
    { p with position := { p.position with y := portPos } }
  setPortNode dummyInput (some dummyNode)
  let dummyOutput ← LayeredM.createPort
  modifyPort dummyOutput fun p =>
    let p := p.setSide .east
    { p with position := { p.position with y := portPos } }
  setPortNode dummyOutput (some dummyNode)
  setEdgeTarget edge (some dummyInput)
  let old ← getEdge edge
  -- `copy_properties` into the empty map of the new edge = all public and internal properties
  let dummyEdge ← createEdge { props := old.props.remove LayeredOptions.JUNCTION_POINTS, internal := old.internal }
  setEdgeSource dummyEdge (some dummyOutput)
  setEdgeTarget dummyEdge oldEdgeTarget
  setDummyNodeProperties dummyNode edge dummyEdge
  moveHeadLabels edge dummyEdge
  return dummyEdge

/-- `process(layered_graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Edge splitting" 1.0
  let layers := (← getGraph graph).layers
  if layers.size <= 2 then
    monitor.done
    return
  for layerIndex in [0:layers.size - 1] do
    let layer := layers[layerIndex]!
    let nextLayer := layers[layerIndex + 1]!
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      let ports := (← getNode node).ports
      for port in ports do
        let outgoing := (← getPort port).outgoingEdges
        for edge in outgoing do
          let targetIndex ← targetLayerIndex edge layers
          if targetIndex != layerIndex && targetIndex != layerIndex + 1 then
            let dummy ← createDummyNode nextLayer edge
            let _ ← splitEdge edge dummy
  monitor.done

/-- The `LongEdgeSplitter` processor. -/
def processor : LayeredProcessor := { name := "LongEdgeSplitter", process := process }

end LongEdgeSplitter

builtin_initialize registerLongEdgeSplitter : Unit ←
  IntermediateProcessorStrategy.register .longEdgeSplitter LongEdgeSplitter.processor

end Elk.Alg.Layered.Intermediate
