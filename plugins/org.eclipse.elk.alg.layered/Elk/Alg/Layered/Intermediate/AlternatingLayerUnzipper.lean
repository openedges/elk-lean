import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
/-!
# `org.eclipse.elk.alg.layered.intermediate.unzipping.AlternatingLayerUnzipper`

Port of elk-rs `intermediate/alternating_layer_unzipper.rs` (Java
`intermediate/unzipping/AlternatingLayerUnzipper.java`; Rust and this port keep it in the
`intermediate` package). Splits each layer into `N` (`LAYER_UNZIPPING_LAYER_SPLIT`, minimum over
the layer's nodes) sub-layers by moving the nodes alternately into the sub-layers and splitting
the edges that now span several layers with long-edge dummies. Placeholder nodes keep the order
of the remaining nodes during the process and are removed at the end.

`LongEdgeSplitter.splitEdge` is not ported yet; `splitEdge` below is a private 1:1 port of the
Rust `LongEdgeSplitter::split_edge` (with `set_dummy_node_properties`, `move_head_labels`).
TODO(I5): replace it with `LongEdgeSplitter.splitEdge` once `LongEdgeSplitter.lean` exists.

Differences to Java, following Rust:
* layers with a split value `N <= 0` are skipped (Java would not terminate / throw);
* the `MINIMIZE_EDGE_LENGTH` heuristic is skipped for empty layers (Java divides by zero);
* new layers are inserted at `min(index, layer count)` (Java throws when out of range);
* removed placeholders get `layer := none` (`LNode::set_layer(None)`; Java only removes them
  from the layer list);
* the progress monitor is begun as `Alternating layer unzipping` (Java does not call `begin`).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace AlternatingLayerUnzipper

/-! ## `LongEdgeSplitter::split_edge` (private copy) -/

/-- `LongEdgeSplitter::set_dummy_node_properties(dummy, in_edge, out_edge)`: the long edge source
and target of the dummy, inherited from a preceding long edge/label dummy or a following label
dummy, else the ends of the split edge. -/
private def setDummyNodeProperties (dummy : LNodeId) (inEdge outEdge : LEdgeId) : LayeredM Unit := do
  let inEdgeSource := (← getEdge inEdge).source
  let outEdgeTarget := (← getEdge outEdge).target
  let inSourceNode ← match inEdgeSource with
    | some p => pure (← getPort p).owner
    | none => pure none
  let outTargetNode ← match outEdgeTarget with
    | some p => pure (← getPort p).owner
    | none => pure none
  let inSourceType ← match inSourceNode with
    | some n => pure (some (← getNode n).type)
    | none => pure none
  let outTargetType ← match outTargetNode with
    | some n => pure (some (← getNode n).type)
    | none => pure none
  if inSourceType == some .longEdge then
    if let some src := inSourceNode then
      let s := (← getNode src).internal
      modifyNode dummy fun x => { x with internal := { x.internal with
        longEdgeSource := s.longEdgeSource, longEdgeTarget := s.longEdgeTarget,
        longEdgeHasLabelDummies := s.longEdgeHasLabelDummies } }
  else if inSourceType == some .label then
    if let some src := inSourceNode then
      let s := (← getNode src).internal
      modifyNode dummy fun x => { x with internal := { x.internal with
        longEdgeSource := s.longEdgeSource, longEdgeTarget := s.longEdgeTarget,
        longEdgeHasLabelDummies := true } }
  else if outTargetType == some .label then
    if let some tgt := outTargetNode then
      let t := (← getNode tgt).internal
      modifyNode dummy fun x => { x with internal := { x.internal with
        longEdgeSource := t.longEdgeSource, longEdgeTarget := t.longEdgeTarget,
        longEdgeHasLabelDummies := true } }
  else
    modifyNode dummy fun x => { x with internal := { x.internal with
      longEdgeSource := inEdgeSource, longEdgeTarget := outEdgeTarget } }

/-- `LongEdgeSplitter::move_head_labels(old_edge, new_edge)`: labels placed at the `HEAD` move to
the new edge and remember the original edge in `END_LABEL_EDGE` (unless already set). -/
private def moveHeadLabels (oldEdge newEdge : LEdgeId) : LayeredM Unit := do
  for l in (← getEdge oldEdge).labels do
    let lb ← getLabel l
    let placement : EdgeLabelPlacement :=
      if lb.props.has LayeredOptions.EDGE_LABELS_PLACEMENT then
        lb.props.getD LayeredOptions.EDGE_LABELS_PLACEMENT .center
      else .center
    if placement != .head then continue
    modifyEdge oldEdge fun e => { e with labels := e.labels.filter (· != l) }
    modifyEdge newEdge fun e => { e with labels := e.labels.push l }
    if lb.internal.endLabelEdge.isNone then
      modifyLabel l fun x => { x with internal := { x.internal with endLabelEdge := some oldEdge } }

/-- `LongEdgeSplitter::split_edge(edge, dummy_node)`: the edge now ends at a new west input port
of the dummy; a new edge (a copy of the edge's properties without `JUNCTION_POINTS`) leads from a
new east output port of the dummy to the old target. The dummy's height is the edge thickness.
Returns the new edge.

The Rust property map also holds the `InternalProperties`, so `copy_properties` copies them as
well: the new edge gets `internal := edge.internal`. -/
private def splitEdge (edge : LEdgeId) (dummy : LNodeId) : LayeredM LEdgeId := do
  let ed ← getEdge edge
  let oldEdgeTarget := ed.target
  let stored : Option Float :=
    if ed.props.has CoreOptions.EDGE_THICKNESS then ed.props.get CoreOptions.EDGE_THICKNESS else none
  let mut thickness := stored.getD 1.0
  if thickness < 0.0 then
    thickness := 0.0
    setEdgeProp edge CoreOptions.EDGE_THICKNESS thickness
  let th := thickness
  modifyNode dummy fun x => { x with size := { x.size with y := th } }
  let portPos := (th / 2.0).floor
  let dummyInput ← createPort
  modifyPort dummyInput fun p => let p := p.setSide .west; { p with position := { p.position with y := portPos } }
  setPortNode dummyInput (some dummy)
  let dummyOutput ← createPort
  modifyPort dummyOutput fun p => let p := p.setSide .east; { p with position := { p.position with y := portPos } }
  setPortNode dummyOutput (some dummy)
  setEdgeTarget edge (some dummyInput)
  let old ← getEdge edge
  let dummyEdge ← createEdge {
    props := (PropertyMap.empty.copyFrom old.props).remove LayeredOptions.JUNCTION_POINTS
    internal := old.internal }
  setEdgeSource dummyEdge (some dummyOutput)
  setEdgeTarget dummyEdge oldEdgeTarget
  setDummyNodeProperties dummy edge dummyEdge
  moveHeadLabels edge dummyEdge
  return dummyEdge

/-! ## Unzipper -/

/-- `get_layer_split_property(layer)`: the minimum `LAYER_UNZIPPING_LAYER_SPLIT` stored on the
layer's nodes, else the option default (`2`). -/
def layerSplitProperty (layer : LayerId) : LayeredM Int := do
  let mut layerSplit : Int := 2147483647
  let mut propertyUnset := true
  for n in (← getLayer layer).nodes do
    let nd ← getNode n
    if nd.props.has LayeredOptions.LAYER_UNZIPPING_LAYER_SPLIT then
      propertyUnset := false
      let nodeValue := nd.props.getD LayeredOptions.LAYER_UNZIPPING_LAYER_SPLIT 1
      layerSplit := min layerSplit nodeValue
  if propertyUnset then
    return LayeredOptions.LAYER_UNZIPPING_LAYER_SPLIT.default.getD 2
  return layerSplit

/-- `get_reset_on_long_edges_property(layer)`: `false` as soon as one node stores `false`. -/
def resetOnLongEdgesProperty (layer : LayerId) : LayeredM Bool := do
  for n in (← getLayer layer).nodes do
    let nd ← getNode n
    if nd.props.has LayeredOptions.LAYER_UNZIPPING_RESET_ON_LONG_EDGES then
      if !nd.props.getD LayeredOptions.LAYER_UNZIPPING_RESET_ON_LONG_EDGES true then
        return false
  return true

/-- `get_minimize_edge_length_property(layer)`: `true` as soon as one node stores `true`. -/
def minimizeEdgeLengthProperty (layer : LayerId) : LayeredM Bool := do
  for n in (← getLayer layer).nodes do
    let nd ← getNode n
    if nd.props.has LayeredOptions.LAYER_UNZIPPING_MINIMIZE_EDGE_LENGTH then
      if nd.props.getD LayeredOptions.LAYER_UNZIPPING_MINIMIZE_EDGE_LENGTH false then
        return true
  return false

/-- `create_dummy_node(graph, edge)`: a `LONG_EDGE` dummy with `ORIGIN := edge` and
`PORT_CONSTRAINTS := FIXED_POS`. -/
def createDummyNode (graph : LGraphId) (edgeToSplit : LEdgeId) : LayeredM LNodeId :=
  createNode graph { type := .longEdge,
                     props := PropertyMap.empty.set LayeredOptions.PORT_CONSTRAINTS .fixedPos,
                     internal := { origin := some (.lEdge edgeToSplit) } }

/-- `place_node_at_index(node, layer, index)`: appends when `index` exceeds the layer size, else
inserts at `index`. -/
def placeNodeAtIndex (n : LNodeId) (layer : LayerId) (index : Nat) : LayeredM Unit := do
  if index > (← getLayer layer).nodes.size then
    setNodeLayer n (some layer)
  else
    setNodeLayerAtIndex n index (some layer)

/-- `shift_node(graph, sub_layers, target_layer, node_index)`: moves the node at `nodeIndex` of the
first sub-layer into sub-layer `targetLayer`, splits its incoming edges (in reverse order) over
the preceding sub-layers and its outgoing edges over the following ones, adds placeholders, and
returns the number of new nodes in the first sub-layer minus one (at least `0`). -/
def shiftNode (graph : LGraphId) (subLayers : Array LayerId) (targetLayer nodeIndex : Nat) : LayeredM Nat := do
  let some node := (← getLayer subLayers[0]!).nodes[nodeIndex]? | return 0
  if targetLayer > 0 then
    setNodeLayer node (some subLayers[targetLayer]!)
  let mut edgeCount := 0
  let mut noIncomingEdges := true
  let reversedIncomingEdges := (← withArena (·.nodeIncomingEdges node)).reverse
  for incomingEdge in reversedIncomingEdges do
    noIncomingEdges := false
    let mut nextEdgeToSplit := incomingEdge
    for layerIndex in [0:targetLayer] do
      let layer := subLayers[layerIndex]!
      let dummyNode ← createDummyNode graph nextEdgeToSplit
      placeNodeAtIndex dummyNode layer (nodeIndex + edgeCount)
      nextEdgeToSplit ← splitEdge nextEdgeToSplit dummyNode
    if targetLayer > 0 then
      edgeCount := edgeCount + 1
  if noIncomingEdges then
    for layerIndex in [0:targetLayer] do
      let layer := subLayers[layerIndex]!
      let dummyNode ← createNode graph { type := .placeholder }
      placeNodeAtIndex dummyNode layer (nodeIndex + edgeCount)
    if targetLayer > 0 then
      edgeCount := edgeCount + 1
  let mut extraEdge := false
  let outgoingEdges ← withArena (·.nodeOutgoingEdges node)
  for outgoingEdge in outgoingEdges do
    let mut nextEdgeToSplit := outgoingEdge
    for layerIndex in [targetLayer + 1:subLayers.size] do
      let layer := subLayers[layerIndex]!
      let dummyNode ← createDummyNode graph nextEdgeToSplit
      setNodeLayer dummyNode (some layer)
      nextEdgeToSplit ← splitEdge nextEdgeToSplit dummyNode
    if extraEdge then
      for layerIndex in [0:min (targetLayer + 1) subLayers.size] do
        let layer := subLayers[layerIndex]!
        let placeholder ← createNode graph { type := .nonshiftingPlaceholder }
        placeNodeAtIndex placeholder layer (nodeIndex + 1)
      edgeCount := edgeCount + 1
    extraEdge := true
  return if edgeCount > 0 then edgeCount - 1 else 0

/-- `remove_unconnected_placeholder_nodes(graph)`: every `PLACEHOLDER`/`NONSHIFTING_PLACEHOLDER`
leaves its layer. -/
def removeUnconnectedPlaceholderNodes (graph : LGraphId) : LayeredM Unit := do
  for layer in (← getGraph graph).layers do
    for n in (← getLayer layer).nodes do
      let t := (← getNode n).type
      if t == .placeholder || t == .nonshiftingPlaceholder then
        setNodeLayer n none

/-- The `MINIMIZE_EDGE_LENGTH` heuristic: `true` when the layer should *not* be split
(`maxWidth / averageHeight >= nodeCount / 4`). Empty layers are never skipped. -/
def skipByEdgeLengthHeuristic (graph : LGraphId) (layer : LayerId) : LayeredM Bool := do
  let layerNodes := (← getLayer layer).nodes
  if layerNodes.isEmpty then return false
  let mut maxWidth : Float := 0.0
  let mut averageHeight : Float := 0.0
  for n in layerNodes do
    let nd ← getNode n
    maxWidth := fmax maxWidth nd.size.x
    averageHeight := averageHeight + nd.size.y
  let count := layerNodes.size.toFloat
  averageHeight := averageHeight / count
  let props := (← getGraph graph).props
  let edgeNodeBetweenLayers := props.getD LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS 0.0
  let edgeEdgeBetweenLayers := props.getD LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS 0.0
  let nodeNodeBetweenLayers := props.getD LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS 0.0
  let nodeNode := props.getD LayeredOptions.SPACING_NODE_NODE 0.0
  let edgeNode := props.getD LayeredOptions.SPACING_EDGE_NODE 0.0
  maxWidth := maxWidth + fmax (2.0 * edgeNodeBetweenLayers) (fmax (count * edgeEdgeBetweenLayers) nodeNodeBetweenLayers)
  averageHeight := averageHeight + fmax nodeNode edgeNode
  return maxWidth / averageHeight >= count / 4.0

/-- Distributes the nodes of `subLayers[0]` over the sub-layers (the `j`/`node_index`/
`target_layer` loop of Rust `process`; `target_layer.rem_euclid(n)`). -/
def unzipLayer (graph : LGraphId) (subLayers : Array LayerId) (n : Int) (resetOnLongEdges : Bool) :
    LayeredM Unit := do
  let nodesInLayer : Int := (← getLayer subLayers[0]!).nodes.size
  let mut j : Int := 0
  let mut nodeIndex : Int := 0
  let mut targetLayer : Int := 0
  while j < nodesInLayer do
    let some node := (← getLayer subLayers[0]!).nodes[nodeIndex.toNat]? | break
    let nodeType := (← getNode node).type
    if nodeType != .nonshiftingPlaceholder then
      let shifted ← shiftNode graph subLayers (Int.emod targetLayer n).toNat nodeIndex.toNat
      nodeIndex := nodeIndex + shifted
    else
      j := j - 1
      targetLayer := targetLayer - 1
    if resetOnLongEdges && nodeType == .longEdge then
      targetLayer := -1
    j := j + 1
    nodeIndex := nodeIndex + 1
    targetLayer := targetLayer + 1

/-- `AlternatingLayerUnzipper.process(graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Alternating layer unzipping" 1.0
  let mut insertionLayerOffset : Nat := 1
  let mut newLayers : Array (LayerId × Nat) := #[]
  let originalLayers := (← getGraph graph).layers
  for i in [0:originalLayers.size] do
    let layer := originalLayers[i]!
    let n ← layerSplitProperty layer
    let resetOnLongEdges ← resetOnLongEdgesProperty layer
    let minimizeEdgeLength ← minimizeEdgeLengthProperty layer
    if n <= 0 then continue
    if minimizeEdgeLength then
      if (← skipByEdgeLengthHeuristic graph layer) then continue
    let layerNodeCount := (← getLayer layer).nodes.size
    if layerNodeCount >= n.toNat then
      let mut subLayers : Array LayerId := #[layer]
      for j in [0:n.toNat - 1] do
        let newLayer ← createLayer graph
        newLayers := newLayers.push (newLayer, i + j + insertionLayerOffset)
        subLayers := subLayers.push newLayer
      insertionLayerOffset := insertionLayerOffset + (n.toNat - 1)
      unzipLayer graph subLayers n resetOnLongEdges
  for (newLayer, insertionIndex) in newLayers do
    modifyGraph graph fun g =>
      { g with layers := g.layers.insertIdx! (min insertionIndex g.layers.size) newLayer }
  removeUnconnectedPlaceholderNodes graph
  monitor.done

/-- `AlternatingLayerUnzipper` as a layered processor. -/
def processor : LayeredProcessor :=
  { name := "AlternatingLayerUnzipper", process := process }

end AlternatingLayerUnzipper

builtin_initialize registerAlternatingLayerUnzipper : Unit ←
  IntermediateProcessorStrategy.register .alternatingLayerUnzipper AlternatingLayerUnzipper.processor

end Elk.Alg.Layered.Intermediate
