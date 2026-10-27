import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.Intermediate.LongEdgeSplitter
/-!
# `org.eclipse.elk.alg.layered.intermediate.unzipping.AlternatingLayerUnzipper`

Port of elk-rs `intermediate/alternating_layer_unzipper.rs` (Java
`intermediate/unzipping/AlternatingLayerUnzipper.java`; Rust and this port keep it in the
`intermediate` package). Splits each layer into `N` (`LAYER_UNZIPPING_LAYER_SPLIT`, minimum over
the layer's nodes) sub-layers by moving the nodes alternately into the sub-layers and splitting
the edges that now span several layers with long-edge dummies. Placeholder nodes keep the order
of the remaining nodes during the process and are removed at the end.

Edges are split with `LongEdgeSplitter.splitEdge` (Rust `LongEdgeSplitter::split_edge`).

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

/-! ## Unzipping -/

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
      nextEdgeToSplit ← LongEdgeSplitter.splitEdge nextEdgeToSplit dummyNode
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
      nextEdgeToSplit ← LongEdgeSplitter.splitEdge nextEdgeToSplit dummyNode
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
