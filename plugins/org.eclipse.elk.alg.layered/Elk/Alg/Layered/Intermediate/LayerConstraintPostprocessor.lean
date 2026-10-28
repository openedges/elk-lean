import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.LayerConstraintPostprocessor`

Port of elk-rs `intermediate/layer_constraint_postprocessor.rs`. After layering:
1. `FIRST` nodes move to the first and `LAST` nodes to the last layer (they must not have incoming resp.
   outgoing edges except from/to label dummies, else `UnsupportedConfigurationException`); the label
   dummies of their incoming (`FIRST`) / outgoing (`LAST`) edges move to a new label layer inserted
   before the first / after the last layer. Layers left empty are removed before the label layers are
   added (only non-empty label layers are added).
2. The hidden `FIRST_SEPARATE`/`LAST_SEPARATE` nodes (`HIDDEN_NODES`) go to new separate first/last layers
   (only added when non-empty) and their detached edges are reconnected to `ORIGINAL_OPPOSITE_PORT`.

Deviation: the new layers belong to the processed graph. Rust takes the graph of the first layer, else of
the first layerless node, else a fresh `LGraph` (only reachable for a graph with neither, where no node
can end up in those layers anyway).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Options Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace LayerConstraintPostprocessor

/-- Rust `layer_constraint_of`: the node's `LAYERING_LAYER_CONSTRAINT` if set, else `NONE`. -/
def layerConstraintOf (node : LNodeId) : LayeredM LayerConstraint := do
  let props := (← getNode node).props
  return if props.has LayeredOptions.LAYERING_LAYER_CONSTRAINT then
      props.getD LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.none
    else LayerConstraint.none

/-- Node type of the owner of an optional port (`NORMAL` when missing, like Rust's `unwrap_or`). -/
def portOwnerType (port : Option LPortId) : LayeredM NodeType := do
  let some p := port | return .normal
  let some owner := (← getPort p).owner | return .normal
  return (← getNode owner).type

/-- `throwUpUnlessNoIncomingEdges(node)`: a `FIRST` node may only have incoming edges from label dummies
(the node is recorded in `LGraphArena.errorNode`, see `LayerConstraintPreprocessor`). -/
def throwUpUnlessNoIncomingEdges (node : LNodeId) : LayeredM Unit := do
  for edge in (← withArena (·.nodeIncomingEdges node)) do
    if (← portOwnerType (← getEdge edge).source) != .label then
      let designation ← withArena (·.nodeDesignation node)
      modify fun a => { a with errorNode := some node }
      -- Java's text has two spaces after "that" (string concatenation)
      throwUnsupportedConfiguration s!"Node '{designation}' has its layer constraint set to FIRST, but has at least one incoming edge that  does not come from a FIRST_SEPARATE node. That must not happen."

/-- `throwUpUnlessNoOutgoingEdges(node)`: a `LAST` node may only have outgoing edges to label dummies. -/
def throwUpUnlessNoOutgoingEdges (node : LNodeId) : LayeredM Unit := do
  for edge in (← withArena (·.nodeOutgoingEdges node)) do
    if (← portOwnerType (← getEdge edge).target) != .label then
      let designation ← withArena (·.nodeDesignation node)
      modify fun a => { a with errorNode := some node }
      throwUnsupportedConfiguration s!"Node '{designation}' has its layer constraint set to LAST, but has at least one outgoing edge that  does not go to a LAST_SEPARATE node. That must not happen."

/-- `moveLabelsToLabelLayer(node, incoming, labelLayer)`: the label dummies at the other end of the
node's incoming (or outgoing) edges move to the label layer. -/
def moveLabelsToLabelLayer (node : LNodeId) (incoming : Bool) (labelLayer : LayerId) : LayeredM Unit := do
  let edges ← withArena fun a => if incoming then a.nodeIncomingEdges node else a.nodeOutgoingEdges node
  for edge in edges do
    let ed ← getEdge edge
    let some port := (if incoming then ed.source else ed.target) | continue
    let some possibleLabelDummy := (← getPort port).owner | continue
    if (← getNode possibleLabelDummy).type == .label then
      setNodeLayer possibleLabelDummy (some labelLayer)

/-- `moveFirstAndLastNodes(...)`: moves `FIRST`/`LAST` nodes (layer and node snapshots) and removes the
layers that became empty. -/
def moveFirstAndLastNodes (graph : LGraphId) (firstLayer lastLayer firstLabelLayer lastLabelLayer : LayerId) :
    LayeredM Unit := do
  for layer in (← getGraph graph).layers do
    for node in (← getLayer layer).nodes do
      match ← layerConstraintOf node with
      | .first =>
        throwUpUnlessNoIncomingEdges node
        setNodeLayer node (some firstLayer)
        moveLabelsToLabelLayer node true firstLabelLayer
      | .last =>
        throwUpUnlessNoOutgoingEdges node
        setNodeLayer node (some lastLayer)
        moveLabelsToLabelLayer node false lastLabelLayer
      | _ => pure ()
  let mut kept : Array LayerId := #[]
  for layer in (← getGraph graph).layers do
    if !(← getLayer layer).nodes.isEmpty then kept := kept.push layer
  let layers := kept
  modifyGraph graph fun g => { g with layers := layers }

/-- `restoreHiddenNodes(hiddenNodes, firstSeparateLayer, lastSeparateLayer)`: puts each hidden node into
its separate layer and reconnects each half-detached connected edge to its `ORIGINAL_OPPOSITE_PORT`. -/
def restoreHiddenNodes (hiddenNodes : Array LNodeId) (firstSeparateLayer lastSeparateLayer : LayerId) :
    LayeredM Unit := do
  for hiddenNode in hiddenNodes do
    match ← layerConstraintOf hiddenNode with
    | .firstSeparate => setNodeLayer hiddenNode (some firstSeparateLayer)
    | .lastSeparate => setNodeLayer hiddenNode (some lastSeparateLayer)
    | _ => pure ()
    for hiddenEdge in (← withArena (·.nodeConnectedEdges hiddenNode)) do
      let ed ← getEdge hiddenEdge
      if ed.source.isSome && ed.target.isSome then continue
      let isOutgoing := ed.target.isNone
      let some opposite := ed.internal.originalOppositePort | continue
      if isOutgoing then setEdgeTarget hiddenEdge (some opposite) else setEdgeSource hiddenEdge (some opposite)

/-- Inserts `first` at the front and appends `last` to the graph's layers when they are non-empty. -/
def addOuterLayers (graph : LGraphId) (first last : LayerId) : LayeredM Unit := do
  if !(← getLayer first).nodes.isEmpty then
    modifyGraph graph fun g => { g with layers := g.layers.insertIdx! 0 first }
  if !(← getLayer last).nodes.isEmpty then
    modifyGraph graph fun g => { g with layers := g.layers.push last }

/-- `process(layeredGraph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let layers := (← getGraph graph).layers
  if let (some firstLayer, some lastLayer) := (layers[0]?, layers.back?) then
    let firstLabelLayer ← createLayer graph
    let lastLabelLayer ← createLayer graph
    moveFirstAndLastNodes graph firstLayer lastLayer firstLabelLayer lastLabelLayer
    addOuterLayers graph firstLabelLayer lastLabelLayer
  let hiddenNodes := (← getGraph graph).internal.hiddenNodes
  if !hiddenNodes.isEmpty then
    let firstSeparateLayer ← createLayer graph
    let lastSeparateLayer ← createLayer graph
    restoreHiddenNodes hiddenNodes firstSeparateLayer lastSeparateLayer
    addOuterLayers graph firstSeparateLayer lastSeparateLayer

/-- The `LayerConstraintPostprocessor` processor. -/
def processor : LayeredProcessor :=
  { name := "LayerConstraintPostprocessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Layer constraint postprocessing" 1.0
      run graph
      monitor.done }

end LayerConstraintPostprocessor

builtin_initialize registerLayerConstraintPostprocessor : Unit ←
  IntermediateProcessorStrategy.register .layerConstraintPostprocessor LayerConstraintPostprocessor.processor

end Elk.Alg.Layered.Intermediate
