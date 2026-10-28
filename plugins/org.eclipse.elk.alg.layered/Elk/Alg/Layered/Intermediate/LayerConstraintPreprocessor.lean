import Std.Data.HashMap
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.LayerConstraintPreprocessor`

Port of elk-rs `intermediate/layer_constraint_preprocessor.rs`. Removes the `FIRST_SEPARATE` and
`LAST_SEPARATE` nodes from the layerless nodes before layering ("hiding" them): their edges are detached
from the opposite port (remembered as `ORIGINAL_OPPOSITE_PORT` on the edge), the hidden nodes are stored
in the graph's `HIDDEN_NODES` (only when non-empty), and opposite nodes without a layer constraint that
lose all their edges this way get `FIRST` (only connected to `FIRST_SEPARATE` nodes) or `LAST` (only
`LAST_SEPARATE`). `LayerConstraintPostprocessor` restores everything.

`FIRST_SEPARATE` nodes must not have incoming and `LAST_SEPARATE` nodes no outgoing edges, unless the edge
connects two external port dummies (`UnsupportedConfigurationException`).

The per-node hidden connections (Rust `FxHashMap` keyed by node pointer, never iterated) are a
`Std.HashMap LNodeId HiddenNodeConnections` local to one run.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Options Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace LayerConstraintPreprocessor

/-- `HiddenNodeConnections`: to which kinds of hidden nodes a node was connected. -/
inductive HiddenNodeConnections where
  | none
  | firstSeparate
  | lastSeparate
  | both
  deriving BEq, Inhabited, Repr

namespace HiddenNodeConnections

/-- `HiddenNodeConnections.combine(layerConstraint)`. -/
def combine : HiddenNodeConnections → LayerConstraint → HiddenNodeConnections
  | .none, .firstSeparate => .firstSeparate
  | .none, .lastSeparate => .lastSeparate
  | .none, _ => .none
  | .firstSeparate, .lastSeparate => .both
  | .firstSeparate, _ => .firstSeparate
  | .lastSeparate, .firstSeparate => .both
  | .lastSeparate, _ => .lastSeparate
  | .both, _ => .both

end HiddenNodeConnections

/-- Hidden connections per opposite node. -/
abbrev HiddenConnections := Std.HashMap LNodeId HiddenNodeConnections

/-- Rust `layer_constraint_of`: the node's `LAYERING_LAYER_CONSTRAINT` if set, else `NONE`. -/
def layerConstraintOf (node : LNodeId) : LayeredM LayerConstraint := do
  let props := (← getNode node).props
  return if props.has LayeredOptions.LAYERING_LAYER_CONSTRAINT then
      props.getD LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.none
    else LayerConstraint.none

/-- `isRelevantNode(node)`: `FIRST_SEPARATE` or `LAST_SEPARATE`. -/
def isRelevantNode (node : LNodeId) : LayeredM Bool := do
  let constraint ← layerConstraintOf node
  return constraint == .firstSeparate || constraint == .lastSeparate

/-- Node type of the owner of an optional port. -/
def portOwnerType (port : Option LPortId) : LayeredM (Option NodeType) := do
  let some p := port | return none
  let some owner := (← getPort p).owner | return none
  return some (← getNode owner).type

/-- `isAcceptableIncidentEdge(edge)`: both ends are external port dummies. -/
def isAcceptableIncidentEdge (edge : LEdgeId) : LayeredM Bool := do
  let ed ← getEdge edge
  let sourceType ← portOwnerType ed.source
  let targetType ← portOwnerType ed.target
  return sourceType == some .externalPort && targetType == some .externalPort

/-- `ensureNoInacceptableEdges(node)`: throws `UnsupportedConfigurationException` for incoming edges of
`FIRST_SEPARATE` and outgoing edges of `LAST_SEPARATE` nodes (except external-port-to-external-port).
The node is recorded in `LGraphArena.errorNode` so that the provider can name it like Java's
`getDesignation()` (identifier path). -/
def ensureNoInacceptableEdges (node : LNodeId) : LayeredM Unit := do
  match ← layerConstraintOf node with
  | .firstSeparate =>
    for edge in (← withArena (·.nodeIncomingEdges node)) do
      if !(← isAcceptableIncidentEdge edge) then
        let designation ← withArena (·.nodeDesignation node)
        modify fun a => { a with errorNode := some node }
        throwUnsupportedConfiguration s!"Node '{designation}' has its layer constraint set to FIRST_SEPARATE, but has at least one incoming edge. FIRST_SEPARATE nodes must not have incoming edges."
  | .lastSeparate =>
    for edge in (← withArena (·.nodeOutgoingEdges node)) do
      if !(← isAcceptableIncidentEdge edge) then
        let designation ← withArena (·.nodeDesignation node)
        modify fun a => { a with errorNode := some node }
        throwUnsupportedConfiguration s!"Node '{designation}' has its layer constraint set to LAST_SEPARATE, but has at least one outgoing edge. LAST_SEPARATE nodes must not have outgoing edges."
  | _ => pure ()

/-- `updateOppositeNodeLayerConstraints(hiddenNode, oppositeNode)`: records the hidden connection of an
opposite node without a layer constraint and, once it has no edges left, constrains it to `FIRST`/`LAST`. -/
def updateOppositeNodeLayerConstraints (hiddenNode oppositeNode : LNodeId) (connections : HiddenConnections) :
    LayeredM HiddenConnections := do
  if (← getNode oppositeNode).props.has LayeredOptions.LAYERING_LAYER_CONSTRAINT then return connections
  let hiddenConstraint ← layerConstraintOf hiddenNode
  let next := (connections.getD oppositeNode .none).combine hiddenConstraint
  let connections := connections.insert oppositeNode next
  if !(← withArena (·.nodeConnectedEdges oppositeNode)).isEmpty then return connections
  match next with
  | .firstSeparate => setNodeProp oppositeNode LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.first
  | .lastSeparate => setNodeProp oppositeNode LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.last
  | .none | .both => pure ()
  return connections

/-- `hideEdge(hiddenNode, edge)`: detaches the edge end at the opposite port and remembers that port. -/
def hideEdge (hiddenNode : LNodeId) (edge : LEdgeId) (connections : HiddenConnections) :
    LayeredM HiddenConnections := do
  let ed ← getEdge edge
  let isOutgoing ← (do
    match ed.source with
    | some source => pure ((← getPort source).owner == some hiddenNode)
    | none => pure false)
  let some oppositePort := (if isOutgoing then ed.target else ed.source) | return connections
  if isOutgoing then setEdgeTarget edge none else setEdgeSource edge none
  modifyEdge edge fun e => { e with internal := { e.internal with originalOppositePort := some oppositePort } }
  match (← getPort oppositePort).owner with
  | some oppositeNode => updateOppositeNodeLayerConstraints hiddenNode oppositeNode connections
  | none => return connections

/-- `hide(node)`: validates the node's edges and hides each connected edge (snapshot, port order,
incoming before outgoing per port). -/
def hide (node : LNodeId) (connections : HiddenConnections) : LayeredM HiddenConnections := do
  ensureNoInacceptableEdges node
  let mut connections := connections
  for edge in (← withArena (·.nodeConnectedEdges node)) do
    connections ← hideEdge node edge connections
  return connections

/-- `process(layeredGraph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let mut hiddenNodes : Array LNodeId := #[]
  let mut connections : HiddenConnections := {}
  let mut index := 0
  while true do
    let nodes := (← getGraph graph).layerlessNodes
    if index >= nodes.size then break
    let node := nodes[index]!
    if ← isRelevantNode node then
      connections ← hide node connections
      hiddenNodes := hiddenNodes.push node
      let removeAt := index
      modifyGraph graph fun g => { g with layerlessNodes := g.layerlessNodes.eraseIdx! removeAt }
      continue
    index := index + 1
  if !hiddenNodes.isEmpty then
    let hidden := hiddenNodes
    modifyGraph graph fun g => { g with internal := { g.internal with hiddenNodes := hidden } }

/-- The `LayerConstraintPreprocessor` processor. -/
def processor : LayeredProcessor :=
  { name := "LayerConstraintPreprocessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Layer constraint preprocessing" 1.0
      run graph
      monitor.done }

end LayerConstraintPreprocessor

builtin_initialize registerLayerConstraintPreprocessor : Unit ←
  IntermediateProcessorStrategy.register .layerConstraintPreprocessor LayerConstraintPreprocessor.processor

end Elk.Alg.Layered.Intermediate
