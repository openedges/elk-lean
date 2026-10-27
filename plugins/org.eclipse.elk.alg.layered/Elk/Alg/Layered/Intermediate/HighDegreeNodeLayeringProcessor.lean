import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.HighDegreeNodeLayeringProcessor`

Port of elk-rs `intermediate/high_degree_node_layering_processor.rs`. After layering, small trees hanging
off high-degree nodes (degree `≥ HIGH_DEGREE_NODES_THRESHOLD`, default `16`) are moved into new layers
next to the high-degree node: for each original layer (snapshot), the incoming trees (roots are sources
of the node's incoming edges with a single outgoing connection) go into `incMax` new layers inserted
directly before the layer (root next to the layer, descendants further away), the outgoing trees into
`outMax` new layers directly after it. A tree must not contain a high-degree node, every node must have a
single connection towards the root, and its height must not exceed `HIGH_DEGREE_NODES_TREE_HEIGHT`
(default `5`, `0` = unbounded). Empty layers are removed at the end.

Rust/Java parity notes: the new layers belong to the processed graph (Rust: graph of the first layer,
same graph); `move_tree` stops recursing when only one layer is left (Java recurses with an empty layer
list, which only happens at leaves). `moveTree` is ported as an iterative pre-order DFS (same order of
`setNodeLayer` calls as the Rust recursion); `isTreeRoot` stays recursive (`partial`: recursion over the
graph, terminated by the single-connection checks like in Rust).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace HighDegreeNodeLayeringProcessor

/-- The processor fields `degree_threshold` and `tree_height_threshold` (`i32`). -/
structure Config where
  degreeThreshold : Int := 16
  treeHeightThreshold : Int := 5

/-- `HighDegreeNodeInformation` (heights start at `-1`). -/
structure HighDegreeNodeInformation where
  incTreesMaxHeight : Int := -1
  incTreeRoots : Array LNodeId := #[]
  outTreesMaxHeight : Int := -1
  outTreeRoots : Array LNodeId := #[]
  deriving Inhabited

/-- Rust `EdgeSelector` (`LNode.getIncomingEdges/getOutgoingEdges/getConnectedEdges`). -/
inductive EdgeSelector where
  | incoming
  | outgoing
  | connected
  deriving BEq, Inhabited

/-- Rust `selected_edges(node, selector)`. -/
def selectedEdges (node : LNodeId) (selector : EdgeSelector) : LayeredM (Array LEdgeId) :=
  withArena fun a => match selector with
    | .incoming => a.nodeIncomingEdges node
    | .outgoing => a.nodeOutgoingEdges node
    | .connected => a.nodeConnectedEdges node

/-- Owner node of an optional port. -/
def portOwner (port : Option LPortId) : LayeredM (Option LNodeId) := do
  let some p := port | return none
  return (← getPort p).owner

/-- Rust `other_node(edge, node)`: the opposite end node; `none` unless both ends have nodes and `node`
is one of them. -/
def otherNode (edge : LEdgeId) (node : LNodeId) : LayeredM (Option LNodeId) := do
  let ed ← getEdge edge
  let some source ← portOwner ed.source | return none
  let some target ← portOwner ed.target | return none
  if source == node then return some target
  if target == node then return some source
  return none

/-- `isHighDegreeNode(node)`: connected edge count `≥ degreeThreshold`. -/
def isHighDegreeNode (cfg : Config) (node : LNodeId) : LayeredM Bool := do
  return ((← selectedEdges node .connected).size : Int) >= cfg.degreeThreshold

/-- `hasSingleConnection(node, edges)`: all selected edges lead to the same other node. -/
def hasSingleConnection (node : LNodeId) (selector : EdgeSelector) : LayeredM Bool := do
  let mut connection : Option LNodeId := none
  for edge in (← selectedEdges node selector) do
    let some other ← otherNode edge node | continue
    match connection with
    | some existing => if existing != other then return false
    | none => connection := some other
  return true

/-- `isTreeRoot(root, ancestorEdges, descendantEdges)`: the height of the tree rooted at `root`, or `-1`
if it is no (small enough) tree. -/
partial def isTreeRoot (cfg : Config) (root : LNodeId) (ancestorEdges descendantEdges : EdgeSelector) :
    LayeredM Int := do
  if ← isHighDegreeNode cfg root then return -1
  if !(← hasSingleConnection root ancestorEdges) then return -1
  let descendants ← selectedEdges root descendantEdges
  if descendants.isEmpty then return 1
  let mut currentHeight : Int := 0
  for edge in descendants do
    let some other ← otherNode edge root | return -1
    let subtreeHeight ← isTreeRoot cfg other ancestorEdges descendantEdges
    if subtreeHeight == -1 then return -1
    currentHeight := max currentHeight subtreeHeight
    if currentHeight > cfg.treeHeightThreshold - 1 then return -1
  return currentHeight + 1

/-- `calculateInformation(highDegreeNode)`: tree roots and maximal heights of the incoming and outgoing
trees (self loops skipped). -/
def calculateInformation (cfg : Config) (highDegreeNode : LNodeId) : LayeredM HighDegreeNodeInformation := do
  let mut info : HighDegreeNodeInformation := {}
  for incomingEdge in (← selectedEdges highDegreeNode .incoming) do
    if ← withArena (·.edgeIsSelfLoop incomingEdge) then continue
    let some source ← portOwner (← getEdge incomingEdge).source | continue
    if ← hasSingleConnection source .outgoing then
      let treeHeight ← isTreeRoot cfg source .outgoing .incoming
      if treeHeight == -1 then continue
      info := { info with
        incTreesMaxHeight := max info.incTreesMaxHeight treeHeight
        incTreeRoots := info.incTreeRoots.push source }
  for outgoingEdge in (← selectedEdges highDegreeNode .outgoing) do
    if ← withArena (·.edgeIsSelfLoop outgoingEdge) then continue
    let some target ← portOwner (← getEdge outgoingEdge).target | continue
    if ← hasSingleConnection target .incoming then
      let treeHeight ← isTreeRoot cfg target .incoming .outgoing
      if treeHeight == -1 then continue
      info := { info with
        outTreesMaxHeight := max info.outTreesMaxHeight treeHeight
        outTreeRoots := info.outTreeRoots.push target }
  return info

/-- Rust `collect_high_degree_nodes(layer)`: the high-degree nodes of the layer with their information and
the maximal incoming/outgoing tree heights (`-1` when none). -/
def collectHighDegreeNodes (cfg : Config) (layer : LayerId) :
    LayeredM (Array (LNodeId × HighDegreeNodeInformation) × Int × Int) := do
  let mut highDegreeNodes : Array (LNodeId × HighDegreeNodeInformation) := #[]
  let mut incMax : Int := -1
  let mut outMax : Int := -1
  for node in (← getLayer layer).nodes do
    if !(← isHighDegreeNode cfg node) then continue
    let info ← calculateInformation cfg node
    incMax := max incMax info.incTreesMaxHeight
    outMax := max outMax info.outTreesMaxHeight
    highDegreeNodes := highDegreeNodes.push (node, info)
  return (highDegreeNodes, incMax, outMax)

/-- `moveTree(root, edges, layers)`: the root goes to `layers[0]`, the nodes reached over the selected
edges to the following layers (pre-order like the Rust recursion; stops at the last layer). -/
def moveTree (root : LNodeId) (edges : EdgeSelector) (layers : Array LayerId) : LayeredM Unit := do
  if layers.isEmpty then return
  let mut stack : Array (LNodeId × Nat) := #[(root, 0)]
  while true do
    let some (node, depth) := stack.back? | break
    stack := stack.pop
    setNodeLayer node (some layers[depth]!)
    if depth + 1 >= layers.size then continue
    let mut children : Array LNodeId := #[]
    for edge in (← selectedEdges node edges) do
      let some other ← otherNode edge node | continue
      children := children.push other
    -- push in reverse so that the first child is visited first
    for child in children.reverse do
      stack := stack.push (child, depth + 1)

/-- Inserts `count` new layers into the graph starting at `index` and returns them in insertion order. -/
def insertLayers (graph : LGraphId) (index count : Nat) : LayeredM (Array LayerId) := do
  let mut created : Array LayerId := #[]
  for offset in [0:count] do
    let newLayer ← createLayer graph
    let position := index + offset
    modifyGraph graph fun g => { g with layers := g.layers.insertIdx! position newLayer }
    created := created.push newLayer
  return created

/-- `process(layeredGraph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let degreeThreshold := gr.props.getD LayeredOptions.HIGH_DEGREE_NODES_THRESHOLD 16
  let treeHeight := gr.props.getD LayeredOptions.HIGH_DEGREE_NODES_TREE_HEIGHT 5
  let cfg : Config := { degreeThreshold, treeHeightThreshold := if treeHeight == 0 then 2147483647 else treeHeight }
  for layer in gr.layers do
    let some layerIndex := (← getGraph graph).indexOfLayer layer | continue
    let (highDegreeNodes, incMax, outMax) ← collectHighDegreeNodes cfg layer
    -- Rust `pre_layers.insert(0, …)`: the layer closest to `layer` comes first
    let preLayers := (← insertLayers graph layerIndex (if incMax > 0 then incMax.toNat else 0)).reverse
    if !preLayers.isEmpty then
      for (_, info) in highDegreeNodes do
        for root in info.incTreeRoots do
          moveTree root .incoming preLayers
    let some currentIndex := (← getGraph graph).indexOfLayer layer | continue
    let afterLayers ← insertLayers graph (currentIndex + 1) (if outMax > 0 then outMax.toNat else 0)
    if !afterLayers.isEmpty then
      for (_, info) in highDegreeNodes do
        for root in info.outTreeRoots do
          moveTree root .outgoing afterLayers
  let mut kept : Array LayerId := #[]
  for layer in (← getGraph graph).layers do
    if !(← getLayer layer).nodes.isEmpty then kept := kept.push layer
  let layers := kept
  modifyGraph graph fun g => { g with layers := layers }

/-- The `HighDegreeNodeLayeringProcessor` processor. -/
def processor : LayeredProcessor :=
  { name := "HighDegreeNodeLayeringProcessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "High degree node processing" 1.0
      run graph
      monitor.done }

end HighDegreeNodeLayeringProcessor

builtin_initialize registerHighDegreeNodeLayeringProcessor : Unit ←
  IntermediateProcessorStrategy.register .highDegreeNodeLayerProcessor HighDegreeNodeLayeringProcessor.processor

end Elk.Alg.Layered.Intermediate
