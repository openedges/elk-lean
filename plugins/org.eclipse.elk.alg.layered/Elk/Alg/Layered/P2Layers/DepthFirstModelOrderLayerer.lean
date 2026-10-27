import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.p2layers.DepthFirstModelOrderLayerer` (elk-rs `depth_first_model_order_layerer.rs`)

Assigns layers in model order, depth first: the real nodes are visited by ascending
`MODEL_ORDER` (stable). A node connected to the current layer goes two layers (label dummy layer
plus node layer) behind its latest predecessor; a node without connection to the current layer
starts a new "chain" in layer 0 (if it has no incoming edges) whose nodes are collected in
`nodesToPlace` with their desired layer stored in `LNode.id` and placed when the chain ends (or
shifted when a later node needs more room). Every pair of new layers stores its intended index in
`Layer.id`; empty layers are removed at the end and `Layer.id` is set to the layer index.

The phase state (`currentLayer`, `currentLayerId`, `currentDummyLayer`, `nodesToPlace`,
`maxToPlace`) is a local `StateT` over `LayeredM`. Deviation (following Rust): the missing model
order is reported while collecting the real nodes.
-/
namespace Elk.Alg.Layered.P2Layers

open Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Alg
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace DepthFirstModelOrderLayerer

/-- `BASELINE_PROCESSING_CONFIGURATION`. -/
def BASELINE_PROCESSING_CONFIGURATION : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p1CycleBreaking .edgeAndLayerConstraintEdgeReverser
    |>.addBefore .p2Layering .layerConstraintPreprocessor
    |>.addBefore .p3NodeOrdering .layerConstraintPostprocessor

/-- Rust `id as usize` for an `i32` id: negative ids wrap to huge (out of range) indices. -/
private def usize (i : Int) : Nat := (i % 18446744073709551616).toNat

/-- The node owning the source port of `e`. -/
private def edgeSourceNode (a : LGraphArena) (e : LEdgeId) : Option LNodeId :=
  (a.edge e).source.bind fun p => (a.port p).owner

/-- The fields of the Rust `DepthFirstModelOrderLayerer`. -/
structure State where
  graph : LGraphId
  graphRef : LGraphId
  currentLayer : Option LayerId := none
  currentLayerId : Int := 0
  currentDummyLayer : Option LayerId := none
  nodesToPlace : Array LNodeId := #[]
  maxToPlace : Int := 0
  deriving Inhabited

/-- The layerer monad: the phase state over `LayeredM`. -/
abbrev DFM := StateT State LayeredM

/-- Creates a layer with the given `Layer.id` and appends it to the graph. -/
private def newLayer (id : Int) : DFM LayerId := do
  let s ← getThe State
  let layer ← createLayer s.graphRef
  modifyLayer layer fun l => { l with id := id }
  modifyGraph s.graph fun g => { g with layers := g.layers.push layer }
  return layer

/-- The layers of the graph. -/
private def graphLayers : DFM (Array LayerId) := do
  return (← getGraph (← getThe State).graph).layers

/-- `isConnectedToCurrentLayer(node)`: while no chain is pending the predecessor's layer id is
compared with `currentLayerId`, otherwise the predecessor's node id (its desired layer). -/
def isConnectedToCurrentLayer (node : LNodeId) : DFM Bool := do
  let s ← getThe State
  let pending := !s.nodesToPlace.isEmpty
  let currentLayerId := s.currentLayerId
  withArena fun a => (a.nodeIncomingEdges node).any fun edge =>
    match edgeSourceNode a edge with
    | none => false
    | some sourceNode =>
      let source := a.node sourceNode
      let labelSource : Option LNodeId :=
        ((a.nodeIncomingEdges sourceNode)[0]?).bind (edgeSourceNode a)
      if !pending then
        let directlyConnected := source.type == .normal &&
          (match source.layer with
           | some l => (a.layer l).id == currentLayerId
           | none => false)
        let connectedViaLabelDummy := source.type == .label &&
          (match labelSource.bind fun n => (a.node n).layer with
           | some l => (a.layer l).id == currentLayerId
           | none => false)
        directlyConnected || connectedViaLabelDummy
      else
        let directlyConnected := source.type == .normal && source.id == currentLayerId
        let connectedViaLabelDummy := source.type == .label &&
          (match labelSource with
           | some n => (a.node n).id == currentLayerId
           | none => false)
        directlyConnected || connectedViaLabelDummy

/-- `addNodeToLayer(layerId, node)`: puts `node` into layer `layerId` (creating the dummy layer
and the layer when they do not exist yet) and unplaced label dummies in front of it into the
dummy layer. -/
def addNodeToLayer (layerId : Int) (node : LNodeId) : DFM Unit := do
  let layers ← graphLayers
  let layerIndex := usize layerId
  if layerIndex < layers.size then
    modifyThe State fun s => { s with
      currentLayer := layers[layerIndex]?
      currentDummyLayer := layers[layerIndex - 1]?
      currentLayerId := layerId }
  else
    let dummyLayer ← newLayer (layerId - 1)
    let layer ← newLayer layerId
    modifyThe State fun s => { s with
      currentDummyLayer := some dummyLayer
      currentLayer := some layer
      currentLayerId := layerId }
  let s ← getThe State
  if let some currentLayer := s.currentLayer then
    setNodeLayer node (some currentLayer)
  for edge in ← withArena (·.nodeIncomingEdges node) do
    let some sourceNode ← withArena (edgeSourceNode · edge) | continue
    let source ← getNode sourceNode
    if source.type == .label && source.layer.isNone then
      if let some dummyLayer := s.currentDummyLayer then
        setNodeLayer sourceNode (some dummyLayer)

/-- `getMaxConnectedLayer(layerId, node)`: the maximum of `layerId` and the layer ids of the
placed predecessors of `node`. -/
def getMaxConnectedLayer (layerId : Int) (node : LNodeId) : DFM Int := do
  withArena fun a => (a.nodeIncomingEdges node).foldl (init := layerId) fun maxLayer edge =>
    match (edgeSourceNode a edge).bind fun n => (a.node n).layer with
    | some l => max maxLayer (a.layer l).id
    | none => maxLayer

/-- `placeNodesToPlace()`: puts every pending node into the layer stored in its id (adding one
dummy layer and one layer when the index is beyond the current layers). -/
def placeNodesToPlace : DFM Unit := do
  modifyThe State fun s => { s with maxToPlace := 0 }
  for nodeToPlace in (← getThe State).nodesToPlace do
    let desiredLayer := (← getNode nodeToPlace).id
    if usize desiredLayer >= (← graphLayers).size then
      let _ ← newLayer (desiredLayer - 1)
      let _ ← newLayer desiredLayer
    if let some layer := (← graphLayers)[usize desiredLayer]? then
      setNodeLayer nodeToPlace (some layer)

/-- Places the real nodes (sorted by model order) — the loop of `process`. -/
def layerNodes (realNodes : Array LNodeId) : DFM Unit := do
  let mut firstNode := true
  for node in realNodes do
    if firstNode then
      if let some currentLayer := (← getThe State).currentLayer then
        setNodeLayer node (some currentLayer)
      firstNode := false
      continue
    if ← isConnectedToCurrentLayer node then
      let currentLayerId := (← getThe State).currentLayerId
      let maxLayer ← getMaxConnectedLayer currentLayerId node
      let desiredLayer := maxLayer + 2
      let layerDiff := maxLayer - currentLayerId
      if !(← getThe State).nodesToPlace.isEmpty then
        if layerDiff > 0 then
          let s ← getThe State
          for toPlace in s.nodesToPlace do
            let newId := (← getNode toPlace).id + (maxLayer - s.maxToPlace)
            modifyNode toPlace fun x => { x with id := newId }
          placeNodesToPlace
          modifyThe State fun s => { s with nodesToPlace := #[] }
          addNodeToLayer desiredLayer node
        else
          modifyThe State fun s => { s with
            nodesToPlace := s.nodesToPlace.push node
            maxToPlace := max s.maxToPlace desiredLayer }
          modifyNode node fun x => { x with id := desiredLayer }
          for edge in ← withArena (·.nodeIncomingEdges node) do
            let some sourceNode ← withArena (edgeSourceNode · edge) | continue
            let source ← getNode sourceNode
            if source.type == .label && source.layer.isNone then
              modifyThe State fun s => { s with nodesToPlace := s.nodesToPlace.push sourceNode }
              modifyNode sourceNode fun x => { x with id := desiredLayer - 1 }
          modifyThe State fun s => { s with currentLayerId := desiredLayer }
      else
        addNodeToLayer desiredLayer node
    else
      placeNodesToPlace
      modifyThe State fun s => { s with nodesToPlace := #[] }
      if (← withArena (·.nodeIncomingEdges node)).isEmpty then
        let firstLayer := (← graphLayers)[0]?
        modifyNode node fun x => { x with id := 0 }
        modifyThe State fun s => { s with
          nodesToPlace := s.nodesToPlace.push node
          maxToPlace := max s.maxToPlace 0
          currentLayer := firstLayer
          currentLayerId := 0 }
      else
        let maxLayer ← getMaxConnectedLayer 0 node
        addNodeToLayer (maxLayer + 2) node
  if !(← getThe State).nodesToPlace.isEmpty then
    placeNodesToPlace

/-- `process(graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Depth first model order layering" 1.0
  let nodes := (← getGraph graph).layerlessNodes
  if nodes.isEmpty then
    monitor.done
    return
  let graphRef := (← nodeGraph nodes[0]!).getD graph
  let mut realNodes : Array (Int × LNodeId) := #[]
  for node in nodes do
    let nd ← getNode node
    if nd.type == .normal then
      let some order := nd.internal.modelOrder
        | throwUnsupportedGraph "The DF model order layer assigner requires all real nodes to have a model order."
      realNodes := realNodes.push (order, node)
  realNodes := stableSort realNodes fun (x, _) (y, _) => compare x y
  let firstLayer ← createLayer graphRef
  modifyLayer firstLayer fun l => { l with id := 0 }
  modifyGraph graph fun g => { g with layers := g.layers.push firstLayer }
  let state : State := { graph, graphRef, currentLayer := some firstLayer }
  let _ ← (layerNodes (realNodes.map (·.2))).run state
  let layers := (← getGraph graph).layers
  let nonEmpty ← layers.filterM fun l => do return !(← getLayer l).nodes.isEmpty
  modifyGraph graph fun g => { g with layerlessNodes := #[], layers := nonEmpty }
  for h : index in [0:nonEmpty.size] do
    modifyLayer nonEmpty[index] fun l => { l with id := index }
  monitor.done

/-- The `DepthFirstModelOrderLayerer` phase. -/
def phase : LayeredPhase :=
  { name := "DepthFirstModelOrderLayerer"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure (some BASELINE_PROCESSING_CONFIGURATION) }

end DepthFirstModelOrderLayerer

end Elk.Alg.Layered.P2Layers
