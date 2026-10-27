import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.p2layers.BreadthFirstModelOrderLayerer` (elk-rs `breadth_first_model_order_layerer.rs`)

Assigns layers in model order: the real nodes are visited by ascending `MODEL_ORDER` (stable);
a node goes into the current layer unless one of its predecessors (directly or through a label
dummy) is already in it, in which case a new label dummy layer and a new current layer are
appended. Unplaced label dummies in front of the node go into the current dummy layer. Empty
layers are removed at the end and `Layer.id` is set to the layer index.

Deviation (following Rust): the missing model order is reported while collecting the real nodes
(Java only throws inside the comparator, i.e. with at least two real nodes).
-/
namespace Elk.Alg.Layered.P2Layers

open Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Alg
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace BreadthFirstModelOrderLayerer

/-- `BASELINE_PROCESSING_CONFIGURATION`. -/
def BASELINE_PROCESSING_CONFIGURATION : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p1CycleBreaking .edgeAndLayerConstraintEdgeReverser
    |>.addBefore .p2Layering .layerConstraintPreprocessor
    |>.addBefore .p3NodeOrdering .layerConstraintPostprocessor

/-- The node owning the source port of `e`. -/
private def edgeSourceNode (a : LGraphArena) (e : LEdgeId) : Option LNodeId :=
  (a.edge e).source.bind fun p => (a.port p).owner

/-- Creates a layer and appends it to the graph. -/
private def newLayer (graph graphRef : LGraphId) : LayeredM LayerId := do
  let layer ← createLayer graphRef
  modifyGraph graph fun g => { g with layers := g.layers.push layer }
  return layer

/-- Whether the source of `edge` (or, for a label dummy source, the source of the dummy's first
incoming edge) lies in `currentLayer`. -/
def isConnectedTo (edge : LEdgeId) (currentLayer : LayerId) : LayeredM Bool := withArena fun a =>
  match edgeSourceNode a edge with
  | none => false
  | some sourceNode =>
    let source := a.node sourceNode
    if source.type == .normal then
      source.layer == some currentLayer
    else if source.type == .label then
      match (a.nodeIncomingEdges sourceNode)[0]? with
      | some labelEdge => ((edgeSourceNode a labelEdge).bind fun n => (a.node n).layer) == some currentLayer
      | none => false
    else false

/-- `process(graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Breadth first model order layering" 1.0
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
        | throwUnsupportedGraph "The BF model order layer assigner requires all real nodes to have a model order."
      realNodes := realNodes.push (order, node)
  realNodes := stableSort realNodes fun (x, _) (y, _) => compare x y
  let mut currentLayer ← newLayer graph graphRef
  let mut currentDummyLayer : Option LayerId := none
  let mut firstNode := true
  for (_, node) in realNodes do
    if firstNode then
      setNodeLayer node (some currentLayer)
      firstNode := false
      continue
    let incomingEdges ← withArena (·.nodeIncomingEdges node)
    for edge in incomingEdges do
      if ← isConnectedTo edge currentLayer then
        let dummyLayer ← newLayer graph graphRef
        currentDummyLayer := some dummyLayer
        currentLayer ← newLayer graph graphRef
    for edge in incomingEdges do
      let some sourceNode ← withArena (edgeSourceNode · edge) | continue
      let source ← getNode sourceNode
      if source.type == .label && source.layer.isNone then
        let some dummyLayer := currentDummyLayer
          | throwIllegalState "dummy layer missing for label dummy placement"
        setNodeLayer sourceNode (some dummyLayer)
    setNodeLayer node (some currentLayer)
  let layers := (← getGraph graph).layers
  let nonEmpty ← layers.filterM fun l => do return !(← getLayer l).nodes.isEmpty
  modifyGraph graph fun g => { g with layerlessNodes := #[], layers := nonEmpty }
  for h : index in [0:nonEmpty.size] do
    modifyLayer nonEmpty[index] fun l => { l with id := index }
  monitor.done

/-- The `BreadthFirstModelOrderLayerer` phase. -/
def phase : LayeredPhase :=
  { name := "BreadthFirstModelOrderLayerer"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure (some BASELINE_PROCESSING_CONFIGURATION) }

end BreadthFirstModelOrderLayerer

end Elk.Alg.Layered.P2Layers
