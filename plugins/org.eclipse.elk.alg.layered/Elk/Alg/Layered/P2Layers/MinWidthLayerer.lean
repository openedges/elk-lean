import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.p2layers.MinWidthLayerer` (elk-rs `min_width_layerer.rs`)

The MinWidth layering heuristic of Nikolov, Tarassov and Branke ("In search for efficient
heuristics for minimum-width graph layering with consideration of dummy nodes", 2005): layers
are filled from the sinks upwards while an estimate of the layer width stays below
`UBW * avgSize`, for all combinations of the upper bound on width (`UBW`) and the compensator
`c` (ranges `1..4` / `1..2` when the options are negative); the layering with the smallest
width (then the fewest layers) is kept.

`LNode.id` is set to the index in the layerless node list and used as array index; the
successor sets hold the (`usize`) ids of the target nodes. The nodes are processed in the
stable descending order of their out-degree (Java `Collections.reverseOrder` on a stable sort).
-/
namespace Elk.Alg.Layered.P2Layers

open Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Alg
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace MinWidthLayerer

/-- `UPPERBOUND_ON_WIDTH_RANGE`. -/
def UPPERBOUND_ON_WIDTH_RANGE : Int × Int := (1, 4)

/-- `COMPENSATOR_RANGE`. -/
def COMPENSATOR_RANGE : Int × Int := (1, 2)

/-- `getLayoutProcessorConfiguration(graph)`. -/
def processorConfiguration : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p1CycleBreaking .edgeAndLayerConstraintEdgeReverser
    |>.addBefore .p2Layering .layerConstraintPreprocessor
    |>.addBefore .p3NodeOrdering .layerConstraintPostprocessor

/-- Rust `id as usize` for an `i32` id: negative ids wrap to huge (out of range) indices. -/
private def usize (i : Int) : Nat := (i % 18446744073709551616).toNat

/-- Per-run data of the heuristic (the Rust struct fields), indexed by `LNode.id`. -/
structure Data where
  dummySize : Float
  normSize : Array Float
  avgSize : Float
  inDegree : Array Int
  outDegree : Array Int
  deriving Inhabited

/-- `countEdgesExceptSelfLoops(edges)`. -/
def countEdgesExceptSelfLoops (a : LGraphArena) (edges : Array LEdgeId) : Int :=
  (edges.filter fun e => !a.edgeIsSelfLoop e).size

/-- `precalcSuccessors(nodes)`: per node the ids of the targets of its non-self-loop outgoing
edges (a set: only membership is used). -/
def precalcSuccessors (a : LGraphArena) (nodes : Array LNodeId) : Array (Array Nat) :=
  nodes.map fun node => Id.run do
    let mut outNodes : Array Nat := #[]
    for edge in a.nodeOutgoingEdges node do
      if a.edgeIsSelfLoop edge then continue
      if let some target := (a.edge edge).target.bind fun p => (a.port p).owner then
        let id := usize (a.node target).id
        if !outNodes.contains id then outNodes := outNodes.push id
    return outNodes

/-- `selectNode(nodes, successors, targets)`: the index of the first node all of whose
successors are already placed in other layers. -/
def selectNode (nodes : Array (LNodeId × Nat)) (successors : Array (Array Nat)) (targets : Std.HashSet Nat) : Option Nat :=
  nodes.findIdx? fun (_, nodeIndex) =>
    match successors[nodeIndex]? with
    | some succ => succ.all targets.contains
    | none => false

/-- `computeMinWidthLayering(upperBoundOnWidth, compensator, nodes, nodeSuccessors)`: the
estimated width and the layers (sinks first) of one parameter combination. `nodes` pairs each
node with its id. -/
def computeMinWidthLayering (d : Data) (upperBoundOnWidth compensator : Int) (nodes : Array (LNodeId × Nat))
    (nodeSuccessors : Array (Array Nat)) : Float × Array (Array LNodeId) := Id.run do
  let mut layers : Array (Array LNodeId) := #[]
  let mut unplacedNodes := nodes
  let ubwConsiderSize := Float.ofInt upperBoundOnWidth * d.avgSize
  let mut outDeg : Int := 0
  let mut alreadyPlacedInCurrentLayer : Array Nat := #[]
  let mut alreadyPlacedInOtherLayers : Std.HashSet Nat := {}
  let mut currentLayer : Array LNodeId := #[]
  let mut widthCurrent := 0.0
  let mut widthUp := 0.0
  let mut maxWidth := 0.0
  let mut realWidth := 0.0
  let mut currentSpanningEdges := 0.0
  let mut goingOutFromThisLayer := 0.0
  while !unplacedNodes.isEmpty do
    let selectedIndex := selectNode unplacedNodes nodeSuccessors alreadyPlacedInOtherLayers
    let selectedNode := selectedIndex.map fun index => unplacedNodes[index]!
    if let some index := selectedIndex then
      unplacedNodes := unplacedNodes.eraseIdx! index
    if let some (currentNode, nodeIndex) := selectedNode then
      currentLayer := currentLayer.push currentNode
      alreadyPlacedInCurrentLayer := alreadyPlacedInCurrentLayer.push nodeIndex
      outDeg := d.outDegree.getD nodeIndex 0
      widthCurrent := widthCurrent + (d.normSize.getD nodeIndex 0.0 - Float.ofInt outDeg * d.dummySize)
      let inDeg := d.inDegree.getD nodeIndex 0
      widthUp := widthUp + Float.ofInt inDeg * d.dummySize
      goingOutFromThisLayer := goingOutFromThisLayer + Float.ofInt outDeg * d.dummySize
      realWidth := realWidth + d.normSize.getD nodeIndex 0.0
    let shouldGoUp : Bool := match selectedNode with
      | some (_, nodeIndex) =>
        if unplacedNodes.isEmpty then true
        else
          (widthCurrent >= ubwConsiderSize && d.normSize.getD nodeIndex 0.0 > Float.ofInt outDeg * d.dummySize)
            || widthUp >= Float.ofInt compensator * ubwConsiderSize
      | none => true
    if shouldGoUp then
      layers := layers.push currentLayer
      currentLayer := #[]
      for i in alreadyPlacedInCurrentLayer do
        alreadyPlacedInOtherLayers := alreadyPlacedInOtherLayers.insert i
      alreadyPlacedInCurrentLayer := #[]
      currentSpanningEdges := currentSpanningEdges - goingOutFromThisLayer
      maxWidth := fmax maxWidth (currentSpanningEdges * d.dummySize + realWidth)
      currentSpanningEdges := currentSpanningEdges + widthUp
      widthCurrent := widthUp
      widthUp := 0.0
      goingOutFromThisLayer := 0.0
      realWidth := 0.0
  return (maxWidth, layers)

/-- `process(graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "MinWidth layering" 1.0
  let notInserted := (← getGraph graph).layerlessNodes
  if notInserted.isEmpty then
    monitor.done
    return
  let upperBoundOnWidth ← getGraphPropD graph LayeredOptions.LAYERING_MIN_WIDTH_UPPER_BOUND_ON_WIDTH 4
  let compensator ← getGraphPropD graph LayeredOptions.LAYERING_MIN_WIDTH_UPPER_LAYER_ESTIMATION_SCALING_FACTOR 2
  let mut dummySize ← getGraphPropD graph LayeredOptions.SPACING_EDGE_EDGE 0.0
  let mut minimumNodeSize := Float.posInf
  for node in notInserted do
    let nd ← getNode node
    if nd.type != .normal then continue
    minimumNodeSize := fmin minimumNodeSize nd.size.y
  minimumNodeSize := fmax minimumNodeSize 1.0
  let numNodes := notInserted.size
  let mut inDegree : Array Int := Array.replicate numNodes 0
  let mut outDegree : Array Int := Array.replicate numNodes 0
  let mut normSize : Array Float := Array.replicate numNodes 0.0
  let mut avgSize := 0.0
  for h : index in [0:notInserted.size] do
    let node := notInserted[index]
    modifyNode node fun x => { x with id := index }
    let inDeg ← withArena fun a => countEdgesExceptSelfLoops a (a.nodeIncomingEdges node)
    let outDeg ← withArena fun a => countEdgesExceptSelfLoops a (a.nodeOutgoingEdges node)
    inDegree := inDegree.set! index inDeg
    outDegree := outDegree.set! index outDeg
    let size := (← getNode node).size.y
    normSize := normSize.set! index (size / minimumNodeSize)
    avgSize := avgSize + normSize[index]!
  dummySize := dummySize / minimumNodeSize
  avgSize := avgSize / numNodes.toFloat
  let nodeSuccessors ← withArena (precalcSuccessors · notInserted)
  -- stable sort by descending out-degree (ties keep the input order)
  let indexed : Array (LNodeId × Nat) := notInserted.mapIdx fun i n => (n, i)
  let sorted := stableSort indexed fun (_, x) (_, y) => compare (outDegree.getD y 0) (outDegree.getD x 0)
  let d : Data := { dummySize, normSize, avgSize, inDegree, outDegree }
  let mut minWidth := Float.posInf
  let mut minNumLayers : Int := 2147483647
  let mut candidateLayering : Option (Array (Array LNodeId)) := none
  let mut ubwStart := upperBoundOnWidth
  let mut ubwEnd := upperBoundOnWidth
  let mut cStart := compensator
  let mut cEnd := compensator
  if upperBoundOnWidth < 0 then
    ubwStart := UPPERBOUND_ON_WIDTH_RANGE.1
    ubwEnd := UPPERBOUND_ON_WIDTH_RANGE.2
  if compensator < 0 then
    cStart := COMPENSATOR_RANGE.1
    cEnd := COMPENSATOR_RANGE.2
  let mut ubw := ubwStart
  while ubw <= ubwEnd do
    let mut c := cStart
    while c <= cEnd do
      let (newWidth, layering) := computeMinWidthLayering d ubw c sorted nodeSuccessors
      let newNumLayers : Int := layering.size
      if newWidth < minWidth || (newWidth == minWidth && newNumLayers < minNumLayers) then
        minWidth := newWidth
        minNumLayers := newNumLayers
        candidateLayering := some layering
      c := c + 1
    ubw := ubw + 1
  let graphRef := (← nodeGraph (sorted[0]!).1).getD graph
  if let some layering := candidateLayering then
    for layerList in layering do
      let currentLayer ← createLayer graphRef
      for node in layerList do
        setNodeLayer node (some currentLayer)
      modifyGraph graph fun g => { g with layers := g.layers.push currentLayer }
  modifyGraph graph fun g => { g with layers := g.layers.reverse, layerlessNodes := #[] }
  monitor.done

/-- The `MinWidthLayerer` phase. -/
def phase : LayeredPhase :=
  { name := "MinWidthLayerer"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure (some processorConfiguration) }

end MinWidthLayerer

end Elk.Alg.Layered.P2Layers
