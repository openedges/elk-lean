import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.p2layers.StretchWidthLayerer` (elk-rs `stretch_width_layerer.rs`)

The StretchWidth layering heuristic of Philipp Döhring ("Algorithmen zur Layerzuweisung", 2014):
nodes whose successors are all placed are put into the current layer (sinks first) until the
estimated width exceeds `maxWidth` (the normalized size of the largest node) or the estimated
width of the next layer exceeds `maxWidth * averageOutDegree * dummySize`; if a single node does
not fit into an empty layer the whole layering restarts with `maxWidth + 1`.

The nodes are sorted by descending rank (`getRank`: the maximum out-degree of the node and its
predecessors; stable). `LNode.id` first holds the rank and is then set to the index in the
sorted list, which indexes all arrays.

Deviations: the successor sets (`computeSuccessors`) are never read by Rust or Java and are not
built (only the id assignment is kept); the average out-degree is computed in `f64` like Rust
(Java uses `float`). After a restart Rust drops the cleared layers (the nodes' weak layer
references die) while here the nodes keep pointing to the orphaned layers until they are placed
again; nothing reads those layers in between.

Like Rust and Java the degrees include self-loops, so a node with a self-loop never becomes
selectable and the loop does not terminate; self-loops are hidden by the `SelfLoopPreprocessor`
before this phase runs.
-/
namespace Elk.Alg.Layered.P2Layers

open Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Alg
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace StretchWidthLayerer

/-- `getLayoutProcessorConfiguration(graph)`. -/
def processorConfiguration : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p1CycleBreaking .edgeAndLayerConstraintEdgeReverser
    |>.addBefore .p2Layering .layerConstraintPreprocessor
    |>.addBefore .p3NodeOrdering .layerConstraintPostprocessor

/-- Rust `id as usize` for an `i32` id: negative ids wrap to huge (out of range) indices. -/
private def usize (i : Int) : Nat := (i % 18446744073709551616).toNat

/-- `getRank(node)`: the maximum of the out-degree of `node` and of its predecessors. -/
def getRank (a : LGraphArena) (node : LNodeId) : Int := Id.run do
  let mut maxRank : Int := (a.nodeOutgoingEdges node).size
  for edge in a.nodeIncomingEdges node do
    if let some predecessor := (a.edge edge).source.bind fun p => (a.port p).owner then
      maxRank := max maxRank (a.nodeOutgoingEdges predecessor).size
  return maxRank

/-- The fixed data of one run (Rust struct fields), indexed by the sorted index. -/
structure Data where
  dummySize : Float
  normSize : Array Float
  inDegree : Array Int
  outDegree : Array Int
  upperLayerInfluence : Float
  deriving Inhabited

/-- `conditionGoUp()` for the node with index `nodeIndex`. -/
def conditionGoUp (d : Data) (widthCurrent widthUp maxWidth : Float) (nodeIndex : Nat) : Bool :=
  let outDeg := Float.ofInt (d.outDegree.getD nodeIndex 0)
  let inDeg := Float.ofInt (d.inDegree.getD nodeIndex 0)
  let a := (widthCurrent - outDeg * d.dummySize + d.normSize.getD nodeIndex 0.0) > maxWidth
  let b := (widthUp + inDeg * d.dummySize) > (maxWidth * d.upperLayerInfluence * d.dummySize)
  a || b

/-- `updateOutGoing(currentLayer)`: every node of the layer consumes one outgoing edge of each
of its predecessors. -/
def updateOutgoing (layer : LayerId) (remaining : Array Int) : LayeredM (Array Int) := do
  let mut remaining := remaining
  for node in (← getLayer layer).nodes do
    for edge in ← withArena (·.nodeIncomingEdges node) do
      let some source ← withArena fun a => (a.edge edge).source.bind fun p => (a.port p).owner | continue
      let pos := usize (← getNode source).id
      if pos < remaining.size then
        remaining := remaining.modify pos (· - 1)
  return remaining

/-- Creates a layer and appends it to the graph. -/
private def newLayer (graph graphRef : LGraphId) : LayeredM LayerId := do
  let layer ← createLayer graphRef
  modifyGraph graph fun g => { g with layers := g.layers.push layer }
  return layer

/-- `process(graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "StretchWidth layering" 1.0
  let unsortedNodes := (← getGraph graph).layerlessNodes
  if unsortedNodes.isEmpty then
    monitor.done
    return
  let mut widthCurrent := 0.0
  let mut widthUp := 0.0
  let mut minimumNodeSize := Float.posInf
  let mut maximumNodeSize := Float.negInf
  let mut dummySize ← getGraphPropD graph LayeredOptions.SPACING_EDGE_EDGE 0.0
  -- computeSortedNodes: rank into the id, stable sort by descending id
  for node in unsortedNodes do
    let rank ← withArena (getRank · node)
    modifyNode node fun x => { x with id := rank }
  let ranked ← unsortedNodes.mapM fun n => do return (n, (← getNode n).id)
  let sortedNodes := (stableSort ranked fun (_, x) (_, y) => compare y x).map (·.1)
  -- computeSuccessors: re-index (the successor sets themselves are unused)
  for h : index in [0:sortedNodes.size] do
    modifyNode sortedNodes[index] fun x => { x with id := index }
  -- computeDegrees
  let count := sortedNodes.size
  let mut inDegree : Array Int := Array.replicate count 0
  let mut outDegree : Array Int := Array.replicate count 0
  for node in sortedNodes do
    let nodeIndex := usize (← getNode node).id
    inDegree := inDegree.set! nodeIndex (← withArena (·.nodeIncomingEdges node)).size
    outDegree := outDegree.set! nodeIndex (← withArena (·.nodeOutgoingEdges node)).size
  -- minMaxNodeSize
  for node in sortedNodes do
    let nd ← getNode node
    if nd.type != .normal then continue
    minimumNodeSize := fmin minimumNodeSize nd.size.y
    maximumNodeSize := fmax maximumNodeSize nd.size.y
  -- computeNormalizedSize (with the not yet clamped minimum, like Rust and Java)
  let mut normSize : Array Float := Array.replicate count 0.0
  for node in sortedNodes do
    let nd ← getNode node
    normSize := normSize.set! (usize nd.id) (nd.size.y / minimumNodeSize)
  minimumNodeSize := fmax minimumNodeSize 1.0
  maximumNodeSize := fmax maximumNodeSize 1.0
  dummySize := dummySize / minimumNodeSize
  let mut maxWidth := maximumNodeSize / minimumNodeSize
  -- getAverageOutDegree over the (still filled) layerless nodes
  let mut totalOut := 0.0
  for node in unsortedNodes do
    totalOut := totalOut + (← withArena (·.nodeOutgoingEdges node)).size.toFloat
  let upperLayerInfluence := totalOut / unsortedNodes.size.toFloat
  let d : Data := { dummySize, normSize, inDegree, outDegree, upperLayerInfluence }
  let graphRef := (← nodeGraph sortedNodes[0]!).getD graph
  let mut currentLayer ← newLayer graph graphRef
  let mut tempLayerlessNodes := sortedNodes
  let mut remainingOutgoing := outDegree
  let mut alreadyPlacedNodes : Nat := 0
  while !tempLayerlessNodes.isEmpty do
    -- selectNode(): the first node all of whose outgoing edges are consumed
    let mut selectedNode : Option (LNodeId × Nat) := none
    for node in tempLayerlessNodes do
      let nodeIndex := usize (← getNode node).id
      if remainingOutgoing.getD nodeIndex 0 <= 0 then
        selectedNode := some (node, nodeIndex)
        break
    let goUp : Bool := match selectedNode with
      | some (_, nodeIndex) => conditionGoUp d widthCurrent widthUp maxWidth nodeIndex && alreadyPlacedNodes != 0
      | none => true
    if goUp then
      remainingOutgoing ← updateOutgoing currentLayer remainingOutgoing
      currentLayer ← newLayer graph graphRef
      alreadyPlacedNodes := 0
      widthCurrent := widthUp
      widthUp := 0.0
    else if let some (node, nodeIndex) := selectedNode then
      if conditionGoUp d widthCurrent widthUp maxWidth nodeIndex then
        -- the node does not fit into an empty layer: restart with a larger maximal width
        modifyGraph graph fun g => { g with layers := #[] }
        currentLayer ← newLayer graph graphRef
        widthCurrent := 0.0
        widthUp := 0.0
        alreadyPlacedNodes := 0
        maxWidth := maxWidth + 1.0
        tempLayerlessNodes := sortedNodes
        remainingOutgoing := outDegree
      else
        setNodeLayer node (some currentLayer)
        if let some index := tempLayerlessNodes.findIdx? (· == node) then
          tempLayerlessNodes := tempLayerlessNodes.eraseIdx! index
        alreadyPlacedNodes := alreadyPlacedNodes + 1
        widthCurrent := widthCurrent - Float.ofInt (outDegree.getD nodeIndex 0) * dummySize + normSize.getD nodeIndex 0.0
        widthUp := widthUp + Float.ofInt (inDegree.getD nodeIndex 0) * dummySize
  modifyGraph graph fun g => { g with layerlessNodes := #[], layers := g.layers.reverse }
  monitor.done

/-- The `StretchWidthLayerer` phase. -/
def phase : LayeredPhase :=
  { name := "StretchWidthLayerer"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure (some processorConfiguration) }

end StretchWidthLayerer

end Elk.Alg.Layered.P2Layers
