import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
/-!
# `org.eclipse.elk.alg.layered.p2layers.LongestPathSourceLayerer` (elk-rs `longest_path_source_layerer.rs`)

Works the same as `LongestPathLayerer` but builds a trivial layering beginning with the sources
and not the sinks: a node's height is the longest path to a source, new layers are appended and
a node of height `h` goes to layer `h - 1`.

`LNode.id` is set to the index in the layerless node list and used as index of the node heights
(Rust `id as usize`). `visit` is the Rust recursion run with an explicit stack: per node the
sources of the incoming edges of each port (self-loops skipped) are visited in order, and the
node is put into its layer in post-order.
-/
namespace Elk.Alg.Layered.P2Layers

open Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Alg
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace LongestPathSourceLayerer

/-- `BASELINE_PROCESSING_CONFIGURATION`. -/
def BASELINE_PROCESSING_CONFIGURATION : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p1CycleBreaking .edgeAndLayerConstraintEdgeReverser
    |>.addBefore .p2Layering .layerConstraintPreprocessor
    |>.addBefore .p3NodeOrdering .layerConstraintPostprocessor

/-- Rust `id as usize` for an `i32` id: negative ids wrap to huge (out of range) indices. -/
private def usize (i : Int) : Nat := (i % 18446744073709551616).toNat

/-- A pending `visit(node)` call: the opposite nodes still to visit and the running maximum. -/
private structure Frame where
  node : LNodeId
  next : Array LNodeId
  idx : Nat := 0
  maxHeight : Int := 1
  deriving Inhabited

/-- The sources of the incoming edges of `node`, per port, without self-loops. -/
private def nextNodes (node : LNodeId) : LayeredM (Array LNodeId) := withArena fun a => Id.run do
  let mut result : Array LNodeId := #[]
  for p in (a.node node).ports do
    for e in (a.port p).incomingEdges do
      if let some source := (a.edge e).source.bind fun q => (a.port q).owner then
        if source != node then result := result.push source
  return result

/-- `nodeHeights[node.id]` when it is in range and already computed (`>= 0`). -/
private def knownHeight (heights : Array Int) (node : LNodeId) : LayeredM (Option Int) := do
  let index := usize (← getNode node).id
  match heights[index]? with
  | some h => return if h >= 0 then some h else none
  | none => return none

/-- `putNode(node, height)`: appends layers until there are `height` layers and puts the node
into layer `height - 1`. -/
def putNode (graph graphRef : LGraphId) (node : LNodeId) (height : Int) (heights : Array Int) :
    LayeredM (Array Int) := do
  let height := (max height 1).toNat
  let currentLayers := (← getGraph graph).layers.size
  for _ in [currentLayers:height] do
    let layer ← createLayer graphRef
    modifyGraph graph fun g => { g with layers := g.layers.push layer }
  if let some layer := (← getGraph graph).layers[height - 1]? then
    setNodeLayer node (some layer)
  let index := usize (← getNode node).id
  return if index < heights.size then heights.set! index height else heights

/-- `visit(node)`: the height of `node` (longest path to a source), computing and placing all
not yet visited nodes reachable backwards from it. -/
def visit (graph graphRef : LGraphId) (start : LNodeId) (heights : Array Int) : LayeredM (Int × Array Int) := do
  let mut heights := heights
  if let some h ← knownHeight heights start then
    return (h, heights)
  let mut stack : Array Frame := #[{ node := start, next := ← nextNodes start }]
  let mut result : Int := 1
  while !stack.isEmpty do
    let top := stack.back!
    if h : top.idx < top.next.size then
      let other := top.next[top.idx]
      match ← knownHeight heights other with
      | some otherHeight =>
        stack := stack.set! (stack.size - 1)
          { top with idx := top.idx + 1, maxHeight := max top.maxHeight (otherHeight + 1) }
      | none =>
        stack := stack.push { node := other, next := ← nextNodes other }
    else
      stack := stack.pop
      heights ← putNode graph graphRef top.node top.maxHeight heights
      result := top.maxHeight
      if !stack.isEmpty then
        let parent := stack.back!
        stack := stack.set! (stack.size - 1)
          { parent with idx := parent.idx + 1, maxHeight := max parent.maxHeight (top.maxHeight + 1) }
  return (result, heights)

/-- `process(graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Longest path to source layering" 1.0
  let nodes := (← getGraph graph).layerlessNodes
  if nodes.isEmpty then
    monitor.done
    return
  let graphRef := (← nodeGraph nodes[0]!).getD graph
  let mut heights : Array Int := Array.replicate nodes.size (-1)
  for h : index in [0:nodes.size] do
    modifyNode nodes[index] fun x => { x with id := index }
  for node in nodes do
    let (_, heights') ← visit graph graphRef node heights
    heights := heights'
  modifyGraph graph fun g => { g with layerlessNodes := #[] }
  monitor.done

/-- The `LongestPathSourceLayerer` phase. -/
def phase : LayeredPhase :=
  { name := "LongestPathSourceLayerer"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure (some BASELINE_PROCESSING_CONFIGURATION) }

end LongestPathSourceLayerer

end Elk.Alg.Layered.P2Layers
