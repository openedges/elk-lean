import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Std.Data.HashSet
/-!
# `org.eclipse.elk.alg.layered.p2layers.LongestPathLayerer` (elk-rs `longest_path_layerer.rs`)

The most basic layering algorithm, which assigns layers according to the longest path to a sink.
Precondition: the graph has no cycles. Postcondition: all nodes have been assigned a layer such
that edges connect only nodes from layers with increasing indices.

`LNode.id` is set to the index in the layerless node list and used as index of the node heights
(Rust `node_index`: `id as usize`, so negative ids are out of range). `visit` is the Rust
recursion run with an explicit stack: per node the targets of the outgoing edges of each port
(self-loops skipped) are visited in order, and the node is put into its layer when all its
targets are done (post-order, which is the order new layers are inserted at the front).
-/
namespace Elk.Alg.Layered.P2Layers

open Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Alg
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace LongestPathLayerer

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

/-- The targets of the outgoing edges of `node`, per port, without self-loops. -/
private def nextNodes (node : LNodeId) : LayeredM (Array LNodeId) := withArena fun a => Id.run do
  let mut result : Array LNodeId := #[]
  for p in (a.node node).ports do
    for e in (a.port p).outgoingEdges do
      if let some target := (a.edge e).target.bind fun q => (a.port q).owner then
        if target != node then result := result.push target
  return result

/-- `nodeHeights[node.id]` when it is in range and already computed (`>= 0`). -/
private def knownHeight (heights : Array Int) (node : LNodeId) : LayeredM (Option Int) := do
  let index := usize (← getNode node).id
  match heights[index]? with
  | some h => return if h >= 0 then some h else none
  | none => return none

/-- `putNode(node, height)`: adds layers at the front until there are `height` layers and puts
the node into layer `layers.size - height`. -/
def putNode (graph graphRef : LGraphId) (node : LNodeId) (height : Int) (heights : Array Int) :
    LayeredM (Array Int) := do
  let height := (max height 1).toNat
  let currentLayers := (← getGraph graph).layers.size
  for _ in [currentLayers:height] do
    let layer ← createLayer graphRef
    modifyGraph graph fun g => { g with layers := #[layer] ++ g.layers }
  let layers := (← getGraph graph).layers
  if let some layer := layers[layers.size - height]? then
    setNodeLayer node (some layer)
  let index := usize (← getNode node).id
  return if index < heights.size then heights.set! index height else heights

/-- `visit(node)`: the height of `node` (longest path to a sink), computing and placing all
not yet visited nodes reachable from it. Reaching a node whose own `visit` is still running (a
cycle the cycle breaker left, e.g. through a `noModelOrder` node of a model order cycle breaker)
makes Java's recursion repeat itself until the stack overflows: `java.lang.StackOverflowError`
(agent HMO; the explicit stack grew without bound before). -/
def visit (graph graphRef : LGraphId) (start : LNodeId) (heights : Array Int) : LayeredM (Int × Array Int) := do
  let mut heights := heights
  if let some h ← knownHeight heights start then
    return (h, heights)
  let mut stack : Array Frame := #[{ node := start, next := ← nextNodes start }]
  let mut onStack : Std.HashSet LNodeId := ({} : Std.HashSet LNodeId).insert start
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
        if onStack.contains other then throw (IO.userError "java.lang.StackOverflowError")
        onStack := onStack.insert other
        stack := stack.push { node := other, next := ← nextNodes other }
    else
      stack := stack.pop
      onStack := onStack.erase top.node
      heights ← putNode graph graphRef top.node top.maxHeight heights
      result := top.maxHeight
      if !stack.isEmpty then
        let parent := stack.back!
        stack := stack.set! (stack.size - 1)
          { parent with idx := parent.idx + 1, maxHeight := max parent.maxHeight (top.maxHeight + 1) }
  return (result, heights)

/-- `process(graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Longest path layering" 1.0
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

/-- The `LongestPathLayerer` phase. -/
def phase : LayeredPhase :=
  { name := "LongestPathLayerer"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure (some BASELINE_PROCESSING_CONFIGURATION) }

end LongestPathLayerer

end Elk.Alg.Layered.P2Layers
