import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
/-!
# `org.eclipse.elk.alg.layered.p2layers.CoffmanGrahamLayerer` (elk-rs `coffman_graham_layerer.rs`)

The Coffman–Graham layering: the graph is transitively reduced, a topological numbering is
computed with the Coffman–Graham priority (lexicographic comparison of the reversed lists of
predecessor numbers), and the nodes are assigned to layers of at most
`LAYERING_COFFMAN_GRAHAM_LAYER_BOUND` nodes starting from the sinks.

`LNode.id` is set to the index in the layerless node list and `LEdge.id` to a running index over
the nodes' `getOutgoingEdges()`; both are used as array indices (Rust `id as usize`, guarded
with `< len` where Rust guards). The priority queues of Java are the Rust `pop_best_by`: the
first element that is strictly smaller than all earlier ones is taken and removed with
`swap_remove`. The transitive reduction DFS is the Rust recursion run with an explicit stack.

Deviation from Java (following Rust): `compareNodesInTopo` compares the predecessor numbers by
value and falls back to the node ids whenever the common suffix is equal (Java compares boxed
`Integer`s by identity and returns `1` when both lists were non-empty).

Like Rust and Java the transitive reduction does not terminate on self-loops (the DFS revisits
the unfinished node); self-loops are hidden by the `SelfLoopPreprocessor` before this phase runs.
-/
namespace Elk.Alg.Layered.P2Layers

open Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Alg
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace CoffmanGrahamLayerer

/-- `BASELINE_PROCESSING_CONFIGURATION`. -/
def BASELINE_PROCESSING_CONFIGURATION : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p1CycleBreaking .edgeAndLayerConstraintEdgeReverser
    |>.addBefore .p2Layering .layerConstraintPreprocessor
    |>.addBefore .p3NodeOrdering .layerConstraintPostprocessor

/-- Rust `id as usize` for an `i32` id: negative ids wrap to huge (out of range) indices. -/
private def usize (i : Int) : Nat := (i % 18446744073709551616).toNat

/-- Rust `node_id(node)`. -/
private def nodeId (a : LGraphArena) (n : LNodeId) : Nat := usize (a.node n).id

/-- Rust `edge_id(edge)`. -/
private def edgeId (a : LGraphArena) (e : LEdgeId) : Nat := usize (a.edge e).id

/-- The node owning the source port of `e`. -/
private def edgeSourceNode (a : LGraphArena) (e : LEdgeId) : Option LNodeId :=
  (a.edge e).source.bind fun p => (a.port p).owner

/-- The node owning the target port of `e`. -/
private def edgeTargetNode (a : LGraphArena) (e : LEdgeId) : Option LNodeId :=
  (a.edge e).target.bind fun p => (a.port p).owner

/-- Rust `pop_best_by`: removes and returns the first minimum of `items` under `lt`
(`swap_remove`, so the last element takes its place). -/
def popBestBy {α : Type} [Inhabited α] (items : Array α) (lt : α → α → Bool) : Option (α × Array α) :=
  if items.isEmpty then none
  else Id.run do
    let mut best := 0
    for index in [1:items.size] do
      if lt items[index]! items[best]! then best := index
    let result := items[best]!
    let last := items.back!
    return some (result, (items.set! best last).pop)

/-- `dfs(start, node)` of the transitive reduction: marks every edge `start → w` for which `w`
is also reachable through a longer path. Iterative version of the Rust recursion (a node is
marked when all its successors are done). -/
def dfs (a : LGraphArena) (start node : LNodeId) (nodeMark edgeMark : Array Bool) :
    Array Bool × Array Bool := Id.run do
  let mut nodeMark := nodeMark
  let mut edgeMark := edgeMark
  if nodeMark.getD (nodeId a node) false then
    return (nodeMark, edgeMark)
  -- frames: (node, its outgoing edges, index of the next edge)
  let mut stack : Array (LNodeId × Array LEdgeId × Nat) := #[(node, a.nodeOutgoingEdges node, 0)]
  while !stack.isEmpty do
    let (v, outgoing, k) := stack.back!
    if h : k < outgoing.size then
      stack := stack.set! (stack.size - 1) (v, outgoing, k + 1)
      let some target := edgeTargetNode a outgoing[k] | continue
      for transitive in a.nodeIncomingEdges target do
        if edgeSourceNode a transitive == some start then
          let ei := edgeId a transitive
          if ei < edgeMark.size then edgeMark := edgeMark.set! ei true
      if !nodeMark.getD (nodeId a target) false then
        stack := stack.push (target, a.nodeOutgoingEdges target, 0)
    else
      stack := stack.pop
      let vi := nodeId a v
      if vi < nodeMark.size then nodeMark := nodeMark.set! vi true
  return (nodeMark, edgeMark)

/-- `transitiveReduction(graph)`: the edge marks of all transitive edges. -/
def transitiveReduction (a : LGraphArena) (nodes : Array LNodeId) (nodeCount edgeCount : Nat) : Array Bool := Id.run do
  let mut edgeMark := Array.replicate edgeCount false
  for start in nodes do
    let mut nodeMark := Array.replicate nodeCount false
    for edge in a.nodeOutgoingEdges start do
      if let some target := edgeTargetNode a edge then
        let (nodeMark', edgeMark') := dfs a start target nodeMark edgeMark
        nodeMark := nodeMark'
        edgeMark := edgeMark'
  return edgeMark

/-- `compareNodesInTopo(u, v)` (Rust semantics): the node whose largest differing predecessor
number is smaller comes first; ties are broken by the node ids. -/
def compareNodesInTopo (inTopo : Array (Array Int)) (uid vid : Nat) : Ordering := Id.run do
  let inListU := inTopo.getD uid #[]
  let inListV := inTopo.getD vid #[]
  let mut i := inListU.size
  let mut j := inListV.size
  while i > 0 && j > 0 do
    let iu := inListU[i - 1]!
    let iv := inListV[j - 1]!
    if iu != iv then
      return compare iu iv
    i := i - 1
    j := j - 1
  return compare uid vid

/-- The topological numbering (`topoOrd`) of step #2 and the initial out-degrees and sinks of
step #3, computed on the reduced graph. -/
def topologicalNumbering (a : LGraphArena) (nodes : Array LNodeId) (edgeMark : Array Bool) :
    Array Int × Array Int × Array LNodeId := Id.run do
  let nodeCount := nodes.size
  let marked (e : LEdgeId) : Option Bool := edgeMark[edgeId a e]?
  let mut inDeg : Array Int := Array.replicate nodeCount 0
  let mut outDeg : Array Int := Array.replicate nodeCount 0
  let mut topoOrd : Array Int := Array.replicate nodeCount 0
  let mut inTopo : Array (Array Int) := Array.replicate nodeCount #[]
  let mut sources : Array LNodeId := #[]
  for node in nodes do
    let ni := nodeId a node
    for edge in a.nodeIncomingEdges node do
      if marked edge == some false then inDeg := inDeg.modify ni (· + 1)
    if inDeg.getD ni 0 == 0 then sources := sources.push node
  let mut topoIndex : Int := 0
  while true do
    let some (node, rest) := popBestBy sources
        (fun x y => compareNodesInTopo inTopo (nodeId a x) (nodeId a y) == .lt) | break
    sources := rest
    let ni := nodeId a node
    topoOrd := topoOrd.set! ni topoIndex
    topoIndex := topoIndex + 1
    for edge in a.nodeOutgoingEdges node do
      if marked edge == some true then continue
      let some target := edgeTargetNode a edge | continue
      let ti := nodeId a target
      inDeg := inDeg.modify ti (· - 1)
      inTopo := inTopo.modify ti (·.push (topoOrd.getD ni 0))
      if inDeg[ti]? == some 0 then sources := sources.push target
  let mut sinks : Array LNodeId := #[]
  for node in nodes do
    let ni := nodeId a node
    for edge in a.nodeOutgoingEdges node do
      if marked edge == some false then outDeg := outDeg.modify ni (· + 1)
    if outDeg.getD ni 0 == 0 then sinks := sinks.push node
  return (topoOrd, outDeg, sinks)

/-- `isLayerFull(layer, bound)`. -/
def isLayerFull (layer : LayerId) (bound : Int) : LayeredM Bool := do
  return (← getLayer layer).nodes.size >= bound.toNat

/-- `canAdd(node, layer)`: no outgoing edge of `node` ends in `layer`. -/
def canAdd (node : LNodeId) (layer : LayerId) : LayeredM Bool := withArena fun a =>
  (a.nodeOutgoingEdges node).all fun e =>
    ((edgeTargetNode a e).bind fun t => (a.node t).layer) != some layer

/-- `process(graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Coffman-Graham Layering" 1.0
  let nodes := (← getGraph graph).layerlessNodes
  if nodes.isEmpty then
    monitor.done
    return
  let graphRef := (← nodeGraph nodes[0]!).getD graph
  let bound ← getGraphPropD graph LayeredOptions.LAYERING_COFFMAN_GRAHAM_LAYER_BOUND 2147483647
  -- initialization, assign indexes
  let mut edgeIndex : Nat := 0
  for h : index in [0:nodes.size] do
    let node := nodes[index]
    modifyNode node fun x => { x with id := index }
    for edge in ← withArena (·.nodeOutgoingEdges node) do
      let id : Int := edgeIndex
      modifyEdge edge fun x => { x with id := id }
      edgeIndex := edgeIndex + 1
  -- #1 remove transitive edges, #2 compute topological ordering
  let edgeMark ← withArena (transitiveReduction · nodes nodes.size edgeIndex)
  let (topoOrd, outDeg, sinks) ← withArena (topologicalNumbering · nodes edgeMark)
  let mut outDeg := outDeg
  let mut sinks := sinks
  -- #3 actual layer assignment, starting with the sinks
  let mut layers : Array LayerId := #[]
  let mut currentLayer ← createLayer graphRef
  layers := layers.push currentLayer
  while true do
    let ids ← sinks.mapM fun n => do return usize (← getNode n).id
    let keyed := sinks.zip ids
    let some ((node, _), rest) := popBestBy keyed
        (fun (_, x) (_, y) => compare (topoOrd.getD y 0) (topoOrd.getD x 0) == .lt) | break
    sinks := rest.map (·.1)
    if (← isLayerFull currentLayer bound) || !(← canAdd node currentLayer) then
      currentLayer ← createLayer graphRef
      layers := layers.push currentLayer
    setNodeLayer node (some currentLayer)
    for edge in ← withArena (·.nodeIncomingEdges node) do
      let ei := usize (← getEdge edge).id
      if edgeMark[ei]? == some true then continue
      let some source ← withArena (edgeSourceNode · edge) | continue
      let si := usize (← getNode source).id
      outDeg := outDeg.modify si (· - 1)
      if outDeg[si]? == some 0 then sinks := sinks.push source
  -- the layers were created in inverse order
  modifyGraph graph fun g => { g with layers := g.layers ++ layers.reverse, layerlessNodes := #[] }
  monitor.done

/-- The `CoffmanGrahamLayerer` phase. -/
def phase : LayeredPhase :=
  { name := "CoffmanGrahamLayerer"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure (some BASELINE_PROCESSING_CONFIGURATION) }

end CoffmanGrahamLayerer

end Elk.Alg.Layered.P2Layers
