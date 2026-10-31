import Std.Data.HashMap
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
with `< len` where Rust guards). The transitive reduction DFS is the Java/Rust recursion run with an
explicit stack.

Java semantics (elk-rs differs): both priority queues are `java.util.PriorityQueue` binary heaps
(`JavaPriorityQueue`: JDK 21 `siftUp`/`siftDown`), and `compareNodesInTopo` is Java's comparator —
boxed `Integer`s compared by identity (`!=`), the node ids only when a predecessor list is empty and
`1` when both lists end undecided. That comparator is not a consistent order, so which source the
heap yields first depends on its structure. elk-rs takes the first minimum of a list
(`pop_best_by` with `swap_remove`), compares the numbers by value and falls back to the ids.

The transitive reduction does not terminate on a cycle (the DFS revisits an unfinished node; a
self-loop is hidden by the `SelfLoopPreprocessor` before this phase runs, but cycles that the cycle
breaker leaves, e.g. edges between nodes of different model order groups, remain): Java's recursion
overflows the stack, so Lean reports `java.lang.StackOverflowError` when the walk reaches a node whose
call is still running (elk-rs recurses until its own stack overflows).
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

/-- `dfs(start, node)` of the transitive reduction: marks every edge `start → w` for which `w`
is also reachable through a longer path. Iterative version of the Java recursion (a node is
marked when all its successors are done). `none` when the walk reaches a node whose own call is
still running: Java's recursion (whose marks only change on return) then repeats itself until
the stack overflows (`java.lang.StackOverflowError`, agent HMO; before, the explicit stack grew
without bound). -/
def dfs (a : LGraphArena) (start node : LNodeId) (nodeMark edgeMark : Array Bool) :
    Option (Array Bool × Array Bool) := Id.run do
  let mut nodeMark := nodeMark
  let mut edgeMark := edgeMark
  if nodeMark.getD (nodeId a node) false then
    return some (nodeMark, edgeMark)
  let mut onStack := Array.replicate nodeMark.size false
  let ni := nodeId a node
  if ni < onStack.size then onStack := onStack.set! ni true
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
      let ti := nodeId a target
      if !nodeMark.getD ti false then
        if onStack.getD ti false then return none
        if ti < onStack.size then onStack := onStack.set! ti true
        stack := stack.push (target, a.nodeOutgoingEdges target, 0)
    else
      stack := stack.pop
      let vi := nodeId a v
      if vi < nodeMark.size then nodeMark := nodeMark.set! vi true
      if vi < onStack.size then onStack := onStack.set! vi false
  return some (nodeMark, edgeMark)

/-- `transitiveReduction(graph)`: the edge marks of all transitive edges (`none`: Java's
`StackOverflowError`, see `dfs`). -/
def transitiveReduction (a : LGraphArena) (nodes : Array LNodeId) (nodeCount edgeCount : Nat) :
    Option (Array Bool) := Id.run do
  let mut edgeMark := Array.replicate edgeCount false
  for start in nodes do
    let mut nodeMark := Array.replicate nodeCount false
    for edge in a.nodeOutgoingEdges start do
      if let some target := edgeTargetNode a edge then
        let some (nodeMark', edgeMark') := dfs a start target nodeMark edgeMark | return none
        nodeMark := nodeMark'
        edgeMark := edgeMark'
  return some edgeMark

/-- Java `compareNodesInTopo(u, v)` (`int` result): walks both `inTopo` lists from the end with
`ListIterator.previous()`. The elements are `Integer`s boxed by every `inTopo.put` (`!=` is identity:
equal values are the same object only inside the `Integer` cache `[-128, 127]`), so a pair of
different values decides by `Integer.compare` and a pair of equal values outside the cache gives
`Integer.compare` = `0`. When the walk ends undecided, `!itU.hasNext() && !itV.hasNext()` holds
exactly when no element was visited (one list is empty): the node ids decide; otherwise (both lists
non-empty) Java returns `1` (the `else` branch; `!itU.hasNext()` alone cannot hold there). Not a
consistent order, so the `PriorityQueue` heap structure decides (`JavaPriorityQueue`). -/
def compareNodesInTopo (inTopo : Array (Array Int)) (uid vid : Nat) : Int := Id.run do
  let inListU := inTopo.getD uid #[]
  let inListV := inTopo.getD vid #[]
  let mut i := inListU.size
  let mut j := inListV.size
  while i > 0 && j > 0 do
    let iu := inListU[i - 1]!
    let iv := inListV[j - 1]!
    if !(iu == iv && -128 <= iu && iu <= 127) then
      return if iu < iv then -1 else if iu > iv then 1 else 0
    i := i - 1
    j := j - 1
  if i == inListU.size && j == inListV.size then
    return if uid < vid then -1 else if uid > vid then 1 else 0
  return 1

/-- `java.util.PriorityQueue` with a comparator (JDK 21 `offer` → `siftUpUsingComparator`, `poll` →
`siftDownUsingComparator` of the last element from the root): the binary heap array. -/
abbrev JavaPriorityQueue (α : Type) := Array α

namespace JavaPriorityQueue

/-- `offer(x)`: `siftUp(size, x)` (stops at the first parent with `cmp(x, parent) >= 0`). -/
def offer {α : Type} [Inhabited α] (q : JavaPriorityQueue α) (cmp : α → α → Int) (x : α) : JavaPriorityQueue α :=
  Id.run do
    let mut k := q.size
    let mut es := q.push x
    while k > 0 do
      let parent := (k - 1) / 2
      let e := es[parent]!
      if cmp x e >= 0 then break
      es := es.set! k e
      k := parent
    return es.set! k x

/-- `poll()`: the root; the last element is sifted down from the root (`siftDownUsingComparator`: the
smaller child is the right one only when `cmp(left, right) > 0`, stop when `cmp(x, child) <= 0`). -/
def poll {α : Type} [Inhabited α] (q : JavaPriorityQueue α) (cmp : α → α → Int) : Option (α × JavaPriorityQueue α) :=
  if q.isEmpty then none
  else Id.run do
    let result := q[0]!
    let n := q.size - 1
    let x := q[n]!
    let mut es := q.pop
    if n > 0 then
      let half := n / 2
      let mut k := 0
      while k < half do
        let mut child := 2 * k + 1
        let mut c := es[child]!
        let right := child + 1
        if right < n && cmp c es[right]! > 0 then
          child := right
          c := es[child]!
        if cmp x c <= 0 then break
        es := es.set! k c
        k := child
      es := es.set! k x
    return some (result, es)

end JavaPriorityQueue

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
  -- `new PriorityQueue<LNode>(this::compareNodesInTopo)`; the comparator reads the current `inTopo`
  let mut sources : JavaPriorityQueue LNodeId := #[]
  for node in nodes do
    let ni := nodeId a node
    for edge in a.nodeIncomingEdges node do
      if marked edge == some false then inDeg := inDeg.modify ni (· + 1)
    if inDeg.getD ni 0 == 0 then
      let it := inTopo
      sources := sources.offer (fun x y => compareNodesInTopo it (nodeId a x) (nodeId a y)) node
  let mut topoIndex : Int := 0
  while true do
    let it := inTopo
    let some (node, rest) := sources.poll (fun x y => compareNodesInTopo it (nodeId a x) (nodeId a y)) | break
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
      if inDeg[ti]? == some 0 then
        let it := inTopo
        sources := sources.offer (fun x y => compareNodesInTopo it (nodeId a x) (nodeId a y)) target
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
  let some edgeMark ← withArena (transitiveReduction · nodes nodes.size edgeIndex)
    | throw (IO.userError "java.lang.StackOverflowError")
  let (topoOrd, outDeg, initialSinks) ← withArena (topologicalNumbering · nodes edgeMark)
  let mut outDeg := outDeg
  -- `new PriorityQueue<LNode>((n1, n2) -> -Integer.compare(topoOrd[n1.id], topoOrd[n2.id]))`: the ids
  -- do not change while the queue is used, so `topoOrd[n.id]` is looked up once per node
  let mut topoOf : Std.HashMap LNodeId Int := {}
  for node in nodes do
    topoOf := topoOf.insert node (topoOrd.getD (usize (← getNode node).id) 0)
  let topoOfNode := topoOf
  let sinkCmp : LNodeId → LNodeId → Int := fun x y =>
    let ox := topoOfNode.getD x 0
    let oy := topoOfNode.getD y 0
    if ox < oy then 1 else if ox > oy then -1 else 0
  let mut sinks : JavaPriorityQueue LNodeId := #[]
  for node in initialSinks do sinks := sinks.offer sinkCmp node
  -- #3 actual layer assignment, starting with the sinks
  let mut layers : Array LayerId := #[]
  let mut currentLayer ← createLayer graphRef
  layers := layers.push currentLayer
  while true do
    let some (node, rest) := sinks.poll sinkCmp | break
    sinks := rest
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
      if outDeg[si]? == some 0 then sinks := sinks.offer sinkCmp source
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
