import Elk.Alg.Common.NetworkSimplex.NGraph
import Elk.Core.Util.ProgressMonitor
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.common.networksimplex.NetworkSimplex` (elk-rs `network_simplex.rs`)

Determines an optimal layering of all nodes of an `NGraph` concerning a minimal
(weighted) length of all edges using the network simplex algorithm of

* Emden R. Gansner, Eleftherios Koutsofios, Stephen C. North, Kiem-Phong Vo,
  A technique for drawing directed graphs. *Software Engineering* 19(3),
  pp. 214-230, 1993.

Precondition: the graph has no cycles. Postcondition: all nodes have been
assigned a layer (`NNode.layer`) such that edges connect only nodes from layers
with increasing indices.

This is a 1:1 port of the elk-rs implementation (the parity oracle), which
replaces the Java object traversal by dense "structure of arrays" caches indexed
by the internal ids (`eSrcId`, `eTgtId`, `nodeEdges`, `treeEdges`, `nLayer`, …),
an iterative post-order traversal, an XOR-summary leaf elimination for the cut
values, and — when all weights are small integers — incremental cut value
updates on pivots (`updateCutvalues`). Iteration orders and tie-breaking are
those of the Rust code:

* `nodeEdges[nid]` holds the incoming edge ids of node `nid` in increasing
  internal id order, followed by its outgoing edge ids in increasing order;
* `treeEdgeIds` is the insertion-ordered list of tree edges (Java
  `LinkedHashSet`): `leaveEdge` returns the first one with a negative cut value;
* `minimalSlack`/`enterEdge` keep the first edge (lowest internal id) with the
  strictly smallest slack.

State lives in `NetworkSimplexM := StateRefT (NetworkSimplex ο) IO`. Loops that
update dense arrays are pure kernels applied with `modify` (the state is unique
inside `modify`, so arrays are updated in place).

Not ported: the `ELK_TRACE_NETWORK_SIMPLEX` diagnostic print when no entering
edge exists (the state changes are identical), and the reusable allocation
buffer `postorder_stack` (the traversal uses a local stack).
-/

namespace Elk.Alg.Common.NetworkSimplex

open Elk.Core.Util

/-- `NetworkSimplex.REMOVE_SUBTREES_THRESH`: empirically determined threshold
when removing subtrees pays off. -/
def REMOVE_SUBTREES_THRESH : Nat := 40

/-- `NetworkSimplex.FUZZY_ST_ZERO`: small value below zero, used to check
whether cut values are negative despite floating point imprecision. -/
def FUZZY_ST_ZERO : Float := -1e-10

/-- `Integer.MAX_VALUE` / `i32::MAX`. -/
def I32_MAX : Int := 2147483647

/-- `Integer.MIN_VALUE` / `i32::MIN`. -/
def I32_MIN : Int := -2147483648

/-- `NetworkSimplex`: configuration and working state of one network simplex run. -/
structure NetworkSimplex (ο : Type) where
  /-- The graph all methods operate on (Rust `&mut NGraph`, owned here and
  returned by `execute`). -/
  graph : NGraph ο
  /-- `previousLayeringNodeCounts`: number of nodes per layer of a previous
  layering, considered by `normalize` and `balanceLayers`. -/
  previousLayeringNodeCounts : Option (Array Int) := none
  /-- `balance`: whether to apply `balanceLayers`. -/
  balance : Bool := false
  /-- `iterationLimit`: a limit on the number of pivots. -/
  iterationLimit : Int := I32_MAX
  /-- `edges`: all edges of the graph, indexed by their internal id. -/
  edges : Array NEdgeId := #[]
  /-- `treeEdges` (Java `LinkedHashSet`): internal ids of the spanning tree
  edges in insertion order. -/
  treeEdgeIds : Array Nat := #[]
  /-- `sources`: nodes without incoming edges. -/
  sources : Array NNodeId := #[]
  /-- `edgeVisited`: DFS visit flags per edge. -/
  edgeVisited : Array Bool := #[]
  /-- `postOrder`: the current post-order traversal number. -/
  postOrder : Int := 1
  /-- `poID`: post-order traversal id of each node. -/
  poId : Array Int := #[]
  /-- `lowestPoID`: lowest post-order id reachable below each node. -/
  lowestPoId : Array Int := #[]
  /-- `cutvalue`: the cut value of every (tree) edge (unboxed, like Rust `Vec<f64>`). -/
  cutvalue : FloatArray := ⟨#[]⟩
  /-- Rust `integral_cutvalues`: all weights are exactly representable integers
  whose absolute sum is at most 2^52, so pivots update cut values incrementally. -/
  integralCutvalues : Bool := false
  /-- `subtreeNodesStack`: removed subtree nodes with the edge that attached them. -/
  subtreeNodesStack : Option (Array (NNodeId × NEdgeId)) := none
  /-- Rust `e_src`: source node of each edge. -/
  eSrc : Array NNodeId := #[]
  /-- Rust `e_tgt`: target node of each edge. -/
  eTgt : Array NNodeId := #[]
  /-- Rust `e_src_id`: internal id of the source of each edge. -/
  eSrcId : Array Nat := #[]
  /-- Rust `e_tgt_id`: internal id of the target of each edge. -/
  eTgtId : Array Nat := #[]
  /-- Rust `e_delta`: cached `NEdge.delta`. -/
  eDelta : Array Int := #[]
  /-- Rust `e_weight`: cached `NEdge.weight`. -/
  eWeight : Array Float := #[]
  /-- Rust `e_tree`: tree edge flags (Java `NEdge.treeEdge`). -/
  eTree : Array Bool := #[]
  /-- Rust `node_edges`: connected edge ids per node (incoming first, then outgoing). -/
  nodeEdges : Array (Array Nat) := #[]
  /-- Rust `tree_edges`: tree-only adjacency, in the same order as `nodeEdges`. -/
  treeEdges : Array (Array Nat) := #[]
  /-- Rust `n_layer`: layer per node during the pivots (Java `NNode.layer`). -/
  nLayer : Array Int := #[]
  /-- Rust `n_tree_node`: tree node flags (Java `NNode.treeNode`). -/
  nTreeNode : Array Bool := #[]

instance {ο : Type} : Inhabited (NetworkSimplex ο) := ⟨{ graph := {} }⟩

/-- The network simplex state monad. -/
abbrev NetworkSimplexM (ο : Type) := StateRefT (NetworkSimplex ο) IO

namespace NetworkSimplex

variable {ο : Type}

-- ================================== Configuration ===========================================

/-- `NetworkSimplex.forGraph(NGraph)`: a new instance for `graph`. -/
def forGraph (graph : NGraph ο) : NetworkSimplex ο := { graph := graph }

/-- `withBalancing(boolean)`: whether to balance the layering concerning its width. -/
def withBalancing (ns : NetworkSimplex ο) (doBalance : Bool) : NetworkSimplex ο :=
  { ns with balance := doBalance }

/-- `withPreviousLayering(int[])`: node counts per layer of previously layered
components, considered while balancing. -/
def withPreviousLayering (ns : NetworkSimplex ο) (counts : Option (Array Int)) : NetworkSimplex ο :=
  { ns with previousLayeringNodeCounts := counts }

/-- `withIterationLimit(int)`: the maximum number of iterations (pivots). -/
def withIterationLimit (ns : NetworkSimplex ο) (limit : Int) : NetworkSimplex ο :=
  { ns with iterationLimit := limit }

-- ================================== Helpers =================================================

/-- Reads a node of the graph. -/
@[inline] def getNode (n : NNodeId) : NetworkSimplexM ο (NNode ο) := do
  return (← get).graph.node n

/-- Reads an edge of the graph. -/
@[inline] def getEdge (e : NEdgeId) : NetworkSimplexM ο (NEdge ο) := do
  return (← get).graph.edge e

/-- In-place update of a graph node. -/
@[inline] def modifyNode (n : NNodeId) (f : NNode ο → NNode ο) : NetworkSimplexM ο Unit :=
  modify fun s => { s with graph := s.graph.modifyNode n f }

/-- In-place update of a graph edge. -/
@[inline] def modifyEdge (e : NEdgeId) (f : NEdge ο → NEdge ο) : NetworkSimplexM ο Unit :=
  modify fun s => { s with graph := s.graph.modifyEdge e f }

/-- `Arrays.fill(arr, false)` / Rust `fill(false)` (in place when unique). -/
private def fillFalse (a : Array Bool) : Array Bool := Id.run do
  let mut a := a
  for i in [0:a.size] do
    a := a.set! i false
  return a

/-- Rust `f64::fract`: `x - x.trunc()`. -/
private def fract (x : Float) : Float := x - (if x < 0.0 then x.ceil else x.floor)

/-- `2^52` as `f64` (Rust `(1_u64 << 52) as f64`). -/
private def TWO_POW_52 : Float := 4503599627370496.0

/-- Rust `slice::partition_point` (binary search): the first index whose
element does not satisfy `pred`, for a slice partitioned by `pred`. -/
private def partitionPoint (a : Array Nat) (pred : Nat → Bool) : Nat := Id.run do
  let mut lo := 0
  let mut hi := a.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if pred a[mid]! then lo := mid + 1 else hi := mid
  return lo

-- =============================== Initialization Methods =====================================

/-- Rust `integral_cutvalues` test: every weight is finite and integral and the
running sum of absolute weights stays at most 2^52 (`try_fold` short-circuits
at the first failure). -/
def integralWeights (weights : Array Float) : Bool := Id.run do
  let mut sum := fl0p0
  for w in weights do
    let sum' := sum + w.abs
    if !(w.isFinite && fract w == fl0p0 && sum' <= TWO_POW_52) then
      return false
    sum := sum'
  return true

/-- Builds the edge caches (`eSrc` … `eTree`) for the collected `edges`. -/
private def buildEdgeCaches (s : NetworkSimplex ο) (edges : Array NEdgeId) : NetworkSimplex ο := Id.run do
  let numEdges := edges.size
  let mut g := s.graph
  let s : NetworkSimplex ο := { s with graph := {} }
  let mut eSrc : Array NNodeId := Array.mkEmpty numEdges
  let mut eTgt : Array NNodeId := Array.mkEmpty numEdges
  let mut eSrcId : Array Nat := Array.mkEmpty numEdges
  let mut eTgtId : Array Nat := Array.mkEmpty numEdges
  let mut eDelta : Array Int := Array.mkEmpty numEdges
  let mut eWeight : Array Float := Array.mkEmpty numEdges
  let mut eTree : Array Bool := Array.mkEmpty numEdges
  for h : index in [0:numEdges] do
    let e := edges[index]
    g := g.modifyEdge e fun ed => { ed with internalId := index }
    let ed := g.edge e
    eSrc := eSrc.push ed.source
    eTgt := eTgt.push ed.target
    eDelta := eDelta.push ed.delta
    eWeight := eWeight.push ed.weight
    eTree := eTree.push false
    -- source/target internal ids were set by `initialize`
    eSrcId := eSrcId.push (g.node ed.source).internalId
    eTgtId := eTgtId.push (g.node ed.target).internalId
  return { s with graph := g, eSrc := eSrc, eTgt := eTgt, eSrcId := eSrcId, eTgtId := eTgtId,
                  eDelta := eDelta, eWeight := eWeight, eTree := eTree }

/-- Builds `nodeEdges` (incoming edge ids first, then outgoing, each in
increasing id order) and empty `treeEdges`. -/
private def buildNodeCaches (s : NetworkSimplex ο) (numNodes : Nat) : NetworkSimplex ο := Id.run do
  let numEdges := s.eSrcId.size
  let mut nodeEdges : Array (Array Nat) := Array.replicate numNodes #[]
  for eid in [0:numEdges] do
    nodeEdges := nodeEdges.modify s.eTgtId[eid]! (·.push eid) -- incoming to target
  for eid in [0:numEdges] do
    nodeEdges := nodeEdges.modify s.eSrcId[eid]! (·.push eid) -- outgoing from source
  return { s with
    nLayer := Array.replicate numNodes 0
    nTreeNode := Array.replicate numNodes false
    nodeEdges := nodeEdges
    treeEdges := Array.replicate numNodes #[] }

/-- `NetworkSimplex.initialize()` (`initialize` is a Lean keyword): re-indexes the nodes (position in
`nodeList`) and edges (order of the outgoing edge lists), collects the sources
and builds all dense caches. -/
def initState : NetworkSimplexM ο Unit := do
  let order := (← get).graph.nodeList
  let numNodes := order.size
  modify fun s => { s with
    poId := Array.replicate numNodes 0
    lowestPoId := Array.replicate numNodes 0
    sources := #[] }
  let mut edges : Array NEdgeId := #[]
  let mut sources : Array NNodeId := #[]
  for h : index in [0:numNodes] do
    let n := order[index]
    modifyNode n fun nd => { nd with internalId := index }
    let nd ← getNode n
    if nd.incomingEdges.isEmpty then
      sources := sources.push n
    edges := edges ++ nd.outgoingEdges
  modify fun s => { s with sources := sources }
  modify fun s => buildEdgeCaches s edges
  modify fun s => { s with integralCutvalues := integralWeights s.eWeight }
  modify fun s => buildNodeCaches s numNodes
  let numEdges := edges.size
  modify fun s =>
    if s.cutvalue.size < numEdges then
      { s with cutvalue := ⟨Array.replicate numEdges fl0p0⟩, edgeVisited := Array.replicate numEdges false }
    else
      { s with edgeVisited := fillFalse s.edgeVisited }
  modify fun s => { s with edges := edges, treeEdgeIds := #[], postOrder := 1 }

/-- `NetworkSimplex.dispose()`: releases all working data. -/
def dispose : NetworkSimplexM ο Unit :=
  modify fun s => { s with
    cutvalue := ⟨#[]⟩, edges := #[], treeEdgeIds := #[], edgeVisited := #[]
    eSrc := #[], eTgt := #[], eSrcId := #[], eTgtId := #[], eDelta := #[], eWeight := #[], eTree := #[]
    nodeEdges := #[], treeEdges := #[], nLayer := #[], nTreeNode := #[]
    lowestPoId := #[], poId := #[], sources := #[], subtreeNodesStack := none }

-- ============================== Network-Simplex Algorithm ===================================

/-- Kernel of `layeringTopologicalNumbering`. -/
private def layeringTopologicalNumberingAux (s : NetworkSimplex ο) : NetworkSimplex ο := Id.run do
  let numNodes := s.graph.nodeList.size
  let mut incident : Array Nat := Array.replicate numNodes 0
  for eid in [0:s.edges.size] do
    incident := incident.modify s.eTgtId[eid]! (· + 1)
  let mut roots : Array Nat := #[]
  for nid in [0:numNodes] do
    if incident[nid]! == 0 then
      roots := roots.push nid
  let mut nLayer := s.nLayer
  let s := { s with nLayer := #[] }
  let mut head := 0
  while head < roots.size do
    let nid := roots[head]!
    head := head + 1
    let nodeLayer := nLayer[nid]!
    for eid in s.nodeEdges[nid]! do
      if s.eSrcId[eid]! != nid then
        continue -- skip incoming edges
      let tgtId := s.eTgtId[eid]!
      let newLayer := max nLayer[tgtId]! (nodeLayer + s.eDelta[eid]!)
      nLayer := nLayer.set! tgtId newLayer
      if incident[tgtId]! > 0 then
        incident := incident.set! tgtId (incident[tgtId]! - 1)
      if incident[tgtId]! == 0 then
        roots := roots.push tgtId
  return { s with nLayer := nLayer }

/-- `layeringTopologicalNumbering(List)`: an initial feasible layering by a
minimal topological numbering, starting from all nodes without incoming edges
(in internal id order), following outgoing edges only. -/
def layeringTopologicalNumbering : NetworkSimplexM ο Unit := modify layeringTopologicalNumberingAux

/-- Kernel of `tightTreeDfs`: returns the updated state and the node count. -/
private partial def tightTreeDfsAux (s : NetworkSimplex ο) (nid : Nat) : NetworkSimplex ο × Nat := Id.run do
  let mut s := { s with nTreeNode := s.nTreeNode.set! nid true }
  let mut nodeCount := 1
  let adj := s.nodeEdges[nid]!
  for eid in adj do
    if s.edgeVisited[eid]! then
      continue
    s := { s with edgeVisited := s.edgeVisited.set! eid true }
    let srcId := s.eSrcId[eid]!
    let tgtId := s.eTgtId[eid]!
    let oppId := if srcId == nid then tgtId else srcId
    if s.eTree[eid]! then
      let (s', c) := tightTreeDfsAux s oppId
      s := s'
      nodeCount := nodeCount + c
    else if !s.nTreeNode[oppId]! then
      if s.eDelta[eid]! == s.nLayer[tgtId]! - s.nLayer[srcId]! then
        s := { s with eTree := s.eTree.set! eid true, treeEdgeIds := s.treeEdgeIds.push eid }
        let (s', c) := tightTreeDfsAux s oppId
        s := s'
        nodeCount := nodeCount + c
  return (s, nodeCount)

/-- `tightTreeDFS(NNode)`: grows a DFS tree from node `nid` along tree edges and
tight non-tree edges (to non-tree nodes) and returns the number of nodes in it. -/
def tightTreeDfs (nid : Nat) : NetworkSimplexM ο Nat :=
  modifyGet fun s => let (s, c) := tightTreeDfsAux s nid; (c, s)

/-- `minimalSlack()`: the first edge (by internal id) with exactly one endpoint
in the tree and a strictly minimal slack, or `none`. -/
def minimalSlack (s : NetworkSimplex ο) : Option Nat := Id.run do
  let mut minSlack := I32_MAX
  let mut minEid : Option Nat := none
  for eid in [0:s.edges.size] do
    let srcId := s.eSrcId[eid]!
    let tgtId := s.eTgtId[eid]!
    if s.nTreeNode[srcId]! != s.nTreeNode[tgtId]! then
      let slack := s.nLayer[tgtId]! - s.nLayer[srcId]! - s.eDelta[eid]!
      if slack < minSlack then
        minSlack := slack
        minEid := some eid
  return minEid

/-- Shifts all tree nodes by the slack of edge `eid` (negated if its target is
a tree node), making the edge tight. -/
private def shiftTreeAux (s : NetworkSimplex ο) (eid : Nat) : NetworkSimplex ο := Id.run do
  let srcLayer := s.nLayer[s.eSrcId[eid]!]!
  let tgtLayer := s.nLayer[s.eTgtId[eid]!]!
  let tgtTree := s.nTreeNode[s.eTgtId[eid]!]!
  let mut slack := tgtLayer - srcLayer - s.eDelta[eid]!
  if tgtTree then
    slack := -slack
  let mut nLayer := s.nLayer
  let s := { s with nLayer := #[] }
  for i in [0:nLayer.size] do
    if s.nTreeNode[i]! then
      nLayer := nLayer.modify i (· + slack)
  return { s with nLayer := nLayer }

/-- Appends the tree edges of `nodeEdges[nid]` to `treeEdges[nid]` for every node. -/
private def collectTreeEdgesAux (s : NetworkSimplex ο) : NetworkSimplex ο := Id.run do
  let mut treeEdges := s.treeEdges
  let s := { s with treeEdges := #[] }
  for nid in [0:s.nodeEdges.size] do
    let tree := s.nodeEdges[nid]!.filter fun eid => s.eTree[eid]!
    treeEdges := treeEdges.modify nid (· ++ tree)
  return { s with treeEdges := treeEdges }

/-- Index of the next tree edge in `adj` at or after `cursor` that has not been
visited (or `adj.size`): the adjacency scan of the post-order traversal. -/
private def scanTreeAdj (eTree edgeVisited : Array Bool) (adj : Array Nat) (cursor : Nat) : Nat :=
  if h : cursor < adj.size then
    let eid := adj[cursor]
    if eTree[eid]! && !edgeVisited[eid]! then cursor
    else scanTreeAdj eTree edgeVisited adj (cursor + 1)
  else
    adj.size
termination_by adj.size - cursor

/-- Loop of the iterative post-order DFS (Rust `postorder_traversal`) over an
explicit stack of `(nid, adjacency cursor, lowest)` frames, kept in three
parallel arrays. Returns `(edgeVisited, poId, lowestPoId, postOrder)`. -/
private partial def postorderLoop (s : NetworkSimplex ο) (edgeVisited : Array Bool)
    (poId lowestPoId : Array Int) (postOrder : Int)
    (stackNid stackCursor : Array Nat) (stackLowest : Array Int) :
    Array Bool × Array Int × Array Int × Int :=
  if stackNid.isEmpty then
    (edgeVisited, poId, lowestPoId, postOrder)
  else
    let top := stackNid.size - 1
    let nid := stackNid[top]!
    let adj := s.treeEdges[nid]!
    -- advance through the adjacency list to the next unvisited tree edge
    let idx := scanTreeAdj s.eTree edgeVisited adj stackCursor[top]!
    if idx < adj.size then
      let eid := adj[idx]!
      let oppId := if s.eSrcId[eid]! == nid then s.eTgtId[eid]! else s.eSrcId[eid]!
      postorderLoop s (edgeVisited.set! eid true) poId lowestPoId postOrder
        (stackNid.push oppId) ((stackCursor.set! top (idx + 1)).push 0) (stackLowest.push I32_MAX)
    else
      -- post-order: all children visited
      let myLowest := min stackLowest[top]! postOrder
      let inRange := nid < poId.size
      let poId := if inRange then poId.set! nid postOrder else poId
      let lowestPoId := if inRange then lowestPoId.set! nid myLowest else lowestPoId
      let stackLowest := stackLowest.pop
      -- propagate lowest to the parent
      let stackLowest := if top > 0 then stackLowest.modify (top - 1) (min · myLowest) else stackLowest
      postorderLoop s edgeVisited poId lowestPoId (postOrder + 1) stackNid.pop stackCursor.pop stackLowest

/-- Kernel of `postorderTraversal`. -/
private def postorderTraversalAux (s : NetworkSimplex ο) (startNid : Nat) : NetworkSimplex ο :=
  let edgeVisited := s.edgeVisited
  let poId := s.poId
  let lowestPoId := s.lowestPoId
  let s := { s with edgeVisited := #[], poId := #[], lowestPoId := #[] }
  let (edgeVisited, poId, lowestPoId, postOrder) :=
    postorderLoop s edgeVisited poId lowestPoId s.postOrder #[startNid] #[0] #[I32_MAX]
  let s := { s with edgeVisited := edgeVisited, poId := poId, lowestPoId := lowestPoId, postOrder := postOrder }
  -- Fundamental-cycle cut updates need intervals for every node of one spanning
  -- tree; disconnected or source-free cyclic inputs leave nodes unvisited.
  if postOrder != (s.graph.nodeList.size : Int) + 1 then
    { s with integralCutvalues := false }
  else
    s

/-- `postorderTraversal(NNode)`: assigns post-order ids (`poId`) and the lowest
post-order id below each node (`lowestPoId`) by a DFS over tree edges from
node `startNid`. Clears `integralCutvalues` if not all nodes were reached. -/
def postorderTraversal (startNid : Nat) : NetworkSimplexM ο Unit :=
  modify (postorderTraversalAux · startNid)

/-- `isInHead(NNode, NEdge)` (Rust `is_in_head_by_id`): whether node `nodeId`
belongs to the head component (the one containing the target) of the tree
edge from `sourceId` to `targetId`. -/
@[inline] def isInHeadById (s : NetworkSimplex ο) (nodeId sourceId targetId : Nat) : Bool :=
  let poN := s.poId[nodeId]!
  let poS := s.poId[sourceId]!
  let poT := s.poId[targetId]!
  if s.lowestPoId[sourceId]! <= poN && poN <= poS && s.lowestPoId[targetId]! <= poN && poN <= poT then
    poS >= poT
  else
    poS < poT

/-- Cut value of the tree edge `tdId` determined at leaf `node`: starts from
`acc` (the edge weight) and adds the contributions of `adj[i:]` (the edges of
`node`). Rust updates `cutvalue[td_id]` in place with the same floating point
operations in the same order; the other cut values read here are unaffected. -/
private def cutAccumulate (s : NetworkSimplex ο) (cutvalue : FloatArray) (adj : Array Nat)
    (node tdId source target : Nat) (i : Nat) (acc : Float) : Float :=
  if h : i < adj.size then
    let eid := adj[i]
    if eid == tdId then
      cutAccumulate s cutvalue adj node tdId source target (i + 1) acc
    else
      let eWeight := s.eWeight[eid]!
      let acc :=
        if s.eTree[eid]! then
          if s.eSrcId[eid]! == source || s.eTgtId[eid]! == target then acc - (cutvalue[eid]! - eWeight)
          else acc + (cutvalue[eid]! - eWeight)
        else if node == source then
          if s.eSrcId[eid]! == node then acc + eWeight else acc - eWeight
        else if s.eSrcId[eid]! == node then acc - eWeight
        else acc + eWeight
      cutAccumulate s cutvalue adj node tdId source target (i + 1) acc
  else
    acc
termination_by adj.size - i

/-- Leaf elimination from `node` (Rust `loop` in `cutvalues`): while the node
has exactly one incident tree edge with unknown cut value, determine it, remove
it from both endpoint summaries and continue at the opposite end. -/
private partial def cutChain (s : NetworkSimplex ο) (cutvalue : FloatArray)
    (unknownCount unknownXor : Array Nat) (node : Nat) : FloatArray × Array Nat × Array Nat :=
  if unknownCount[node]! != 1 then
    (cutvalue, unknownCount, unknownXor)
  else
    let tdId := unknownXor[node]!
    if tdId >= cutvalue.size then
      (cutvalue, unknownCount, unknownXor)
    else
      let source := s.eSrcId[tdId]!
      let target := s.eTgtId[tdId]!
      let value := cutAccumulate s cutvalue s.nodeEdges[node]! node tdId source target 0 s.eWeight[tdId]!
      let cutvalue := cutvalue.set! tdId value
      -- remove the determined edge from both endpoint summaries
      let unknownCount := (unknownCount.modify source (· - 1)).modify target (· - 1)
      let unknownXor := (unknownXor.modify source (· ^^^ tdId)).modify target (· ^^^ tdId)
      cutChain s cutvalue unknownCount unknownXor (if source == node then target else source)

/-- Kernel of `cutvalues`. -/
private def cutvaluesAux (s : NetworkSimplex ο) : NetworkSimplex ο := Id.run do
  -- per node: count and XOR of the incident tree edges with unknown cut value
  -- (only a singleton is read, whose XOR is exactly its sole edge id)
  let mut unknownCount : Array Nat :=
    s.nodeEdges.map fun adj => adj.foldl (fun c eid => if s.eTree[eid]! then c + 1 else c) 0
  let mut unknownXor : Array Nat :=
    s.nodeEdges.map fun adj => adj.foldl (fun x eid => if s.eTree[eid]! then x ^^^ eid else x) 0
  let mut leafs : Array Nat := #[]
  for nid in [0:unknownCount.size] do
    if unknownCount[nid]! == 1 then
      leafs := leafs.push nid
  let mut cutvalue := s.cutvalue
  let s := { s with cutvalue := ⟨#[]⟩ }
  for leaf in leafs do
    let (cv, uc, ux) := cutChain s cutvalue unknownCount unknownXor leaf
    cutvalue := cv
    unknownCount := uc
    unknownXor := ux
  return { s with cutvalue := cutvalue }

/-- `cutvalues()`: determines the cut value of every tree edge by leaf
elimination (Rust: count + XOR summaries of the unknown incident tree edges).
The cut value of a tree edge is the weight sum of all edges from the tail to
the head component (including the edge) minus the weights from head to tail. -/
def cutvalues : NetworkSimplexM ο Unit := modify cutvaluesAux

/-- Rust `remove_unknown_cutvalue` (test-only): removes `edge` from the unknown
cut values of `node`. -/
def removeUnknownCutvalue (node : NNodeId) (edge : NEdgeId) : NetworkSimplexM ο Unit :=
  modifyNode node fun n => { n with unknownCutvalues := n.unknownCutvalues.filter (· != edge) }

/-- Rust `cutvalues_reference` (`#[cfg(test)]`): the object-based leaf
elimination of the Java `cutvalues()`, keeping the unknown cut values in
`NNode.unknownCutvalues`. Used by the tests to validate `cutvalues` bit for bit. -/
def cutvaluesReference : NetworkSimplexM ο Unit := do
  let order := (← get).graph.nodeList
  let mut leafs : Array NNodeId := #[]
  for node in order do
    let nid := (← getNode node).internalId
    let unknown ← do
      let s ← get
      pure ((s.nodeEdges[nid]!.filter fun eid => s.eTree[eid]!).map fun eid => s.edges[eid]!)
    modifyNode node fun n => { n with unknownCutvalues := unknown }
    if unknown.size == 1 then
      leafs := leafs.push node
  for leaf in leafs do
    let mut node := leaf
    while true do
      let nd ← getNode node
      if nd.unknownCutvalues.size != 1 then
        break
      let toDetermine := nd.unknownCutvalues[0]!
      let tdId := (← getEdge toDetermine).internalId
      if tdId >= (← get).cutvalue.size then
        break
      let (tdWeight, source, target) ← do
        let s ← get
        pure (s.eWeight[tdId]!, s.eSrc[tdId]!, s.eTgt[tdId]!)
      modify fun s => { s with cutvalue := s.cutvalue.set! tdId tdWeight }
      let adj := (← get).nodeEdges[nd.internalId]!
      for eid in adj do
        if eid == tdId then
          continue
        let (eWeight, isTree, eSrc, eTgt, cvE) ← do
          let s ← get
          pure (s.eWeight[eid]!, s.eTree[eid]!, s.eSrc[eid]!, s.eTgt[eid]!, s.cutvalue[eid]!)
        let update : Float → Float :=
          if isTree then
            if eSrc == source || eTgt == target then
              fun cv => cv - (cvE - eWeight)
            else
              fun cv => cv + (cvE - eWeight)
          else if node == source then
            if eSrc == node then (· + eWeight) else (· - eWeight)
          else if eSrc == node then (· - eWeight)
          else (· + eWeight)
        modify fun s => { s with cutvalue := s.cutvalue.set! tdId (update s.cutvalue[tdId]!) }
      removeUnknownCutvalue source toDetermine
      removeUnknownCutvalue target toDetermine
      node := if source == node then target else source

/-- `leaveEdge()`: the first tree edge (in `treeEdgeIds` insertion order) with a
cut value below `FUZZY_ST_ZERO`, or `none` if the layering is optimal. -/
def leaveEdge (s : NetworkSimplex ο) : Option Nat :=
  s.treeEdgeIds.find? fun eid =>
    s.eTree[eid]! && eid < s.cutvalue.size && s.cutvalue[eid]! < FUZZY_ST_ZERO

/-- Edge loop of `enterEdge` from `eid` on: keeps the first edge from the head
(`head[src]`) to the tail component with strictly minimal slack. -/
private def enterSearch (s : NetworkSimplex ο) (head : Array Bool) (eid : Nat)
    (replace : Option Nat) (repSlack : Int) : Option Nat :=
  if eid < s.edges.size then
    let srcId := s.eSrcId[eid]!
    let tgtId := s.eTgtId[eid]!
    if head[srcId]! && !head[tgtId]! then
      let slack := s.nLayer[tgtId]! - s.nLayer[srcId]! - s.eDelta[eid]!
      if slack < repSlack then
        enterSearch s head (eid + 1) (some eid) slack
      else
        enterSearch s head (eid + 1) replace repSlack
    else
      enterSearch s head (eid + 1) replace repSlack
  else
    replace
termination_by s.edges.size - eid

/-- `enterEdge(NEdge)`: the non-tree edge from the head to the tail component of
the tree edge `leaveId` with minimal slack (first by internal id on ties), or
`none` if there is none or `leaveId` is not a tree edge (Java throws
`IllegalArgumentException`; Rust returns `None`). -/
def enterEdge (s : NetworkSimplex ο) (leaveId : Nat) : Option Nat := Id.run do
  if !s.eTree[leaveId]! then
    return none
  let leaveSrcId := s.eSrcId[leaveId]!
  let leaveTgtId := s.eTgtId[leaveId]!
  -- each node's cut membership is constant for this search
  let mut head : Array Bool := Array.mkEmpty s.nLayer.size
  for nid in [0:s.nLayer.size] do
    head := head.push (isInHeadById s nid leaveSrcId leaveTgtId)
  return enterSearch s head 0 none I32_MAX

/-- Kernel of `updateCutvalues`. -/
private def updateCutvaluesAux (s : NetworkSimplex ο) (leaveId enterId : Nat) : NetworkSimplex ο := Id.run do
  let cut := s.cutvalue[leaveId]!
  let source := s.eSrcId[enterId]!
  let target := s.eTgtId[enterId]!
  let mut cutvalue := s.cutvalue
  let s := { s with cutvalue := ⟨#[]⟩ }
  for eid in s.treeEdgeIds do
    if eid == leaveId then
      continue
    let sourceInHead := isInHeadById s source s.eSrcId[eid]! s.eTgtId[eid]!
    let targetInHead := isInHeadById s target s.eSrcId[eid]! s.eTgtId[eid]!
    if sourceInHead != targetInHead then
      if targetInHead then
        cutvalue := cutvalue.set! eid (cutvalue[eid]! + cut)
      else
        cutvalue := cutvalue.set! eid (cutvalue[eid]! - cut)
  cutvalue := cutvalue.set! enterId (-cut)
  return { s with cutvalue := cutvalue }

/-- Rust `update_cutvalues`: incremental cut value update for a pivot (only
used when `integralCutvalues`). Only cuts on the entering edge's fundamental
cycle change; the new cut is the old one plus the cycle's signed leaving cut.
Must run before the tree membership and post-order ids change. -/
def updateCutvalues (leaveId enterId : Nat) : NetworkSimplexM ο Unit :=
  modify (updateCutvaluesAux · leaveId enterId)

/-- Tree membership update of `exchange`: toggles the flags, `treeEdgeIds` and
the tree adjacency (the entering edge is inserted at its `nodeEdges` position,
keyed by `(isOutgoing, internalId)`). -/
private def swapTreeEdgeAux (s : NetworkSimplex ο) (leaveId enterId : Nat) : NetworkSimplex ο := Id.run do
  let mut treeEdgeIds := s.treeEdgeIds
  let mut eTree := s.eTree
  let mut treeEdges := s.treeEdges
  let s := { s with treeEdgeIds := #[], eTree := #[], treeEdges := #[] }
  eTree := eTree.set! leaveId false
  if let some pos := treeEdgeIds.findIdx? (· == leaveId) then
    treeEdgeIds := treeEdgeIds.eraseIdx! pos
  eTree := eTree.set! enterId true
  treeEdgeIds := treeEdgeIds.push enterId
  for nid in #[s.eSrcId[leaveId]!, s.eTgtId[leaveId]!] do
    treeEdges := treeEdges.modify nid (·.filter (· != leaveId))
  let enterSrcId := s.eSrcId[enterId]!
  for nid in #[enterSrcId, s.eTgtId[enterId]!] do
    -- key `(isOutgoing, id)` compared lexicographically (`false < true`)
    let keyOut := enterSrcId == nid
    let lt (eid : Nat) : Bool :=
      let out := s.eSrcId[eid]! == nid
      (!out && keyOut) || (out == keyOut && eid < enterId)
    let insertAt := partitionPoint treeEdges[nid]! lt
    treeEdges := treeEdges.modify nid (·.insertIdx! insertAt enterId)
  return { s with treeEdgeIds := treeEdgeIds, eTree := eTree, treeEdges := treeEdges }

/-- Layer update of `exchange`: shifts every node of the tail component of the
old tree (w.r.t. `leaveId`) such that the entering edge becomes tight. -/
private def shiftTailAux (s : NetworkSimplex ο) (leaveId enterId : Nat) : NetworkSimplex ο := Id.run do
  let leaveSrcId := s.eSrcId[leaveId]!
  let leaveTgtId := s.eTgtId[leaveId]!
  let enterSrcId := s.eSrcId[enterId]!
  let enterTgtId := s.eTgtId[enterId]!
  let mut delta := s.nLayer[enterTgtId]! - s.nLayer[enterSrcId]! - s.eDelta[enterId]!
  if !isInHeadById s enterTgtId leaveSrcId leaveTgtId then
    delta := -delta
  let mut nLayer := s.nLayer
  let s := { s with nLayer := #[] }
  for nid in [0:nLayer.size] do
    if !isInHeadById s nid leaveSrcId leaveTgtId then
      nLayer := nLayer.modify nid (· + delta)
  return { s with nLayer := nLayer }

/-- `exchange(NEdge, NEdge)`: replaces the tree edge `leaveId` by the non-tree
edge `enterId`, shifts the tail component, recomputes the post-order ids and
updates the cut values (incrementally if `integralCutvalues`). Does nothing if
`leaveId` is no tree edge or `enterId` already is one (Java throws
`IllegalArgumentException`; Rust returns). -/
def exchange (leaveId enterId : Nat) : NetworkSimplexM ο Unit := do
  let valid ← do
    let s ← get
    pure (s.eTree[leaveId]! && !s.eTree[enterId]!)
  if !valid then
    return
  if (← get).integralCutvalues then
    updateCutvalues leaveId enterId
  modify (swapTreeEdgeAux · leaveId enterId)
  modify (shiftTailAux · leaveId enterId)
  modify fun s => { s with postOrder := 1, edgeVisited := fillFalse s.edgeVisited }
  if !(← get).graph.nodeList.isEmpty then
    postorderTraversal 0
  if !(← get).integralCutvalues then
    cutvalues

/-- `feasibleTree()`: determines an initial feasible tight spanning tree
(topological numbering, then repeatedly growing a tight tree from node 0 and
shifting it by the minimal slack of an incident edge), followed by the
post-order ids and the initial cut values. -/
def feasibleTree : NetworkSimplexM ο Unit := do
  layeringTopologicalNumbering
  if (← get).edges.isEmpty then
    return
  modify fun s => { s with edgeVisited := fillFalse s.edgeVisited }
  while !(← get).graph.nodeList.isEmpty do
    let count ← tightTreeDfs 0
    if count >= (← get).graph.nodeList.size then
      break
    let some eid := minimalSlack (← get) | break
    modify (shiftTreeAux · eid)
    modify fun s => { s with edgeVisited := fillFalse s.edgeVisited }
  modify collectTreeEdgesAux
  modify fun s => { s with edgeVisited := fillFalse s.edgeVisited }
  if !(← get).graph.nodeList.isEmpty then
    postorderTraversal 0
    cutvalues

/-- `minimalSpan(NNode)`: the lengths `(in, out)` of the currently shortest
incoming and outgoing edge of `node` (`-1` if there is none), reading the
current `NNode.layer`s. As in Java/Rust, an incoming edge that is not shorter
than the current incoming minimum is compared against the outgoing minimum. -/
def minimalSpan (node : NNodeId) : NetworkSimplexM ο (Int × Int) := do
  let mut minSpanOut := I32_MAX
  let mut minSpanIn := I32_MAX
  let edges := (← getNode node).connectedEdges
  for e in edges do
    let ed ← getEdge e
    let span := (← getNode ed.target).layer - (← getNode ed.source).layer
    let targetIsNode := ed.target == node
    if targetIsNode && span < minSpanIn then
      minSpanIn := span
    else if span < minSpanOut then
      minSpanOut := span
  if minSpanIn == I32_MAX then
    minSpanIn := -1
  if minSpanOut == I32_MAX then
    minSpanOut := -1
  return (minSpanIn, minSpanOut)

/-- `normalize()`: shifts all layers such that the lowest one is `0` and
returns the number of nodes per layer, plus `previousLayeringNodeCounts`. -/
def normalize : NetworkSimplexM ο (Array Int) := do
  let order := (← get).graph.nodeList
  let mut highest := I32_MIN
  let mut lowest := I32_MAX
  for node in order do
    let layer := (← getNode node).layer
    highest := max highest layer
    lowest := min lowest layer
  let size := (max (highest - lowest + 1) 1).toNat
  let mut filling : Array Int := Array.replicate size 0
  for node in order do
    modifyNode node fun n => { n with layer := n.layer - lowest }
    let idx := (max (← getNode node).layer 0).toNat
    if idx < filling.size then
      filling := filling.modify idx (· + 1)
  if let some previous := (← get).previousLayeringNodeCounts then
    for h : idx in [0:previous.size] do
      if idx >= filling.size then
        break
      filling := filling.modify idx (· + previous[idx])
  return filling

/-- `balance(int[])` (Rust `balance_layers`): moves nodes with as many incoming
as outgoing edges to the least filled layer within their feasible span. -/
def balanceLayers (filling : Array Int) : NetworkSimplexM ο Unit := do
  let mut filling := filling
  let order := (← get).graph.nodeList
  for node in order do
    let nd ← getNode node
    if nd.incomingEdges.size != nd.outgoingEdges.size then
      continue
    let currentLayer := nd.layer
    let (first, second) ← minimalSpan node
    let mut newLayer := currentLayer
    let mut idx := currentLayer - first + 1
    while idx < currentLayer + second do
      if !(idx < 0 || idx.toNat >= filling.size) then
        if filling[idx.toNat]! < filling[newLayer.toNat]! then
          newLayer := idx
      idx := idx + 1
    if newLayer != currentLayer && filling[newLayer.toNat]! < filling[currentLayer.toNat]! then
      filling := filling.modify currentLayer.toNat (· - 1)
      filling := filling.modify newLayer.toNat (· + 1)
      modifyNode node fun n => { n with layer := newLayer }

/-- Removes `edge` from the outgoing (`outgoing = true`) or incoming edges of `node`. -/
private def removeEdgeFromNode (node : NNodeId) (edge : NEdgeId) (outgoing : Bool) : NetworkSimplexM ο Unit :=
  modifyNode node fun n =>
    if outgoing then { n with outgoingEdges := n.outgoingEdges.filter (· != edge) }
    else { n with incomingEdges := n.incomingEdges.filter (· != edge) }

/-- Appends `edge` to the outgoing (`outgoing = true`) or incoming edges of `node`. -/
private def addEdgeToNode (node : NNodeId) (edge : NEdgeId) (outgoing : Bool) : NetworkSimplexM ο Unit :=
  modifyNode node fun n =>
    if outgoing then { n with outgoingEdges := n.outgoingEdges.push edge }
    else { n with incomingEdges := n.incomingEdges.push edge }

/-- `removeSubtrees()`: repeatedly removes leaves (nodes with exactly one
connected edge) from `nodeList`, detaching the edge from the remaining
neighbour. Leaves are processed in FIFO order; the survivors keep their order
and the removed `(node, edge)` pairs are stacked for `reattachSubtrees`. -/
def removeSubtrees : NetworkSimplexM ο Unit := do
  let order := (← get).graph.nodeList
  let mut leafs : Array NNodeId := #[]
  for node in order do
    if (← getNode node).connectedEdgeCount == 1 then
      leafs := leafs.push node
  let mut stack : Array (NNodeId × NEdgeId) := #[]
  let mut removed : Array Bool := Array.replicate (← get).graph.nodes.size false
  let mut head := 0
  while head < leafs.size do
    let node := leafs[head]!
    head := head + 1
    let nd ← getNode node
    if nd.connectedEdgeCount == 0 then
      continue
    -- first connected edge: incoming first, then outgoing (Java parity)
    let isOutEdge := nd.incomingEdges.isEmpty
    let edge := if !nd.incomingEdges.isEmpty then nd.incomingEdges[0]! else nd.outgoingEdges[0]!
    let other ← (← getEdge edge).other node
    if isOutEdge then
      removeEdgeFromNode other edge false
    else
      removeEdgeFromNode other edge true
    if (← getNode other).connectedEdgeCount == 1 then
      leafs := leafs.push other
    stack := stack.push (node, edge)
    removed := removed.set! node.idx true
  -- compact once, preserving the survivor order
  modify fun s => { s with
    graph := { s.graph with nodeList := s.graph.nodeList.filter fun n => !removed[n.idx]! }
    subtreeNodesStack := some stack }

/-- `reattachSubtrees()`: re-attaches the removed subtree nodes in reverse
removal order, placing each at minimal distance (`delta`) from its neighbour and
appending it to `nodeList`. -/
def reattachSubtrees : NetworkSimplexM ο Unit := do
  let some stack := (← get).subtreeNodesStack | return
  modify fun s => { s with subtreeNodesStack := some #[] }
  let mut i := stack.size
  while i > 0 do
    i := i - 1
    let (node, edge) := stack[i]!
    let ed ← getEdge edge
    let placed ← ed.other node
    if ed.target == node then
      addEdgeToNode placed edge true
      let layer := (← getNode placed).layer + ed.delta
      modifyNode node fun n => { n with layer := layer }
    else
      addEdgeToNode placed edge false
      let layer := (← getNode placed).layer - ed.delta
      modifyNode node fun n => { n with layer := layer }
    modify fun s => { s with graph := { s.graph with nodeList := s.graph.nodeList.push node } }

/-- `execute(IElkProgressMonitor)` (Rust `execute_with_monitor`) on the monad
state: determines the optimal layering and stores it in `NNode.layer`. -/
def executeWithMonitor (monitor : ProgressMonitor) : NetworkSimplexM ο Unit := do
  let _ ← monitor.begin "Network simplex" 1.0
  if (← get).graph.nodeList.isEmpty then
    monitor.done
    return
  -- reset any old layering
  for node in (← get).graph.nodeList do
    modifyNode node fun n => { n with layer := 0 }
  let doRemoveSubtrees := (← get).graph.nodeList.size >= REMOVE_SUBTREES_THRESH
  if doRemoveSubtrees then
    removeSubtrees
  initState
  feasibleTree
  let mut leaveOpt := leaveEdge (← get)
  let mut iter : Int := 0
  while true do
    let some leaveId := leaveOpt | break
    if iter >= (← get).iterationLimit then
      break
    match enterEdge (← get) leaveId with
    | some enterId => exchange leaveId enterId
    | none => break -- Rust prints a diagnostic under `ELK_TRACE_NETWORK_SIMPLEX` (not ported)
    leaveOpt := leaveEdge (← get)
    iter := iter + 1
  -- publish the dense layers once, before the subtree and balancing passes
  let order := (← get).graph.nodeList
  for h : nid in [0:order.size] do
    let layer := (← get).nLayer[nid]!
    modifyNode order[nid] fun n => { n with layer := layer }
  if doRemoveSubtrees then
    reattachSubtrees
  if (← get).balance then
    let filling ← normalize
    balanceLayers filling
  else
    let _ ← normalize
  dispose
  monitor.done

/-- `execute(IElkProgressMonitor)`: runs the network simplex and returns the
graph with `NNode.layer` assigned (and `nodeList` reordered if subtrees were
removed, see `removeSubtrees`). -/
def execute (ns : NetworkSimplex ο) (monitor : ProgressMonitor) : IO (NGraph ο) := do
  let ((), s) ← (executeWithMonitor monitor).run ns
  return s.graph

/-- `execute()`: like `execute` with a fresh `BasicProgressMonitor`. -/
def execute' (ns : NetworkSimplex ο) : IO (NGraph ο) := do
  execute ns (← ProgressMonitor.basic)

end NetworkSimplex

end Elk.Alg.Common.NetworkSimplex
