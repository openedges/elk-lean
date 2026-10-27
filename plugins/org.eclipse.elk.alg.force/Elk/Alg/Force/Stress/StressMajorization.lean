import Elk.Graph
import Elk.Core.Util.Java
import Elk.Alg.Force.Graph.FGraph
import Elk.Alg.Force.Options.StressOptions
import Elk.Alg.Force.Stress.Dimension
/-!
# `org.eclipse.elk.alg.force.stress.StressMajorization`

Port of `stress_majorization.rs` (elk-rs): stress majorization after Gansner, Koren and North.

`init` computes the all-pairs shortest path matrix `apsp` (Dijkstra from every node over the
undirected edge graph, edge length `DESIRED_EDGE_LENGTH` of the edge or of the graph) and the weights
`w[i][j] = 1 / apsp[i][j]^2` (0 where the distance is 0). Both are indexed by the arena `nodeId`s.

`execute` iterates: every non-`FIXED` node in node list order is moved to the weighted average of the
positions suggested by all other nodes (Gauss-Seidel: later nodes already see the new positions of
earlier ones; `DIMENSION` restricts the update to x or y), until the relative stress decrease drops
below `EPSILON`, the previous stress is 0 or `ITERATION_LIMIT` is reached.

The Rust Dijkstra uses `std::collections::BinaryHeap` ordered by (cost ascending, position descending);
the heap below pops entries in exactly that order, so ties between equally distant nodes are
processed in the same sequence. The `ElkTrace.stress` diagnostics of Rust (stderr only) are not ported.
-/
namespace Elk.Alg.Force.Stress

open Elk.Graph Elk.Core.Util Elk.Alg.Force.Graph Elk.Alg.Force.Options

/-- An entry of the Dijkstra priority queue (elk-rs `State`). -/
private structure HeapEntry where
  cost : Float
  position : Nat
  deriving Inhabited

/-- `State::cmp(a, b) == Greater`: `a` is popped before `b` (lower cost first; on a tie the higher
position first). -/
private def popsBefore (a b : HeapEntry) : Bool :=
  match Float.comparePartial b.cost a.cost with
  | .gt => true
  | .lt => false
  | .eq => a.position > b.position

private def siftUp (heap : Array HeapEntry) (start : Nat) : Array HeapEntry := Id.run do
  let mut h := heap
  let mut i := start
  while i > 0 do
    let p := (i - 1) / 2
    if popsBefore h[i]! h[p]! then
      h := h.swapIfInBounds i p
      i := p
    else
      break
  return h

private def siftDown (heap : Array HeapEntry) : Array HeapEntry := Id.run do
  let mut h := heap
  let n := h.size
  let mut i := 0
  while true do
    let l := 2 * i + 1
    let r := l + 1
    let mut best := i
    if l < n && popsBefore h[l]! h[best]! then best := l
    if r < n && popsBefore h[r]! h[best]! then best := r
    if best == i then break
    h := h.swapIfInBounds i best
    i := best
  return h

private def heapPush (heap : Array HeapEntry) (e : HeapEntry) : Array HeapEntry :=
  siftUp (heap.push e) heap.size

private def heapPop (heap : Array HeapEntry) : Option (HeapEntry × Array HeapEntry) :=
  match heap.back? with
  | none => none
  | some last =>
    let top := heap[0]!
    let rest := heap.pop
    if rest.isEmpty then some (top, rest) else some (top, siftDown (rest.set! 0 last))

/-- `dijkstra_flat`: shortest path distances from `source` over the adjacency lists. -/
private def dijkstra (adj : Array (Array (Nat × Float))) (n source : Nat) : FloatArray := Id.run do
  let mut dist := FloatArray.emptyWithCapacity n
  let mut heap : Array HeapEntry := Array.mkEmpty n
  for i in [0:n] do
    let d := if i == source then 0.0 else Float.posInf
    dist := dist.push d
    heap := heapPush heap { cost := d, position := i }
  let mut visited : Array Bool := Array.replicate n false
  while !heap.isEmpty do
    let some (top, rest) := heapPop heap | break
    heap := rest
    let position := top.position
    if visited[position]! then continue
    visited := visited.set! position true
    if top.cost > dist.get! position then continue
    for (otherId, edgeLen) in adj[position]! do
      if visited[otherId]! then continue
      let next := dist.get! position + edgeLen
      if next < dist.get! otherId then
        dist := dist.set! otherId next
        heap := heapPush heap { cost := next, position := otherId }
  return dist

/-- elk-rs `StressMajorization`: the matrices and options computed by `initialize`. -/
structure StressMajorization where
  apsp : Array FloatArray := #[]
  w : Array FloatArray := #[]
  desiredEdgeLength : Float := 0.0
  dim : Dimension := .xy
  epsilon : Float := 0.0
  iterationLimit : Int := 0

namespace StressMajorization

/-- `StressMajorization::initialize(graph)` (named `init`, `initialize` is a Lean keyword): options, all-pairs shortest paths and weights (a graph
with at most one node leaves the default instance). -/
def init (graph : FGraph) : StressMajorization := Id.run do
  let n := graph.nodes.size
  if n <= 1 then return {}
  let dim := graph.props.getD StressOptions.DIMENSION Dimension.xy
  let iterationLimit := graph.props.getD StressOptions.ITERATION_LIMIT 2147483647
  let epsilon := graph.props.getD StressOptions.EPSILON 0.001
  let desiredEdgeLength := graph.props.getD StressOptions.DESIRED_EDGE_LENGTH 100.0
  let mut adj : Array (Array (Nat × Float)) := Array.replicate n #[]
  for eid in graph.edges do
    let sourceId := (graph.arena.edgeSource[eid.idx]!).map fun nid => graph.arena.nodeId[nid.idx]!
    let targetId := (graph.arena.edgeTarget[eid.idx]!).map fun nid => graph.arena.nodeId[nid.idx]!
    let edgeProps := graph.arena.edgeProperties[eid.idx]!
    let edgeLen :=
      if edgeProps.has StressOptions.DESIRED_EDGE_LENGTH then
        edgeProps.getD StressOptions.DESIRED_EDGE_LENGTH desiredEdgeLength
      else desiredEdgeLength
    if let (some sid, some tid) := (sourceId, targetId) then
      if sid < n then adj := adj.modify sid (·.push (tid, edgeLen))
      if tid < n then adj := adj.modify tid (·.push (sid, edgeLen))
  let mut apsp : Array FloatArray := Array.mkEmpty n
  for sourceId in [0:n] do
    apsp := apsp.push (dijkstra adj n sourceId)
  let mut w : Array FloatArray := Array.mkEmpty n
  for i in [0:n] do
    let mut row := FloatArray.emptyWithCapacity n
    for j in [0:n] do
      let dij := (apsp[i]!).get! j
      row := row.push (if dij != 0.0 then 1.0 / (dij * dij) else 0.0)
    w := w.push row
  return { apsp, w, desiredEdgeLength, dim, epsilon, iterationLimit }

/-- `done(count, prev_stress, cur_stress)`. -/
def done (m : StressMajorization) (count : Int) (prevStress curStress : Float) : Bool :=
  prevStress == 0.0 || ((prevStress - curStress) / prevStress) < m.epsilon || count >= m.iterationLimit

/-- `compute_stress_soa`: the stress `sum w[i][j] * (|p_i - p_j| - apsp[i][j])^2` over all pairs. -/
def computeStress (m : StressMajorization) (posX posY : FloatArray) (nodeIds : Array Nat) (n : Nat) : Float :=
  Id.run do
    let mut stress := 0.0
    for i in [0:n] do
      let ui := nodeIds[i]!
      for j in [i + 1:n] do
        let uj := nodeIds[j]!
        let dx := posX.get! i - posX.get! j
        let dy := posY.get! i - posY.get! j
        let eucDist := Float.sqrt (dx * dx + dy * dy)
        let eucDisplacement := eucDist - (m.apsp[ui]!).get! uj
        stress := stress + (m.w[ui]!).get! uj * eucDisplacement * eucDisplacement
    return stress

/-- The sums of `compute_new_position_soa` over `j, j + 1, …, n - 1` (skipping `nodeIdx`), accumulated
onto `(weightSum, xDisp, yDisp)` in loop order. Tail recursive with unboxed `Float` parameters (a
`for` loop would box the three accumulators in its state tuple on every iteration). -/
private partial def newPositionSums (apspRow wRow posX posY : FloatArray) (nodeIds : Array Nat)
    (nodeIdx n : Nat) (ux uy : Float) (useX useY : Bool) (j : Nat) (weightSum xDisp yDisp : Float) :
    Float × Float × Float :=
  if j >= n then (weightSum, xDisp, yDisp)
  else if j == nodeIdx then
    newPositionSums apspRow wRow posX posY nodeIds nodeIdx n ux uy useX useY (j + 1) weightSum xDisp yDisp
  else
    let vId := nodeIds[j]!
    let vx := posX.get! j
    let vy := posY.get! j
    let wij := wRow.get! vId
    let weightSum := weightSum + wij
    let dx := ux - vx
    let dy := uy - vy
    let eucDist := Float.sqrt (dx * dx + dy * dy)
    let d := apspRow.get! vId
    let xDisp := if eucDist > 0.0 && useX then xDisp + wij * (vx + d * dx / eucDist) else xDisp
    let yDisp := if eucDist > 0.0 && useY then yDisp + wij * (vy + d * dy / eucDist) else yDisp
    newPositionSums apspRow wRow posX posY nodeIds nodeIdx n ux uy useX useY (j + 1) weightSum xDisp yDisp

/-- `compute_new_position_soa`: the new position of node `nodeIdx` (weighted average of the positions
suggested by all other nodes, restricted by `DIMENSION`). -/
def computeNewPosition (m : StressMajorization) (posX posY : FloatArray) (nodeIds : Array Nat)
    (nodeIdx n : Nat) : Float × Float :=
  let uId := nodeIds[nodeIdx]!
  let ux := posX.get! nodeIdx
  let uy := posY.get! nodeIdx
  let (weightSum, xDisp, yDisp) :=
    newPositionSums (m.apsp[uId]!) (m.w[uId]!) posX posY nodeIds nodeIdx n ux uy
      (m.dim != Dimension.y) (m.dim != Dimension.x) 0 0.0 0.0 0.0
  match m.dim with
  | .x => (xDisp / weightSum, uy)
  | .y => (ux, yDisp / weightSum)
  | .xy => (xDisp / weightSum, yDisp / weightSum)

/-- `StressMajorization::execute(graph)`: iterates until `done`, then stores the positions in the
graph (nodes with `StressOptions.FIXED` keep their position). -/
def execute (m : StressMajorization) (graph : FGraph) : FGraph := Id.run do
  let n := graph.nodes.size
  if n <= 1 then return graph
  let mut posX := FloatArray.emptyWithCapacity n
  let mut posY := FloatArray.emptyWithCapacity n
  let mut nodeIds : Array Nat := Array.mkEmpty n
  let mut fixed : Array Bool := Array.mkEmpty n
  for nid in graph.nodes do
    let pos := graph.arena.nodePosition[nid.idx]!
    posX := posX.push pos.x
    posY := posY.push pos.y
    nodeIds := nodeIds.push (graph.arena.nodeId[nid.idx]!)
    fixed := fixed.push ((graph.arena.nodeProperties[nid.idx]!).getD StressOptions.FIXED false)
  let mut count : Int := 0
  let mut prevStress := m.computeStress posX posY nodeIds n
  let mut curStress := Float.posInf
  while true do
    if count > 0 then prevStress := curStress
    for i in [0:n] do
      if fixed[i]! then continue
      let (nx, ny) := m.computeNewPosition posX posY nodeIds i n
      posX := posX.set! i nx
      posY := posY.set! i ny
    curStress := m.computeStress posX posY nodeIds n
    if m.done count prevStress curStress then break
    count := count + 1
  let mut arena := graph.arena
  for i in [0:n] do
    let nid := graph.nodes[i]!
    arena := { arena with nodePosition := arena.nodePosition.modify nid.idx fun p =>
      { p with x := posX.get! i, y := posY.get! i } }
  return { graph with arena }

end StressMajorization

end Elk.Alg.Force.Stress
