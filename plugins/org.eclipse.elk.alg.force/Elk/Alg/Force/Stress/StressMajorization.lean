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

/-! The Dijkstra priority queue (elk-rs `BinaryHeap<State>`) is a binary heap stored flat in a
`FloatArray` with an explicit entry count `cnt`: entry `i < cnt` is `(h[2i], h[2i+1])` =
(cost, position), slots past `cnt` are stale. Positions are node indices (exact as floats), so entries
need no allocation and the comparisons are the same as on the `State` records. -/

/-- `State::cmp(a, b) == Greater`: `(ac, ap)` is popped before `(bc, bp)` (lower cost first; on a tie
the higher position first). `Float.comparePartial bc ac` spelled out: `.lt` → false, `.gt` → true,
otherwise (equal or NaN) the positions decide. -/
@[inline] private def popsBefore (ac ap bc bp : Float) : Bool :=
  if bc < ac then false else if bc > ac then true else ap > bp

/-- Swaps the heap entries `i` and `j`. -/
@[inline] private def heapSwap (h : FloatArray) (i j : USize) (zero : Float) : FloatArray :=
  let ci := fgetU h (2 * i) zero
  let pi := fgetU h (2 * i + 1) zero
  let cj := fgetU h (2 * j) zero
  let pj := fgetU h (2 * j + 1) zero
  fsetU (fsetU (fsetU (fsetU h (2 * i) cj) (2 * i + 1) pj) (2 * j) ci) (2 * j + 1) pi

/-- `popsBefore` of the heap entries `i` and `j`. -/
@[inline] private def entryBefore (h : FloatArray) (i j : USize) (zero : Float) : Bool :=
  popsBefore (fgetU h (2 * i) zero) (fgetU h (2 * i + 1) zero) (fgetU h (2 * j) zero)
    (fgetU h (2 * j + 1) zero)

/-- Restores the heap property upwards from `i` (tail recursive: the heap array stays unshared and is
swapped in place). -/
private partial def siftUp (h : FloatArray) (i : USize) (zero : Float) : FloatArray :=
  if i == 0 then h
  else
    let p := (i - 1) / 2
    if entryBefore h i p zero then siftUp (heapSwap h i p zero) p zero else h

/-- Restores the heap property downwards from `i` in a heap of `n` entries (same comparisons, in the
same order, as the `while` loop it replaces). -/
private partial def siftDown (h : FloatArray) (n i : USize) (zero : Float) : FloatArray :=
  let l := 2 * i + 1
  let r := l + 1
  let best := if l < n && entryBefore h l i zero then l else i
  let best := if r < n && entryBefore h r best zero then r else best
  if best == i then h else siftDown (heapSwap h i best zero) n best zero

/-- Pushes the entry `(cost, position)` onto a heap of `cnt` entries (which then has `cnt + 1`). -/
@[inline] private def heapPush (heap : FloatArray) (cnt : USize) (cost position zero : Float) :
    FloatArray :=
  let heap := if 2 * cnt < heap.usize then fsetU (fsetU heap (2 * cnt) cost) (2 * cnt + 1) position
    else (heap.push cost).push position
  siftUp heap cnt zero

/-- Removes the top entry (entry 0) of a heap of `cnt > 0` entries (which then has `cnt - 1`). -/
private def heapRemoveTop (heap : FloatArray) (cnt : USize) (zero : Float) : FloatArray :=
  let rest := cnt - 1
  if rest == 0 then heap
  else
    let lastCost := fgetU heap (2 * rest) zero
    let lastPos := fgetU heap (2 * rest + 1) zero
    siftDown (fsetU (fsetU heap 0 lastCost) 1 lastPos) rest 0 zero

/-- State of the relaxation loop: distances, heap and heap entry count. -/
private structure RelaxState where
  dist : FloatArray
  heap : FloatArray
  cnt : USize
  deriving Inhabited

/-- The relaxation loop of `dijkstra_flat` over the adjacency list of `position` (from entry `k`):
unvisited neighbours whose distance improves get the new distance and a heap entry. -/
private partial def relax (row : Array (Nat × Float)) (visited : Array Bool) (position k : Nat)
    (zero : Float) (dist heap : FloatArray) (cnt : USize) : RelaxState :=
  if h : k < row.size then
    let (otherId, edgeLen) := row[k]
    if visited[otherId]! then relax row visited position (k + 1) zero dist heap cnt
    else
      let next := dist.get! position + edgeLen
      if next < dist.get! otherId then
        relax row visited position (k + 1) zero (dist.set! otherId next)
          (heapPush heap cnt next otherId.toFloat zero) (cnt + 1)
      else relax row visited position (k + 1) zero dist heap cnt
  else ⟨dist, heap, cnt⟩

/-- `dijkstra_flat`: shortest path distances from `source` over the adjacency lists. -/
private def dijkstra (adj : Array (Array (Nat × Float))) (n source : Nat) : FloatArray := Id.run do
  let zero : Float := 0.0
  let mut dist := FloatArray.emptyWithCapacity n
  let mut heap := FloatArray.emptyWithCapacity (4 * n)
  let mut cnt : USize := 0
  for i in [0:n] do
    let d := if i == source then 0.0 else Float.posInf
    dist := dist.push d
    heap := heapPush heap cnt d i.toFloat zero
    cnt := cnt + 1
  let mut visited : Array Bool := Array.replicate n false
  while cnt != 0 do
    let cost := fgetU heap 0 zero
    let position := (fgetU heap 1 zero).toUInt64.toNat
    heap := heapRemoveTop heap cnt zero
    cnt := cnt - 1
    if visited[position]! then continue
    visited := visited.set! position true
    if cost > dist.get! position then continue
    let r := relax adj[position]! visited position 0 zero dist heap cnt
    dist := r.dist
    heap := r.heap
    cnt := r.cnt
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

/-- The distance and weight matrices in node list order, flat: `a[i * n + j] = apsp[id_i][id_j]` and
`w[i * n + j] = w[id_i][id_j]` (`id_i` = arena `nodeId` of the `i`-th node), read once per `execute`
so the loops below index rows directly. -/
private def permuted (m : StressMajorization) (nodeIds : Array Nat) (n : Nat) : FloatArray × FloatArray :=
  Id.run do
    let mut a := FloatArray.emptyWithCapacity (n * n)
    let mut w := FloatArray.emptyWithCapacity (n * n)
    for i in [0:n] do
      let ui := nodeIds[i]!
      let aRow := m.apsp[ui]!
      let wRow := m.w[ui]!
      for j in [0:n] do
        let uj := nodeIds[j]!
        a := a.push (aRow.get! uj)
        w := w.push (wRow.get! uj)
    return (a, w)

/-- The pairs `(i, j)`, `j = j0, …, n - 1`, of `compute_stress_soa`, accumulated onto `stress` in loop
order (`row = i * n`, `(xi, yi)` = position of `i`). Tail recursive with unboxed parameters. -/
private partial def stressRow (a w posX posY : FloatArray) (n row : USize) (xi yi zero : Float)
    (j : USize) (stress : Float) : Float :=
  if j >= n then stress
  else
    let dx := xi - fgetU posX j zero
    let dy := yi - fgetU posY j zero
    let eucDist := Float.sqrt (dx * dx + dy * dy)
    let eucDisplacement := eucDist - fgetU a (row + j) zero
    stressRow a w posX posY n row xi yi zero (j + 1)
      (stress + fgetU w (row + j) zero * eucDisplacement * eucDisplacement)

/-- The rows `i, i + 1, …, n - 1` of `compute_stress_soa`. -/
private partial def stressRows (a w posX posY : FloatArray) (n : USize) (zero : Float) (i : USize)
    (stress : Float) : Float :=
  if i >= n then stress
  else
    stressRows a w posX posY n zero (i + 1)
      (stressRow a w posX posY n (i * n) (fgetU posX i zero) (fgetU posY i zero) zero (i + 1) stress)

/-- `compute_stress_soa`: the stress `sum w[i][j] * (|p_i - p_j| - apsp[i][j])^2` over all pairs
`i < j` (matrices in node list order, see `permuted`). -/
def computeStress (a w posX posY : FloatArray) (n : Nat) : Float :=
  stressRows a w posX posY n.toUSize 0.0 0 0.0

/-- The three sums of `compute_new_position_soa`; the float fields are stored unboxed. -/
private structure PositionSums where
  weightSum : Float
  xDisp : Float
  yDisp : Float
  deriving Inhabited

/-- The sums of `compute_new_position_soa` over `j, j + 1, …, n - 1` (skipping `nodeIdx`), accumulated
onto `(weightSum, xDisp, yDisp)` in loop order (`row = nodeIdx * n`). Tail recursive with unboxed
`Float` parameters (a `for` loop would box the three accumulators in its state tuple on every
iteration). -/
private partial def newPositionSums (a w posX posY : FloatArray) (n nodeIdx row : USize)
    (ux uy zero : Float) (useX useY : Bool) (j : USize) (weightSum xDisp yDisp : Float) : PositionSums :=
  if j >= n then ⟨weightSum, xDisp, yDisp⟩
  else if j == nodeIdx then
    newPositionSums a w posX posY n nodeIdx row ux uy zero useX useY (j + 1) weightSum xDisp yDisp
  else
    let vx := fgetU posX j zero
    let vy := fgetU posY j zero
    let wij := fgetU w (row + j) zero
    let weightSum := weightSum + wij
    let dx := ux - vx
    let dy := uy - vy
    let eucDist := Float.sqrt (dx * dx + dy * dy)
    let d := fgetU a (row + j) zero
    let xDisp := if eucDist > zero && useX then xDisp + wij * (vx + d * dx / eucDist) else xDisp
    let yDisp := if eucDist > zero && useY then yDisp + wij * (vy + d * dy / eucDist) else yDisp
    newPositionSums a w posX posY n nodeIdx row ux uy zero useX useY (j + 1) weightSum xDisp yDisp

/-- One Gauss-Seidel sweep of `execute` from node `i` on: every non-fixed node gets the new position
of `compute_new_position_soa` (weighted average of the positions suggested by all other nodes,
restricted by `DIMENSION`), later nodes see the updated positions of earlier ones. -/
private partial def sweep (a w : FloatArray) (fixed : Array Bool) (dim : Dimension) (n : USize)
    (zero : Float) (i : USize) (posX posY : FloatArray) : FloatArray × FloatArray :=
  if i >= n then (posX, posY)
  else if fixed[i.toNat]! then sweep a w fixed dim n zero (i + 1) posX posY
  else
    let ux := fgetU posX i zero
    let uy := fgetU posY i zero
    let useX := match dim with | .y => false | _ => true
    let useY := match dim with | .x => false | _ => true
    let s := newPositionSums a w posX posY n i (i * n) ux uy zero useX useY 0 zero zero zero
    let (nx, ny) : Float × Float := match dim with
      | .x => (s.xDisp / s.weightSum, uy)
      | .y => (ux, s.yDisp / s.weightSum)
      | .xy => (s.xDisp / s.weightSum, s.yDisp / s.weightSum)
    sweep a w fixed dim n zero (i + 1) (fsetU posX i nx) (fsetU posY i ny)

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
  let (a, w) := m.permuted nodeIds n
  let nu := n.toUSize
  let mut count : Int := 0
  let mut prevStress := computeStress a w posX posY n
  let mut curStress := Float.posInf
  while true do
    if count > 0 then prevStress := curStress
    let (posX', posY') := sweep a w fixed m.dim nu 0.0 0 posX posY
    posX := posX'
    posY := posY'
    curStress := computeStress a w posX posY n
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
