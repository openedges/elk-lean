import Tests.Framework
import Tests.Layered.P3Counting
import Elk.Alg.Layered
import Elk.Alg.Layered.P3Order.PortDistributors
import Elk.Alg.Layered.P3Order.Heuristics
/-!
Tests of the `p3order` crossing minimisation heuristics (`BarycenterHeuristic`,
`ModelOrderBarycenterHeuristic`, elk-rs `MedianHeuristic`), `SweepCopy` and elk-rs `RandomTrace`,
ported from elk-rs `tests/p3_order/{barycenter_heuristic_test,model_order_barycenter_heuristic_test}.rs`
(check names are the Rust test names), plus hand-derived checks ("hand: …"). The graph builders
are the `Tests.Layered.P3Counting` ones with the barycenter test configuration (self layout
units, `FIXED_SIDE` ports, graph property flags, full north/south bookkeeping).

Random draws used by the hand checks (`Random(0)`, `java.util.Random` values):
`nextFloat`: 0.73096776, 0.831441, 0.24053639, 0.6063452;
`nextDouble`: 0.730967787376657, 0.24053641567148587, 0.6374174253501083.
The perturbation of a draw `f` is `f32(f32(f * 0.07f) - 0.035f)`, i.e. 0.016167745, 0.02320087,
-0.018162454, 0.007444162 for the four floats above.
-/
namespace Tests.Layered.P3Heuristics

open Tests Elk.Graph Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open Elk.Alg.Layered.P3Order Elk.Alg.Layered.P3Order.Counting Elk.Alg.Layered.Intermediate.Preserveorder
open Tests.Layered.P3Counting (Cfg newGraph makeLayer addNode addNodes addPort connect eastWestEdgeFromTo
  addInLayerEdge setFixedOrderConstraint setAsLongEdgeDummy addNorthSouthEdge assignIds nodeArray runL)
open LayeredM

/-! ## Builders and helpers -/

/-- The helpers of `barycenter_heuristic_test.rs`. -/
def bCfg : Cfg := { selfUnit := true, fixSide := true, graphProps := true, full := true }

/-- `Random(0)` draws (see the module doc). -/
def F1 : Float := 0.730967760086059570
def F2 : Float := 0.831440985202789307
def F3 : Float := 0.240536391735076904
def F4 : Float := 0.606345176696777344
def D1 : Float := 0.730967787376657019
def D2 : Float := 0.240536415671485870
def D3 : Float := 0.637417425350108258

/-- The perturbation of a `nextFloat` draw. -/
def pert (f : Float) : Float :=
  let ra := Float.toF32 0.07
  Float.toF32 (Float.toF32 (f * ra) - Float.toF32 (ra / 2.0))

/-- `Random(seed)` advanced by `n` `nextFloat`s. -/
def afterFloats (seed : Int) (n : Nat) : Random := Id.run do
  let mut r := Random.ofInt seed
  for _ in [0:n] do r := r.nextFloat.2
  return r

/-- `create_heuristic(node_order, _)`: a node-relative distributor and a resolver initialised
together, then the heuristic initialised (which re-initialises the resolver, as in Rust). -/
def createHeuristic (order : Array (Array LNodeId)) : LayeredM BarycenterHeuristic := do
  let d ← NodeRelativePortDistributor.new order.size
  let r ← ForsterConstraintResolver.new order false
  Initializable.init #[d.initializable, r.initializable] order
  let h ← BarycenterHeuristic.new r d.toBarycenterPortDistributor
  Initializable.init #[h.initializable] order
  return h

/-- `create_heuristic` of `model_order_barycenter_heuristic_test.rs`. -/
def createModelOrderHeuristic (order : Array (Array LNodeId)) (force : Bool := true) (maxNodes : Int := 0)
    (strategy : GroupOrderStrategy := .onlyWithinGroup) (locked : Option LGraphId := none) :
    LayeredM ModelOrderBarycenterHeuristic := do
  let d ← NodeRelativePortDistributor.new order.size
  let r ← ForsterConstraintResolver.new order false
  Initializable.init #[d.initializable, r.initializable] order
  let h ← ModelOrderBarycenterHeuristic.new r d.toBarycenterPortDistributor force maxNodes strategy locked
  Initializable.init #[h.initializable] order
  return h

/-- `relative_index_order(actual, reference)`. -/
def relativeIndexOrder (actual reference : Array LNodeId) : Array Nat :=
  actual.map fun n => (reference.findIdx? (· == n)).getD 999

/-- The barycenters of nodes. -/
def barysOf (h : BarycenterHeuristic) (nodes : Array LNodeId) : LayeredM (Array (Option Float)) :=
  nodes.mapM h.getBarycenter

/-- Absolute tolerance of the hand checks. -/
def eps : Float := 1e-12

/-- `checkFloat` on an optional value. -/
def checkBary (name : String) (actual : Option Float) (expected : Float) : TestM Unit :=
  match actual with
  | some v => checkFloat name v expected eps
  | none => report name false "expected a barycenter, got none"

/-! ## `barycenter_heuristic_test.rs` -/

/-- `minimize_crossings_removes_crossing_in_simple_cross`. -/
def tSimpleCross : LayeredM Bool := do
  let g ← newGraph bCfg
  let left ← makeLayer g
  let right ← makeLayer g
  let ln ← addNodes bCfg g left 2
  let rn ← addNodes bCfg g right 2
  eastWestEdgeFromTo bCfg ln[0]! rn[1]!
  eastWestEdgeFromTo bCfg ln[1]! rn[0]!
  let _ ← assignIds g
  let order ← nodeArray g
  let expected := order[1]!.swapIfInBounds 0 1
  let h ← createHeuristic order
  let (order, _) ← h.minimizeCrossings order 1 true true (← IO.mkRef (Random.ofInt 1))
  return order[1]! == expected

/-- One run of `randomize_first_layer_can_keep_or_swap_order`: whether the first layer kept (`true`)
or swapped (`false`) its order, `none` otherwise. -/
def randomizeFirstLayerRun (seed : Int) : LayeredM (Option Bool) := do
  let g ← newGraph bCfg
  let left ← makeLayer g
  let right ← makeLayer g
  let ln ← addNodes bCfg g left 2
  let rn ← addNodes bCfg g right 2
  eastWestEdgeFromTo bCfg ln[0]! rn[1]!
  eastWestEdgeFromTo bCfg ln[1]! rn[0]!
  let _ ← assignIds g
  let order ← nodeArray g
  let h ← createHeuristic order
  let (order', _) ← h.setFirstLayerOrder order true (← IO.mkRef (Random.ofInt seed))
  if order'[0]! == order[0]! then return some true
  if order'[0]! == order[0]!.swapIfInBounds 0 1 then return some false
  return none

/-- `randomize_first_layer_can_keep_or_swap_order` (seeds `0..128`). -/
def tRandomizeFirstLayer : IO (Bool × Bool) := do
  let mut sawOriginal := false
  let mut sawSwitched := false
  for seed in [0:128] do
    match ← runL (randomizeFirstLayerRun seed) with
    | some true => sawOriginal := true
    | some false => sawSwitched := true
    | none => pure ()
    if sawOriginal && sawSwitched then break
  return (sawOriginal, sawSwitched)

/-- `fixed_port_order_crossing_backwards`. -/
def tFixedPortOrderBackwards : LayeredM Bool := do
  let g ← newGraph bCfg
  let left ← makeLayer g
  let right ← makeLayer g
  let ln ← addNodes bCfg g left 2
  let rightNode ← addNode bCfg g right
  eastWestEdgeFromTo bCfg ln[0]! rightNode
  eastWestEdgeFromTo bCfg ln[1]! rightNode
  setFixedOrderConstraint bCfg rightNode
  let _ ← assignIds g
  let order ← nodeArray g
  let expected := order[0]!.swapIfInBounds 0 1
  let h ← createHeuristic order
  let (order, _) ← h.minimizeCrossings order 0 false true (← IO.mkRef (Random.ofInt 1))
  return order[0]! == expected

/-- `in_layer_edges_reorder_nodes`; also returns the three barycenters. -/
def tInLayerEdges : LayeredM (Bool × Array (Option Float)) := do
  let g ← newGraph bCfg
  let left ← makeLayer g
  let right ← makeLayer g
  let leftNode ← addNode bCfg g left
  let rn ← addNodes bCfg g right 3
  setFixedOrderConstraint bCfg rn[0]!
  eastWestEdgeFromTo bCfg leftNode rn[0]!
  addInLayerEdge bCfg rn[0]! rn[2]! .west
  eastWestEdgeFromTo bCfg leftNode rn[1]!
  let _ ← assignIds g
  let order ← nodeArray g
  let expected := #[order[1]![2]!, order[1]![0]!, order[1]![1]!]
  let h ← createHeuristic order
  let (order', _) ← h.minimizeCrossings order 1 true true (← IO.mkRef (Random.ofInt 1))
  return (order'[1]! == expected, ← barysOf h order[1]!)

/-- `north_south_edges_reorder_nodes`: the relative order of the middle layer. -/
def tNorthSouthEdges : LayeredM (Array Nat) := do
  let g ← newGraph bCfg
  let left ← makeLayer g
  let middle ← makeLayer g
  let right ← makeLayer g
  let ln ← addNodes bCfg g left 1
  let mn ← addNodes bCfg g middle 4
  let rn ← addNodes bCfg g right 3
  eastWestEdgeFromTo bCfg ln[0]! mn[2]!
  eastWestEdgeFromTo bCfg mn[2]! rn[2]!
  setAsLongEdgeDummy mn[2]!
  addNorthSouthEdge bCfg .north mn[3]! mn[0]! rn[0]! false
  addNorthSouthEdge bCfg .north mn[3]! mn[1]! rn[1]! false
  let _ ← assignIds g
  let order ← nodeArray g
  let initial := order[1]!
  let h ← createHeuristic order
  let (order, _) ← h.minimizeCrossings order 1 true true (← IO.mkRef (Random.ofInt 17))
  return relativeIndexOrder order[1]! initial

/-- `filling_in_unknown_barycenters`: middle layer kept, right layer switched. -/
def tFillingInUnknown : LayeredM (Bool × Bool) := do
  let g ← newGraph bCfg
  let left ← makeLayer g
  let middle ← makeLayer g
  let right ← makeLayer g
  let leftNode ← addNode bCfg g left
  let mn ← addNodes bCfg g middle 2
  let rn ← addNodes bCfg g right 2
  eastWestEdgeFromTo bCfg mn[0]! rn[1]!
  eastWestEdgeFromTo bCfg mn[1]! rn[0]!
  eastWestEdgeFromTo bCfg leftNode mn[1]!
  let _ ← assignIds g
  let order ← nodeArray g
  let expectedRight := order[2]!.swapIfInBounds 0 1
  let expectedMiddle := order[1]!
  let h ← createHeuristic order
  let random ← IO.mkRef (Random.ofInt 1)
  let (order, _) ← h.minimizeCrossings order 0 true true random
  let (order, _) ← h.minimizeCrossings order 1 true false random
  let middleOk := order[1]! == expectedMiddle
  let (order, _) ← h.minimizeCrossings order 2 true false random
  return (middleOk, order[2]! == expectedRight)

/-- `fixed_port_order_crossing_independent_of_random_seed`. -/
def tFixedPortOrderSeeds : LayeredM (Bool × Bool) := do
  let g ← newGraph bCfg
  let left ← makeLayer g
  let right ← makeLayer g
  let leftNode ← addNode bCfg g left
  let rightTop ← addNode bCfg g right
  let rightBottom ← addNode bCfg g right
  eastWestEdgeFromTo bCfg leftNode rightBottom
  eastWestEdgeFromTo bCfg leftNode rightTop
  setFixedOrderConstraint bCfg leftNode
  let _ ← assignIds g
  let order ← nodeArray g
  let expected := order[1]!.swapIfInBounds 0 1
  let h ← createHeuristic order
  let (order, _) ← h.minimizeCrossings order 1 true true (← IO.mkRef (Random.ofInt 1))
  let first := order[1]! == expected
  let (order, _) ← h.minimizeCrossings order 1 true true (← IO.mkRef (Random.ofInt 999))
  return (first, order[1]! == expected)

def rustBarycenterTests : Suite := suite "layered.p3order.barycenter_heuristic" do
  check "minimize_crossings_removes_crossing_in_simple_cross" (← runL tSimpleCross)
  let (sawOriginal, sawSwitched) ← tRandomizeFirstLayer
  check "randomize_first_layer_can_keep_or_swap_order (kept)" sawOriginal
  check "randomize_first_layer_can_keep_or_swap_order (swapped)" sawSwitched
  check "fixed_port_order_crossing_backwards" (← runL tFixedPortOrderBackwards)
  let (ok, barys) ← runL tInLayerEdges
  check "in_layer_edges_reorder_nodes" ok
  -- hand: Random(1) perturbations q1, q2, q3; r0 = 1/3 + q1, r1 = 2/3 + q2, r2 inherits r0's sum + q3
  let r1 := Random.ofInt 1
  let (g1, r1) := r1.nextFloat
  let (g2, r1) := r1.nextFloat
  let (g3, _) := r1.nextFloat
  let third := Float.toF32 (1.0 / 3.0)
  checkBary "in_layer_edges_reorder_nodes r0 (hand: f32(1/3) + q1)" barys[0]! (third + pert g1)
  checkBary "in_layer_edges_reorder_nodes r1 (hand: f32(2/3) + q2)" barys[1]! (Float.toF32 (2.0 / 3.0) + pert g2)
  checkBary "in_layer_edges_reorder_nodes r2 (hand: f32(1/3) + q1 + q3)" barys[2]! (third + pert g1 + pert g3)
  checkEqR "north_south_edges_reorder_nodes (Rust: [2, 1, 0, 3])" (← runL tNorthSouthEdges) #[2, 1, 0, 3]
  let (middleOk, rightOk) ← runL tFillingInUnknown
  check "filling_in_unknown_barycenters (middle kept)" middleOk
  check "filling_in_unknown_barycenters (right switched)" rightOk
  let (first, second) ← runL tFixedPortOrderSeeds
  check "fixed_port_order_crossing_independent_of_random_seed (seed 1)" first
  check "fixed_port_order_crossing_independent_of_random_seed (seed 999)" second

/-! ## Hand-derived barycenter checks -/

/-- Two layers `[a, b, c]` → `[x, y, z]` with edges `a→z`, `b→y`, `c→x`, `a→y` (ports in that
order). Forward ranks of the left layer (node-relative): `a`: 1/3, 2/3; `b`: 1.5; `c`: 2.5. -/
def twoLayerGraph : LayeredM (LGraphId × Array LNodeId × Array LNodeId) := do
  let g ← newGraph bCfg
  let left ← makeLayer g
  let right ← makeLayer g
  let ln ← addNodes bCfg g left 3
  let rn ← addNodes bCfg g right 3
  eastWestEdgeFromTo bCfg ln[0]! rn[2]!
  eastWestEdgeFromTo bCfg ln[1]! rn[1]!
  eastWestEdgeFromTo bCfg ln[2]! rn[0]!
  eastWestEdgeFromTo bCfg ln[0]! rn[1]!
  let _ ← assignIds g
  return (g, ln, rn)

/-- Forward sweep on the right layer with `Random(0)`, lock or snapshot path. -/
def hForward (snapshot : Bool) (scrambleIds : Bool := false) :
    LayeredM (Array LNodeId × Array LNodeId × Array (Option Float) × Random) := do
  let (g, _, rn) ← twoLayerGraph
  let order ← nodeArray g
  let h ← createHeuristic order
  if snapshot then
    h.setSnapshot (← CrossMinSnapshot.build order 8)
    if scrambleIds then
      for layer in order do
        for n in layer do modifyNode n fun x => { x with id := 77 }
  let random ← IO.mkRef (Random.ofInt 0)
  let (order', improved) ← h.minimizeCrossings order 1 true true random
  return (rn, if improved then #[] else order'[1]!, ← barysOf h rn, ← random.get)

/-- Backward sweep on the left layer of `twoLayerGraph` (input ranks of the right layer:
`x`: 0.5; `y`: f32(5/3), f32(4/3); `z`: 2.5). -/
def hBackward : LayeredM (Array LNodeId × Array LNodeId × Array (Option Float)) := do
  let (g, ln, _) ← twoLayerGraph
  let order ← nodeArray g
  let h ← createHeuristic order
  let (order', _) ← h.minimizeCrossings order 0 false true (← IO.mkRef (Random.ofInt 0))
  return (ln, order'[0]!, ← barysOf h ln)

/-- `[a]` → `[u, v, w]` with only `a→v`: `u` and `w` have no barycenter and are filled in. -/
def hFillIn (isFirstSweep : Bool) : LayeredM (Array LNodeId × Array LNodeId × Array (Option Float) × Random) := do
  let g ← newGraph bCfg
  let left ← makeLayer g
  let right ← makeLayer g
  let a ← addNode bCfg g left
  let rn ← addNodes bCfg g right 3
  eastWestEdgeFromTo bCfg a rn[1]!
  let _ ← assignIds g
  let order ← nodeArray g
  let h ← createHeuristic order
  let random ← IO.mkRef (Random.ofInt 0)
  let (order', _) ← h.minimizeCrossings order 1 true isFirstSweep random
  return (rn, order'[1]!, ← barysOf h rn, ← random.get)

/-- `setFirstLayerOrder` on three unconnected nodes with `Random(0)`, forward or backward. -/
def hRandomize (forward : Bool) : LayeredM (Array LNodeId × Array LNodeId × Array (Option BarycenterState)) := do
  let g ← newGraph bCfg
  let l0 ← makeLayer g
  let l1 ← makeLayer g
  let n0 ← addNodes bCfg g l0 3
  let n1 ← addNodes bCfg g l1 3
  let _ ← assignIds g
  let order ← nodeArray g
  let h ← createHeuristic order
  let (order', improved) ← h.setFirstLayerOrder order forward (← IO.mkRef (Random.ofInt 0))
  let nodes := if forward then n0 else n1
  let result := if improved then #[] else order'[if forward then 0 else 1]!
  return (nodes, result, ← nodes.mapM h.stateOf)

/-- `[a, b]` → `[x, y]` with `a→y`, `b→x` (barycenters x ≈ 1.5, y ≈ 0.5) and the successor
constraint `x → y`, without layout units: the resolver merges `x` and `y`. -/
def hSuccessorConstraint : LayeredM (Array LNodeId × Array LNodeId × Array (Option Float)) := do
  let c : Cfg := { fixSide := true }
  let g ← newGraph c
  let left ← makeLayer g
  let right ← makeLayer g
  let ln ← addNodes c g left 2
  let rn ← addNodes c g right 2
  eastWestEdgeFromTo c ln[0]! rn[1]!
  eastWestEdgeFromTo c ln[1]! rn[0]!
  modifyNode rn[0]! fun x => { x with internal := { x.internal with inLayerSuccessorConstraints := #[rn[1]!] } }
  let _ ← assignIds g
  let order ← nodeArray g
  let h ← createHeuristic order
  let (order', _) ← h.minimizeCrossings order 1 true true (← IO.mkRef (Random.ofInt 0))
  return (rn, order'[1]!, ← barysOf h rn)

/-- The first layer of a forward sweep: no ranks are computed (they stay those of the
initialisation) and the nodes without predecessors are filled in. -/
def hFirstLayer : LayeredM (Array Float × Array LNodeId × Array LNodeId × Array (Option Float)) := do
  let (g, ln, _) ← twoLayerGraph
  let order ← nodeArray g
  let h ← createHeuristic order
  let (order', _) ← h.minimizeCrossings order 0 true true (← IO.mkRef (Random.ofInt 0))
  return (← h.portRanks.get, ln, order'[0]!, ← barysOf h ln)

/-- The record view and the sweep iteration counter. -/
def hRecord : LayeredM (Bool × Bool × Bool × Nat × Nat) := do
  let (g, _, _) ← twoLayerGraph
  let order ← nodeArray g
  let h ← createHeuristic order
  let rec_ := h.toHeuristic (← IO.mkRef (Random.ofInt 0))
  let (_, improved) ← rec_.minimizeCrossings order 1 true true
  rec_.incrementSweepIteration
  rec_.incrementSweepIteration
  let afterIncrement ← h.sweepIteration.get
  rec_.resetSweepIteration
  return (← rec_.isDeterministic, ← rec_.alwaysImproves, improved, afterIncrement, ← h.sweepIteration.get)

def handBarycenterTests : Suite := suite "layered.p3order.barycenter_heuristic.hand" do
  checkFloat "RANDOM_AMOUNT = 0.07f" BarycenterHeuristic.RANDOM_AMOUNT 0.070000000298023224 0.0
  checkFloat "perturbation of Random(0).nextFloat() #1 (hand: 0.73096776 * 0.07 - 0.035)" (pert F1) 0.016167744994163513 0.0
  let third := Float.toF32 (1.0 / 3.0)
  let twoThirds := Float.toF32 (2.0 / 3.0)
  -- forward, lock path
  let (rn, result, barys, rnd) ← runL (hForward false)
  checkBary "forward x (hand: c's rank 2.5 + p1)" barys[0]! (2.5 + pert F1)
  checkBary "forward y (hand: (b's 1.5 + a's f32(2/3) + p2) / 2)" barys[1]! ((1.5 + twoThirds + pert F2) / 2.0)
  checkBary "forward z (hand: a's f32(1/3) + p3)" barys[2]! (third + pert F3)
  check "forward order (hand: [z, y, x])" (result == #[rn[2]!, rn[1]!, rn[0]!])
  checkEq "forward draws one nextFloat per node (hand: 3)" rnd.seed (afterFloats 0 3).seed
  -- forward, snapshot path: same values
  let (rn', result', barys', rnd') ← runL (hForward true)
  check "snapshot path order equals the lock path (hand: [z, y, x])" (result' == #[rn'[2]!, rn'[1]!, rn'[0]!])
  checkEqR "snapshot path barycenters equal the lock path" barys' barys
  checkEq "snapshot path draws the same numbers" rnd'.seed rnd.seed
  let (rn'', result'', barys'', _) ← runL (hForward true (scrambleIds := true))
  check "snapshot path uses the captured ids (live ids scrambled)" (result'' == #[rn''[2]!, rn''[1]!, rn''[0]!])
  checkEqR "snapshot path barycenters with scrambled live ids" barys'' barys
  -- backward
  let (ln, result, barys) ← runL hBackward
  checkBary "backward a (hand: (z's 2.5 + y's f32(4/3) + p1) / 2)" barys[0]! ((2.5 + Float.toF32 (4.0 / 3.0) + pert F1) / 2.0)
  checkBary "backward b (hand: y's f32(5/3) + p2)" barys[1]! (Float.toF32 (5.0 / 3.0) + pert F2)
  checkBary "backward c (hand: x's 0.5 + p3)" barys[2]! (0.5 + pert F3)
  check "backward order (hand: [c, b, a])" (result == #[ln[2]!, ln[1]!, ln[0]!])
  -- fill in, not pre-ordered (first sweep): random placement
  let (rn, result, barys, rnd) ← runL (hFillIn true)
  let v := 0.5 + pert F1
  checkBary "fill-in v computed (hand: 0.5 + p1)" barys[1]! v
  checkBary "fill-in u random (hand: F2 * (v + 2) - 1)" barys[0]! (F2 * (v + 2.0) - 1.0)
  checkBary "fill-in w random (hand: F3 * (v + 2) - 1)" barys[2]! (F3 * (v + 2.0) - 1.0)
  check "fill-in order (hand: [w, v, u])" (result == #[rn[2]!, rn[1]!, rn[0]!])
  checkEq "fill-in draws 1 + 2 nextFloats" rnd.seed (afterFloats 0 3).seed
  -- fill in, pre-ordered
  let (rn, result, barys, rnd) ← runL (hFillIn false)
  checkBary "pre-ordered u (hand: (-1 + v) / 2)" barys[0]! ((-1.0 + v) / 2.0)
  checkBary "pre-ordered w (hand: (v + (v + 1)) / 2)" barys[2]! ((v + (v + 1.0)) / 2.0)
  check "pre-ordered order kept (hand: [u, v, w])" (result == rn)
  checkEq "pre-ordered fill-in draws nothing (hand: 1 draw for v)" rnd.seed (afterFloats 0 1).seed
  -- randomize (setFirstLayerOrder)
  let (nodes, result, states) ← runL (hRandomize true)
  check "setFirstLayerOrder forward (hand: nextDouble 0.731, 0.2405, 0.637 → [b, c, a])"
    (result == #[nodes[1]!, nodes[2]!, nodes[0]!])
  checkBary "randomized barycenter a (hand: D1)" (states[0]!.bind (·.barycenter)) D1
  checkBary "randomized summed weight c (hand: D3)" ((states[2]!).map (·.summedWeight)) D3
  checkEqR "randomized degrees (hand: 1)" (states.map fun s => (s.map (·.degree)).getD 0) #[1, 1, 1]
  let (nodes, result, _) ← runL (hRandomize false)
  check "setFirstLayerOrder backward orders the last layer (hand: [b, c, a])"
    (result == #[nodes[1]!, nodes[2]!, nodes[0]!])
  -- successor constraint resolved by the Forster resolver
  let (rn, result, barys) ← runL hSuccessorConstraint
  check "successor constraint x → y keeps x first (hand: [x, y])" (result == rn)
  let merged := ((1.5 + pert F1) + (0.5 + pert F2)) / 2.0
  checkBary "merged barycenter x (hand: ((1.5 + p1) + (0.5 + p2)) / 2)" barys[0]! merged
  checkBary "merged barycenter y (hand: same)" barys[1]! merged
  -- first layer
  let (ranks, ln, result, barys) ← runL hFirstLayer
  checkEqR "first layer: no ranks computed (hand: all 0)" ranks (Array.replicate 8 0.0)
  checkBary "first layer a filled in (hand: F1 * 2 - 1)" barys[0]! (F1 * 2.0 - 1.0)
  checkBary "first layer b filled in (hand: F2 * 2 - 1)" barys[1]! (F2 * 2.0 - 1.0)
  checkBary "first layer c filled in (hand: F3 * 2 - 1)" barys[2]! (F3 * 2.0 - 1.0)
  check "first layer order (hand: [c, a, b])" (result == #[ln[2]!, ln[0]!, ln[1]!])
  let (deterministic, always, improved, afterIncrement, afterReset) ← runL hRecord
  check "toHeuristic: not deterministic, never always improving, no improvement reported"
    (!deterministic && !always && !improved)
  checkEq "sweep iteration incremented twice, then reset" (afterIncrement, afterReset) (2, 0)

/-! ## `model_order_barycenter_heuristic_test.rs` and hand checks -/

/-- `create_graph()` of the Rust test with node model orders `[2, 0, 1]` on the right. -/
def tModelOrderRespected : LayeredM Bool := do
  let c : Cfg := { selfUnit := true, fixSide := true }
  let g ← newGraph c
  setGraphProp g LayeredOptions.CONSIDER_MODEL_ORDER_STRATEGY OrderingStrategy.nodesAndEdges
  setGraphProp g LayeredOptions.CROSSING_MINIMIZATION_FORCE_NODE_MODEL_ORDER true
  let left ← makeLayer g
  let right ← makeLayer g
  let ln ← addNodes c g left 3
  let rn ← addNodes c g right 3
  for (n, mo) in rn.zip #[2, 0, 1] do
    modifyNode n fun x => { x with internal := { x.internal with modelOrder := some mo } }
  eastWestEdgeFromTo c ln[0]! rn[1]!
  eastWestEdgeFromTo c ln[1]! rn[2]!
  eastWestEdgeFromTo c ln[2]! rn[0]!
  let _ ← assignIds g
  let order ← nodeArray g
  let h ← createModelOrderHeuristic order
  let (order, _) ← h.minimizeCrossings order 1 true true (← IO.mkRef (Random.ofInt 7))
  let mut modelOrder : Int := -1
  for n in order[1]! do
    if let some mo := (← getNode n).internal.modelOrder then
      if mo <= modelOrder then return false
      modelOrder := mo
  return true

/-- `[a, b]` → `[x (model order 0), z (model order 1)]` with `b→x`, `a→z`: by barycenter `z`
(≈ 0.5) precedes `x` (≈ 1.5). `setup` adjusts the nodes before the heuristic is created. -/
def moGraph (setup : LNodeId → LNodeId → LayeredM Unit := fun _ _ => pure ()) :
    LayeredM (LGraphId × Array (Array LNodeId) × LNodeId × LNodeId) := do
  let c : Cfg := { selfUnit := true, fixSide := true }
  let g ← newGraph c
  let left ← makeLayer g
  let right ← makeLayer g
  let ln ← addNodes c g left 2
  let rn ← addNodes c g right 2
  let (x, z) := (rn[0]!, rn[1]!)
  modifyNode x fun n => { n with internal := { n.internal with modelOrder := some 0 } }
  modifyNode z fun n => { n with internal := { n.internal with modelOrder := some 1 } }
  eastWestEdgeFromTo c ln[1]! x
  eastWestEdgeFromTo c ln[0]! z
  setup x z
  let _ ← assignIds g
  return (g, ← nodeArray g, x, z)

/-- The model order sort result on `moGraph` and the barycenters of `x`, `z` afterwards. -/
def moRun (force : Bool := true) (strategy : GroupOrderStrategy := .onlyWithinGroup)
    (setup : LNodeId → LNodeId → LayeredM Unit := fun _ _ => pure ()) :
    LayeredM (Array LNodeId × LNodeId × LNodeId × Array (Option Float) × Int) := do
  let (_, order, x, z) ← moGraph setup
  let h ← createModelOrderHeuristic order force (strategy := strategy)
  let (order', _) ← h.minimizeCrossings order 1 true true (← IO.mkRef (Random.ofInt 0))
  -- a comparison after the sort sees the relations left by the sort (cleared with `force`)
  let after ← h.compareNodesM x z
  return (order'[1]!, x, z, ← barysOf h.base #[x, z], after)

/-- The plain barycenter heuristic on `moGraph`. -/
def moPlainBarycenter : LayeredM (Array LNodeId × LNodeId × LNodeId) := do
  let (_, order, x, z) ← moGraph
  let h ← createHeuristic order
  let (order', _) ← h.minimizeCrossings order 1 true true (← IO.mkRef (Random.ofInt 0))
  return (order'[1]!, x, z)

/-- `compare_nodes` decisions on `moGraph` after the barycenters were computed; `prepare` can set
the barycenter states. -/
def moCompare (force : Bool := true) (strategy : GroupOrderStrategy := .onlyWithinGroup) (maxNodes : Int := 0)
    (locked : Bool := false) (setup : LNodeId → LNodeId → LayeredM Unit := fun _ _ => pure ())
    (equalBarycenters : Bool := false) : LayeredM (Int × Int) := do
  let (g, order, x, z) ← moGraph setup
  let h ← createModelOrderHeuristic order force maxNodes strategy (if locked then some g else none)
  let random ← IO.mkRef (Random.ofInt 0)
  h.base.updatePortRanks order 1 true
  h.base.calculateBarycentersM order[1]! true random
  if equalBarycenters then
    h.base.constraintResolver.barycenterStates.modify fun s =>
      s.modify 1 fun l => l.map fun o => o.map fun st => { st with barycenter := some 1.0 }
  let first ← h.compareNodesM x z
  let second ← h.compareNodesM x z
  return (first, second)

/-- Sets the crossing minimisation group ids. -/
def setGroups (gx gz : Int) (x z : LNodeId) : LayeredM Unit := do
  setNodeProp x LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID gx
  setNodeProp z LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID gz

/-- `ENFORCED` group order on the graph with enforced groups `[0, 1]`; `x` in group 1, `z` in 0. -/
def setEnforced (x z : LNodeId) : LayeredM Unit := do
  let some g := (← getNode x).graph | return
  setGraphProp g LayeredOptions.GROUP_MODEL_ORDER_CM_GROUP_ORDER_STRATEGY GroupOrderStrategy.enforced
  setGraphProp g LayeredOptions.GROUP_MODEL_ORDER_CM_ENFORCED_GROUP_ORDERS #[0, 1]
  setGroups 1 0 x z

/-- Insertion sort with a dummy: `[x (mo 2), y (mo 0), d (no mo), z (mo 1)]` whose barycenters
are x ≈ 2.5, y ≈ 1/3, d ≈ 2/3, z ≈ 1.5 (left `[a, b, c]`, edges `c→x`, `a→y`, `b→z`, `a→d`). -/
def moDummyGraph : LayeredM (Array LNodeId × Array LNodeId) := do
  let c : Cfg := { selfUnit := true, fixSide := true }
  let g ← newGraph c
  let left ← makeLayer g
  let right ← makeLayer g
  let ln ← addNodes c g left 3
  let rn ← addNodes c g right 4
  for (n, mo) in rn.zip #[some 2, some 0, none, some 1] do
    modifyNode n fun x => { x with internal := { x.internal with modelOrder := mo } }
  eastWestEdgeFromTo c ln[2]! rn[0]!
  eastWestEdgeFromTo c ln[0]! rn[1]!
  eastWestEdgeFromTo c ln[1]! rn[3]!
  eastWestEdgeFromTo c ln[0]! rn[2]!
  let _ ← assignIds g
  let order ← nodeArray g
  let h ← createModelOrderHeuristic order
  let (order', _) ← h.minimizeCrossings order 1 true true (← IO.mkRef (Random.ofInt 0))
  return (rn, order'[1]!)

def modelOrderTests : Suite := suite "layered.p3order.model_order_barycenter_heuristic" do
  check "test_model_order_respected" (← runL tModelOrderRespected)
  let (plain, x, z) ← runL moPlainBarycenter
  check "plain barycenter order on the model order graph (hand: [z, x])" (plain == #[z, x])
  let (result, x, z, barys, after) ← runL moRun
  check "forced model order overrides the barycenters (hand: [x, z])" (result == #[x, z])
  checkBary "forced: x keeps its own barycenter (hand: 1.5 + p1)" barys[0]! (1.5 + pert F1)
  checkBary "forced: z keeps its own barycenter (no resolver; hand: 0.5 + p2)" barys[1]! (0.5 + pert F2)
  checkEq "forced: the relations are cleared after the sort (hand: fresh compare -1)" after (-1)
  let (result, x, z, barys, after) ← runL (moRun (force := false))
  check "non-forced sort_by keeps the model order (hand: [x, z])" (result == #[x, z])
  let merged := ((1.5 + pert F1) + (0.5 + pert F2)) / 2.0
  checkBary "non-forced: the resolver merges the layout units (hand: mean)" barys[0]! merged
  checkEq "non-forced: the relations survive the sort (hand: biggerThan(x) ∋ z → 1)" after 1
  let (first, second) ← runL moCompare
  checkEq "compare_nodes by model order (hand: 0 < 1 → -1)" first (-1)
  checkEq "the same pair again uses the recorded relation (Java/Rust quirk: 1)" second 1
  let (result, x, z, _, _) ← runL (moRun (setup := setGroups 1 2))
  check "ONLY_WITHIN_GROUP across groups falls back to the barycenters (hand: [z, x])" (result == #[z, x])
  let (result, x, z, _, _) ← runL (moRun (strategy := .modelOrder) (setup := setGroups 1 2))
  check "MODEL_ORDER group strategy compares across groups (hand: [x, z])" (result == #[x, z])
  let (first, _) ← runL (moCompare (setup := fun x _ => modifyNode x fun n =>
    { n with props := n.props.set LayeredOptions.LAYERING_LAYER_CONSTRAINT LayerConstraint.firstSeparate }) )
  checkEq "FIRST_SEPARATE compares equal" first 0
  let (first, _) ← runL (moCompare (equalBarycenters := true))
  checkEq "model order decides between equal barycenters (hand: -1)" first (-1)
  let (first, _) ← runL (moCompare (equalBarycenters := true) (setup := fun x _ => modifyNode x fun n =>
    { n with internal := { n.internal with modelOrder := none } }))
  checkEq "equal barycenters without model order compare equal" first 0
  let (first, _) ← runL (moCompare (strategy := .enforced) (maxNodes := 10) (setup := setEnforced))
  checkEq "graph readable: enforced group model order (hand: 10*1+0 vs 10*0+1 → 1)" first 1
  let (first, _) ← runL (moCompare (strategy := .enforced) (maxNodes := 10) (locked := true) (setup := setEnforced))
  checkEq "graph locked (Rust try_lock fails): plain model order (hand: 0 vs 1 → -1)" first (-1)
  let (rn, result) ← runL moDummyGraph
  check "insertion sort places the dummy by barycenter (hand: [y, d, z, x])"
    (result == #[rn[1]!, rn[2]!, rn[3]!, rn[0]!])

/-! ## `MedianHeuristic` -/

/-- `[a, b, c]` → `[x, y, z, w]` with `a→x`, `c→x`, `b→y`, `a→w`, `b→w`, `c→w` (`z` unconnected),
after `setFirstLayerOrder` with `Random(0)` (weights 0.731, 0.2405, 0.637 → `[b, c, a]`, then
`b = 1`, `c = 2`, `a = 3`) and a forward step on the right layer. -/
def medianRun : LayeredM (Array LNodeId × Array LNodeId × Array LNodeId × Array LNodeId × Array (Option Float) × Bool) := do
  let c : Cfg := { fixSide := true }
  let g ← newGraph c
  let left ← makeLayer g
  let right ← makeLayer g
  let ln ← addNodes c g left 3
  let rn ← addNodes c g right 4
  let (a, b, cc) := (ln[0]!, ln[1]!, ln[2]!)
  let (x, y, w) := (rn[0]!, rn[1]!, rn[3]!)
  eastWestEdgeFromTo c a x
  eastWestEdgeFromTo c cc x
  eastWestEdgeFromTo c b y
  eastWestEdgeFromTo c a w
  eastWestEdgeFromTo c b w
  eastWestEdgeFromTo c cc w
  let _ ← assignIds g
  let order ← nodeArray g
  let h := MedianHeuristic.new
  let rec_ := h.toHeuristic (← IO.mkRef (Random.ofInt 0))
  Initializable.init #[rec_.initializable] order
  let (order, _) ← rec_.setFirstLayerOrder order true
  let (order', improved) ← rec_.minimizeCrossings order 1 true true
  let weights ← (ln ++ rn).mapM fun n => do return (← getNode n).internal.weight
  return (ln, rn, order'[0]!, order'[1]!, weights, improved || (← rec_.isDeterministic) == false)

/-- Backward step: the left layer by the weights of the right layer `[x (5), y (1)]`. -/
def medianBackward : LayeredM (Array LNodeId × Array LNodeId × Array LNodeId) := do
  let c : Cfg := { fixSide := true }
  let g ← newGraph c
  let left ← makeLayer g
  let right ← makeLayer g
  let ln ← addNodes c g left 2
  let rn ← addNodes c g right 2
  eastWestEdgeFromTo c ln[0]! rn[0]!
  eastWestEdgeFromTo c ln[1]! rn[1]!
  modifyNode rn[0]! fun n => { n with internal := { n.internal with weight := some 5.0 } }
  modifyNode rn[1]! fun n => { n with internal := { n.internal with weight := some 1.0 } }
  let _ ← assignIds g
  let order ← nodeArray g
  let (order', _) ← MedianHeuristic.new.minimizeCrossings order 0 false true
  let (unchanged, _) ← MedianHeuristic.new.minimizeCrossings order 0 true true
  return (ln, order'[0]!, unchanged[0]!)

def medianTests : Suite := suite "layered.p3order.median_heuristic" do
  let (ln, rn, left, right, weights, flags) ← runL medianRun
  check "setFirstLayerOrder sorts by nextDouble weights (hand: [b, c, a])" (left == #[ln[1]!, ln[2]!, ln[0]!])
  checkEqR "first layer weights renumbered (hand: a 3, b 1, c 2)" (weights.extract 0 3) #[some 3.0, some 1.0, some 2.0]
  checkEqR "median weights (hand: x upper median of [c 2, a 3] = 3, y 1, w median of [1, 2, 3] = 2)"
    #[weights[3]!, weights[4]!, weights[6]!] #[some 3.0, some 1.0, some 2.0]
  let huge := (Float.maxValue + MedianHeuristic.F64_MIN_POSITIVE) / 2.0
  checkEqR "unconnected z gets (f64::MAX + f64::MIN_POSITIVE) / 2" weights[5]! (some huge)
  check "median order (hand: [y, w, x, z])" (right == #[rn[1]!, rn[3]!, rn[0]!, rn[2]!])
  check "deterministic and no improvement reported" (!flags)
  let (ln, backward, unchanged) ← runL medianBackward
  check "backward step uses the next layer (hand: [b (1), a (5)])" (backward == #[ln[1]!, ln[0]!])
  check "no reference layer: unchanged" (unchanged == ln)
  let sorted ← runL do
    let g ← newGraph {}
    let l ← makeLayer g
    let ns ← addNodes {} g l 4
    modifyNode ns[1]! fun n => { n with internal := { n.internal with weight := some 5.0 } }
    modifyNode ns[3]! fun n => { n with internal := { n.internal with weight := some 2.0 } }
    return (MedianHeuristic.stableSortByWeight (← get) ns == #[ns[3]!, ns[1]!, ns[0]!, ns[2]!])
  check "stable_sort_by_weight: known weights first, unknown keep their order" sorted
  checkFloat "f64::MIN_POSITIVE" MedianHeuristic.F64_MIN_POSITIVE 2.2250738585072014e-308 0.0

/-! ## `SweepCopy` -/

/-- Two layers `[a, b]`, `[x, y]`; `a` has two east ports. A copy is taken, the order and the
ports of `a` are scrambled, and the copy is written back. -/
def sweepRoundTrip (setPortConstraints : Bool) :
    LayeredM (Bool × Bool × Array Int × Array PortConstraints × SweepCopy) := do
  let c : Cfg := {}
  let g ← newGraph c
  let l0 ← makeLayer g
  let l1 ← makeLayer g
  let ln ← addNodes c g l0 2
  let rn ← addNodes c g l1 2
  let (a, b) := (ln[0]!, ln[1]!)
  let p1 ← addPort c a .east
  let p2 ← addPort c a .east
  connect p1 (← addPort c rn[0]! .west)
  connect p2 (← addPort c rn[1]! .west)
  setNodeProp b LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedPos
  setNodeProp rn[0]! LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
  let nPorts ← assignIds g
  let order ← nodeArray g
  let snap ← CrossMinSnapshot.build order nPorts
  let sc ← SweepCopy.new order snap
  modifyLayer l0 fun l => { l with nodes := #[b, a] }
  modifyNode a fun n => { n with ports := #[p2, p1], id := 5 }
  sc.transferNodeAndPortOrdersToGraph g setPortConstraints snap
  let nodesOk := (← getLayer l0).nodes == #[a, b]
  let portsOk := (← getNode a).ports == #[p1, p2]
  let ids ← (ln ++ rn).mapM fun n => do return (← getNode n).id
  let constraints ← (ln ++ rn).mapM fun n => getNodePropD n LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  return (nodesOk, portsOk, ids, constraints, sc)

/-- A node `n` with a `side` port `pn` (explicit anchor `(2, 1)` on a `4 × 6` port when
`explicitAnchor`) and an east port, and its north/south dummy `d` (layout unit `n`, port origin
`pn`); the saved order puts `d` `dummyFirst` or after `n`. Returns `pn`'s side and anchor and
`n`'s port order after the transfer. -/
def sweepNorthSouth (side : PortSide) (dummyFirst explicitAnchor : Bool) (originConstraints : PortConstraints) :
    LayeredM (PortSide × Float × Bool) := do
  let c : Cfg := {}
  let g ← newGraph c
  let l0 ← makeLayer g
  let nodes ← addNodes c g l0 2
  let (n, d) := if dummyFirst then (nodes[1]!, nodes[0]!) else (nodes[0]!, nodes[1]!)
  let pn ← addPort c n side
  let pe ← addPort c n .east
  modifyPort pn fun p => { p with size := ⟨4.0, 6.0⟩ }
  if explicitAnchor then
    modifyPort pn fun p => { p with anchor := ⟨2.0, 1.0⟩, explicitlySuppliedPortAnchor := true }
  let pd ← addPort c d .east
  modifyPort pd fun p => { p with internal := { p.internal with origin := some (.lPort pn) } }
  modifyNode d fun x => { x with type := .northSouthPort, internal := { x.internal with inLayerLayoutUnit := some n } }
  setNodeProp n LayeredOptions.PORT_CONSTRAINTS originConstraints
  let nPorts ← assignIds g
  let order ← nodeArray g
  let snap ← CrossMinSnapshot.build order nPorts
  let sc ← SweepCopy.new order snap
  sc.transferNodeAndPortOrdersToGraph g false snap
  let p ← getPort pn
  -- after a side switch the ports of `n` are re-sorted by side (`east` before `south`)
  return (p.side, p.anchor.y, (← getNode n).ports == (if p.side == .south then #[pe, pn] else #[pn, pe]))

def sweepCopyTests : Suite := suite "layered.p3order.sweep_copy" do
  let (nodesOk, portsOk, ids, constraints, sc) ← runL (sweepRoundTrip false)
  check "node order written back" nodesOk
  check "port order written back" portsOk
  checkEqR "ids are the positions in the layer" ids #[0, 1, 0, 1]
  checkEqR "without setPortConstraints the constraints are unchanged" constraints
    #[.undefined, .fixedPos, .fixedSide, .undefined]
  checkEqR "the copy stores flat node indices and port ids" sc.nodeIndices #[#[0, 1], #[2, 3]]
  checkEqR "port ids per node" sc.portOrders #[#[#[0, 1], #[]], #[#[2], #[3]]]
  check "copy_from_sweep yields the source" (SweepCopy.copyFromSweep {} sc == sc)
  let (_, _, _, constraints, _) ← runL (sweepRoundTrip true)
  checkEqR "setPortConstraints fixes the order unless already fixed" constraints
    #[.fixedOrder, .fixedPos, .fixedOrder, .fixedOrder]
  let (side, anchorY, portsOk) ← runL (sweepNorthSouth .north false false .undefined)
  checkEq "north port with its dummy below becomes south" side PortSide.south
  checkFloat "implicit anchor moved by setSide (hand: y = height 6)" anchorY 6.0 0.0
  check "origin ports re-sorted by side (hand: [east, south])" portsOk
  let (side, anchorY, _) ← runL (sweepNorthSouth .north false true .undefined)
  checkEq "explicit anchor: side switched" side PortSide.south
  checkFloat "explicit anchor mirrored (hand: 6 - 1 = 5)" anchorY 5.0 0.0
  let (side, anchorY, _) ← runL (sweepNorthSouth .south true true .undefined)
  checkEq "south port with its dummy above becomes north" side PortSide.north
  checkFloat "explicit anchor mirrored (hand: -(6 - 1) = -5)" anchorY (-5.0) 0.0
  let (side, _, _) ← runL (sweepNorthSouth .north true false .undefined)
  checkEq "north port with its dummy above stays north" side PortSide.north
  let (side, _, _) ← runL (sweepNorthSouth .north false false .fixedPos)
  checkEq "FIXED_POS origin: no side switch (Rust)" side PortSide.north
  let sorted ← runL do
    let g ← newGraph {}
    let l ← makeLayer g
    let n ← addNode {} g l
    let pw ← addPort {} n .west
    let pn1 ← addPort {} n .north
    let pn2 ← addPort {} n .north
    modifyPort pn1 fun p => { p with position := ⟨5.0, 0.0⟩ }
    modifyPort pn2 fun p => { p with position := ⟨1.0, 0.0⟩ }
    let a ← get
    return (SweepCopy.sortPortsCombined a #[pw, pn1, pn2] .fixedPos == #[pn2, pn1, pw],
      SweepCopy.sortPortsCombined a #[pw, pn1, pn2] .free == #[pn1, pn2, pw])
  check "compare_ports: fixed order sorts by side, then x on the north side" sorted.1
  check "compare_ports: free order sorts by side only" sorted.2

/-! ## `RandomTrace` -/

def randomTraceTests : Suite := suite "layered.p3order.random_trace" do
  -- expected strings printed by Rust 1.97.1 (`format!("{:.7}|{:.2}|{:.0}", v, v, v)`)
  let cases : Array (Float × String) := #[
    (0.7309677600860596, "0.7309678|0.73|1"), (-0.0, "-0.0000000|-0.00|-0"), (1.5, "1.5000000|1.50|2"),
    (0.125, "0.1250000|0.12|0"), (2.5, "2.5000000|2.50|2"), (0.5, "0.5000000|0.50|0"),
    (0.00000005, "0.0000000|0.00|0"), (0.00000015, "0.0000001|0.00|0"), (-1e-12, "-0.0000000|-0.00|-0"),
    (123.45678905, "123.4567890|123.46|123"), (Float.nan, "NaN|NaN|NaN"), (Float.posInf, "inf|inf|inf"),
    (Float.negInf, "-inf|-inf|-inf"), (0.03125, "0.0312500|0.03|0")]
  for (v, expected) in cases do
    let actual := s!"{RandomTrace.formatFixed 7 v}|{RandomTrace.formatFixed 2 v}|{RandomTrace.formatFixed 0 v}"
    checkEq s!"formatFixed matches Rust ({expected})" actual expected
  checkEq "trace_next_long returns its value" (← RandomTrace.traceNextLong (-5) "test") (-5)
  checkEq "trace_next_boolean returns its value" (← RandomTrace.traceNextBoolean true "test") true
  checkFloat "trace_next_float returns its value" (← RandomTrace.traceNextFloat 0.25 "test") 0.25 0.0
  checkFloat "trace_next_double returns its value" (← RandomTrace.traceNextDouble 0.75 "test") 0.75 0.0
  checkEq "trace_next_int returns its value" (← RandomTrace.traceNextInt 3 "test") 3

/-! ## Suites -/

def suites : Array Suite := #[rustBarycenterTests, handBarycenterTests, modelOrderTests, medianTests, sweepCopyTests,
  randomTraceTests]

end Tests.Layered.P3Heuristics
