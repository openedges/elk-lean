import Tests.Framework
import Tests.Layered.P3Counting
import Elk.Alg.Layered
import Elk.Alg.Layered.P3Order.PortDistributors
/-!
Tests of the `p3order` port distributors (`AbstractBarycenterPortDistributor` with its
node-relative/layer-total ranks, `GreedyPortDistributor`, the `ISweepPortDistributor.create`
factory) and of `ForsterConstraintResolver`, ported from elk-rs
`tests/intermediate/greedyswitch/{abstract_barycenter_port_distributor_test,greedy_port_distributor_test}.rs`
and `tests/p3_order/forster_constraint_resolver_test.rs` (check names are the Rust test names),
plus hand-derived checks ("hand: …"). The graph builders are the `Tests.Layered.P3Counting` ones.

`distribute_ports_in_complete_graph` builds a `GraphInfoHolder` in Rust, which is not ported yet;
it is emulated (`distributeInCompleteGraph`): side caches, the distributor and resolver
initialisation, the `CrossMinSnapshot` hand-over. Its `Random(0).nextBoolean()` picks the
node-relative distributor (`Mode.nodeRelativeSnapshot`); the other modes run the same graphs
through the layer-total ranks and the snapshot-free (lock) path.
-/
namespace Tests.Layered.P3PortDistributors

open Tests Elk.Graph Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open Elk.Alg.Layered.P3Order Elk.Alg.Layered.P3Order.Counting
open Tests.Layered.P3Counting (Cfg newGraph makeLayer addNode addNodes addPort addPorts connect eastWestEdgeFromTo
  eastWestEdgeFromPort eastWestEdgeFromNode addInLayerEdge addNorthSouthEdge nodeArray runL rnd shuffle)
open LayeredM

/-! ## Builders -/

/-- `abstract_barycenter_port_distributor_test.rs` helpers: graph options, self layout units,
`FIXED_SIDE` ports, the full north/south bookkeeping. -/
def bCfg : Cfg := { options := true, selfUnit := true, fixSide := true, full := true }

/-- `greedy_port_distributor_test.rs` helpers (`set_up_graph` is called explicitly). -/
def gCfg : Cfg := { selfUnit := true, fixSide := true }

/-- The node's ports in order. -/
def portsOf (n : LNodeId) : LayeredM (Array LPortId) := do return (← getNode n).ports

/-- `nested_graph(node)`: the node's nested graph (created with `set_up_graph`). -/
def nestedGraph (n : LNodeId) : LayeredM LGraphId := do
  if let some g := (← getNode n).nestedGraph then return g
  let g ← newGraph { options := true }
  modifyGraph g fun x => { x with parentNode := some n }
  modifyNode n fun x => { x with nestedGraph := some g }
  return g

/-- `add_external_port_dummy_node_to_layer(layer, port)`. -/
def addExternalPortDummy (c : Cfg) (l : LayerId) (port : LPortId) : LayeredM LNodeId := do
  let g := (← getLayer l).owner
  let n ← addNode c g l
  let side := (← getPort port).side
  modifyNode n fun x => { x with
    type := .externalPort, internal := { x.internal with origin := some (.lPort port), extPortSide := side } }
  modifyPort port fun x => { x with internal := { x.internal with portDummy := some n, insideConnections := true } }
  modifyGraph g fun x => { x with
    internal := { x.internal with graphProperties := x.internal.graphProperties.insert .externalPorts } }
  return n

/-- `add_external_port_dummies_to_layer(layer, ports)`: eastern ports top-down, others reversed. -/
def addExternalPortDummies (c : Cfg) (l : LayerId) (ports : Array LPortId) : LayeredM (Array LNodeId) := do
  if ports.isEmpty then return #[]
  let side := (← getPort ports[0]!).side
  let mut nodes := #[]
  for i in [0:ports.size] do
    let index := if side == .east then i else ports.size - 1 - i
    nodes := nodes.push (← addExternalPortDummy c l ports[index]!)
  return nodes

/-- Number of ports of an order. -/
def portCount (order : Array (Array LNodeId)) : LayeredM Nat := do
  let mut n := 0
  for layer in order do
    for node in layer do
      n := n + (← getNode node).ports.size
  return n

/-! ## Barycenter distributor harness -/

/-- Rank strategy and code path of a barycenter distributor run. -/
inductive Mode where
  | nodeRelativeSnapshot
  | layerTotalSnapshot
  | nodeRelativeLive
  | layerTotalLive
  deriving BEq, Repr, Inhabited

instance : ToString Mode where
  toString
    | .nodeRelativeSnapshot => "node-relative/snapshot"
    | .layerTotalSnapshot => "layer-total/snapshot"
    | .nodeRelativeLive => "node-relative/live"
    | .layerTotalLive => "layer-total/live"

def Mode.strategy : Mode → PortRankStrategy
  | .nodeRelativeSnapshot | .nodeRelativeLive => .nodeRelative
  | .layerTotalSnapshot | .layerTotalLive => .layerTotal

def Mode.snapshot : Mode → Bool
  | .nodeRelativeSnapshot | .layerTotalSnapshot => true
  | _ => false

def allModes : Array Mode := #[.nodeRelativeSnapshot, .layerTotalSnapshot, .nodeRelativeLive, .layerTotalLive]

/-- A barycenter distributor initialised on `order` like the `GraphInfoHolder` does (port side
caches, distributor and resolver initialisation, snapshot hand-over in the snapshot modes). -/
def initDistributor (m : Mode) (order : Array (Array LNodeId)) : LayeredM AbstractBarycenterPortDistributor := do
  let d ← AbstractBarycenterPortDistributor.new order.size m.strategy
  let r ← ForsterConstraintResolver.new order false
  for layer in order do
    for n in layer do cachePortSides n
  Initializable.init #[d.initializable, r.initializable] order
  if m.snapshot then
    let s ← CrossMinSnapshot.build order (← portCount order)
    d.setSnapshot s
    r.setSnapshot s
  return d

/-- `distribute_ports_in_complete_graph(graph)`: a forward sweep over all layers, then a
backward sweep. -/
def distributeInCompleteGraph (m : Mode) (g : LGraphId) : LayeredM Unit := do
  let order ← nodeArray g
  let d ← initDistributor m order
  for i in [0:order.size] do
    let _ ← d.distributePortsWhileSweeping order i true
  for k in [0:order.size] do
    let _ ← d.distributePortsWhileSweeping order (order.size - 1 - k) false

/-! ## `abstract_barycenter_port_distributor_test.rs` -/

/-- `distribute_ports_on_side_given_cross_on_western_side_removes_crossing`. -/
def abWesternCross (m : Mode) : LayeredM Bool := do
  let g ← newGraph bCfg
  let leftNodes ← addNodes bCfg g (← makeLayer g) 2
  let rightNode ← addNode bCfg g (← makeLayer g)
  eastWestEdgeFromTo bCfg leftNodes[0]! rightNode
  eastWestEdgeFromTo bCfg leftNodes[1]! rightNode
  let original ← portsOf rightNode
  distributeInCompleteGraph m g
  return (← portsOf rightNode) == #[original[1]!, original[0]!]

/-- `distribute_ports_of_graph_given_cross_on_both_sides_removes_crossing`. -/
def abBothSidesCross (m : Mode) : LayeredM Bool := do
  let g ← newGraph bCfg
  let leftNodes ← addNodes bCfg g (← makeLayer g) 2
  let middleNode ← addNode bCfg g (← makeLayer g)
  let rightNodes ← addNodes bCfg g (← makeLayer g) 2
  eastWestEdgeFromTo bCfg middleNode rightNodes[1]!
  eastWestEdgeFromTo bCfg middleNode rightNodes[0]!
  eastWestEdgeFromTo bCfg leftNodes[0]! middleNode
  eastWestEdgeFromTo bCfg leftNodes[1]! middleNode
  let o ← portsOf middleNode
  distributeInCompleteGraph m g
  return (← portsOf middleNode) == #[o[1]!, o[0]!, o[3]!, o[2]!]

/-- `distribute_ports_of_graph_given_cross_on_eastern_side_removes_crossing`. -/
def abEasternCross (m : Mode) : LayeredM Bool := do
  let g ← newGraph bCfg
  let leftNode ← addNode bCfg g (← makeLayer g)
  let rightNodes ← addNodes bCfg g (← makeLayer g) 2
  eastWestEdgeFromTo bCfg leftNode rightNodes[1]!
  eastWestEdgeFromTo bCfg leftNode rightNodes[0]!
  let o ← portsOf leftNode
  distributeInCompleteGraph m g
  return (← portsOf leftNode) == #[o[1]!, o[0]!]

/-- `distribute_ports_of_graph_given_in_layer_edge_port_order_crossing_removes_it`. -/
def abInLayerCross (m : Mode) : LayeredM Bool := do
  let g ← newGraph bCfg
  let _ ← addNode bCfg g (← makeLayer g)
  let nodes ← addNodes bCfg g (← makeLayer g) 3
  addInLayerEdge bCfg nodes[0]! nodes[2]! .east
  addInLayerEdge bCfg nodes[1]! nodes[2]! .east
  let o ← portsOf nodes[2]!
  distributeInCompleteGraph m g
  return (← portsOf nodes[2]!) == #[o[1]!, o[0]!]

/-- `distribute_ports_of_graph_given_north_south_port_order_crossing_switches`; also returns the
sides of the switched ports (the distributors never move ports between sides). -/
def abNorthSouthCross (m : Mode) : LayeredM (Bool × Array PortSide) := do
  let g ← newGraph bCfg
  let leftNodes ← addNodes bCfg g (← makeLayer g) 3
  let rightNodes ← addNodes bCfg g (← makeLayer g) 2
  addNorthSouthEdge bCfg .north leftNodes[2]! leftNodes[1]! rightNodes[1]! false
  addNorthSouthEdge bCfg .north leftNodes[2]! leftNodes[0]! rightNodes[0]! false
  let o ← portsOf leftNodes[2]!
  distributeInCompleteGraph m g
  let after ← portsOf leftNodes[2]!
  let sides ← after.mapM fun p => return (← getPort p).side
  return (after == #[o[1]!, o[0]!], sides)

/-- `distribute_ports_while_sweeping_given_simple_cross_removes_crossing` (layer-total, no
snapshot, one forward step on layer 1). -/
def abSimpleCross : LayeredM Bool := do
  let g ← newGraph bCfg
  let leftNode ← addNode bCfg g (← makeLayer g)
  let rightNode ← addNode bCfg g (← makeLayer g)
  eastWestEdgeFromTo bCfg leftNode rightNode
  eastWestEdgeFromTo bCfg leftNode rightNode
  let o ← portsOf rightNode
  let order ← nodeArray g
  let d ← LayerTotalPortDistributor.new order.size
  Initializable.init #[d.initializable] order
  let _ ← d.distributePortsWhileSweeping order 1 true
  return (← portsOf rightNode) == #[o[1]!, o[0]!]

def abstractBarycenterTests : Suite := suite "layered.p3order.abstract_barycenter_port_distributor" do
  for m in allModes do
    check s!"distribute_ports_on_side_given_cross_on_western_side_removes_crossing ({m})" (← runL (abWesternCross m))
    check s!"distribute_ports_of_graph_given_cross_on_both_sides_removes_crossing ({m})" (← runL (abBothSidesCross m))
    check s!"distribute_ports_of_graph_given_cross_on_eastern_side_removes_crossing ({m})" (← runL (abEasternCross m))
    check s!"distribute_ports_of_graph_given_in_layer_edge_port_order_crossing_removes_it ({m})" (← runL (abInLayerCross m))
    let (switched, sides) ← runL (abNorthSouthCross m)
    check s!"distribute_ports_of_graph_given_north_south_port_order_crossing_switches ({m})" switched
    checkEq s!"north/south ports keep their side ({m}) (hand: NORTH, NORTH)" sides #[PortSide.north, .north]
  check "distribute_ports_while_sweeping_given_simple_cross_removes_crossing" (← runL abSimpleCross)

/-! ## Hand-derived barycenter checks -/

/-- Rank graph: layer 0 `[X]` with `nx` (north) and `x1`, `x2` (east) outputs; layer 1
`[C, A, B]`: `C` without ports, `A` with inputs `n1` (north), `w1`, `w2` (west), `s1` (south),
`B` with input `w3` (west). -/
def rankGraph : LayeredM (Array (Array LNodeId) × Array LPortId) := do
  let c : Cfg := { fixSide := true }
  let g ← newGraph c
  let l0 ← makeLayer g
  let l1 ← makeLayer g
  let x ← addNode c g l0
  let _nodeC ← addNode c g l1
  let nodeA ← addNode c g l1
  let nodeB ← addNode c g l1
  let nx ← addPort c x .north
  let x1 ← addPort c x .east
  let x2 ← addPort c x .east
  let n1 ← addPort c nodeA .north
  let w1 ← addPort c nodeA .west
  let w2 ← addPort c nodeA .west
  let s1 ← addPort c nodeA .south
  let w3 ← addPort c nodeB .west
  connect nx n1
  connect x1 w1
  connect x2 w2
  connect x1 s1
  connect x2 w3
  return (← nodeArray g, #[nx, x1, x2, n1, w1, w2, s1, w3])

/-- Ranks of the rank graph: input ranks of layer 1 and output ranks of layer 0, by port id
`0‥7` (`nx, x1, x2, n1, w1, w2, s1, w3`). -/
def rankGraphRanks (m : Mode) : LayeredM (Array Float × Array Float) := do
  let (order, _) ← rankGraph
  let d ← initDistributor m order
  d.calculatePortRanks order[1]! .input
  let inputs ← d.portRanks
  d.calculatePortRanks order[0]! .output
  let outputs ← d.portRanks
  return (inputs, outputs)

/-- Checks a rank array against hand values (absolute tolerance for the `f32` rounding). -/
def checkRanks (name : String) (actual expected : Array Float) : TestM Unit := do
  checkEq s!"{name} (count)" actual.size expected.size
  for i in [0:expected.size] do
    checkFloat s!"{name} [{i}]" (actual[i]?.getD Float.nan) expected[i]! (eps := 1e-6)

/-- Two-node cross: layer 0 `[L0, L1]` with east ports `e0`, `e1`; layer 1 `[R]` with west
ports `p0 ← e0`, `p1 ← e1`. One forward step on layer 1 with the given constraints on `R`;
returns `R`'s ports, the barycenters and the ranks (port ids `e0 = 0, e1 = 1, p0 = 2, p1 = 3`). -/
def crossStep (m : Mode) (constraints : Option PortConstraints) :
    LayeredM (Array LPortId × Array LPortId × Array Float × Array Float) := do
  let c : Cfg := { fixSide := true }
  let g ← newGraph c
  let l0 ← makeLayer g
  let l1 ← makeLayer g
  let left ← addNodes c g l0 2
  let r ← addNode c g l1
  let e0 ← addPort c left[0]! .east
  let e1 ← addPort c left[1]! .east
  let p0 ← addPort c r .west
  let p1 ← addPort c r .west
  connect e0 p0
  connect e1 p1
  match constraints with
  | some pc => setNodeProp r LayeredOptions.PORT_CONSTRAINTS pc
  | none => modifyNode r fun x => { x with props := {} }
  let order ← nodeArray g
  let d ← initDistributor m order
  let _ ← d.distributePortsWhileSweeping order 1 true
  return (← portsOf r, #[p0, p1], ← d.portBarycenters, ← d.portRanks)

/-- Ports with equal barycenters: layer 0 `[L]` (no ports), layer 1 `[R]` with unconnected west
ports `u0`, `u1`, reordered to `[u1, u0]` after the initialisation (and snapshot). -/
def tieStep (m : Mode) : LayeredM (Array LPortId × Array LPortId) := do
  let c : Cfg := { fixSide := true }
  let g ← newGraph c
  let _ ← addNode c g (← makeLayer g)
  let r ← addNode c g (← makeLayer g)
  let u0 ← addPort c r .west
  let u1 ← addPort c r .west
  let order ← nodeArray g
  let d ← initDistributor m order
  modifyNode r fun x => { x with ports := #[u1, u0] }
  let _ ← d.distributePortsWhileSweeping order 1 true
  return (← portsOf r, #[u0, u1])

/-- Graph where the two rank strategies disagree: layer 0 `[A, B]` with east ports `a0` and
`b0, b1, b2`; layer 1 `[R, S]` with west ports `p ← b0`, `q ← a0, b2` and `s0 ← b1`. -/
def strategyGraph : LayeredM (Array (Array LNodeId) × LNodeId × LPortId × LPortId) := do
  let c : Cfg := { fixSide := true }
  let g ← newGraph c
  let l0 ← makeLayer g
  let l1 ← makeLayer g
  let nodeA ← addNode c g l0
  let nodeB ← addNode c g l0
  let r ← addNode c g l1
  let s ← addNode c g l1
  let a0 ← addPort c nodeA .east
  let bs ← addPorts c nodeB 3 .east
  let p ← addPort c r .west
  let q ← addPort c r .west
  let s0 ← addPort c s .west
  connect bs[0]! p
  connect a0 q
  connect bs[2]! q
  connect bs[1]! s0
  return (← nodeArray g, r, p, q)

/-- One forward step on layer 1 of the strategy graph; `R`'s ports and whether they are `[p, q]`. -/
def strategyStep (m : Mode) : LayeredM (Bool × Array Float) := do
  let (order, r, p, q) ← strategyGraph
  let d ← initDistributor m order
  let _ ← d.distributePortsWhileSweeping order 1 true
  return ((← portsOf r) == #[p, q], ← d.portBarycenters)

def handBarycenterTests : Suite := suite "layered.p3order.barycenter_port_distributor.hand" do
  -- node-relative: C consumes 1; A: incr 1/5 from 1 (north 1.2, rest 1.8, 1.6, 1.4); B: 2 + 1 - 1/2
  -- layer-total: C consumes 0; A: north 0 + 1, rest 0 + 4 downwards; B: 4 + 1. Outputs 1/4 steps or 1, 2, 3.
  for m in allModes do
    let (inputs, outputs) ← runL (rankGraphRanks m)
    match m.strategy with
    | .nodeRelative =>
      checkRanks s!"node-relative input ranks ({m}) (hand: n1 1.2, w1 1.8, w2 1.6, s1 1.4, w3 2.5)" inputs
        #[0.0, 0.0, 0.0, 1.2, 1.8, 1.6, 1.4, 2.5]
      checkRanks s!"node-relative output ranks ({m}) (hand: nx 0.25, x1 0.5, x2 0.75)" outputs
        #[0.25, 0.5, 0.75, 1.2, 1.8, 1.6, 1.4, 2.5]
    | .layerTotal =>
      checkRanks s!"layer-total input ranks ({m}) (hand: n1 1, w1 4, w2 3, s1 2, w3 5)" inputs
        #[0.0, 0.0, 0.0, 1.0, 4.0, 3.0, 2.0, 5.0]
      checkRanks s!"layer-total output ranks ({m}) (hand: nx 1, x1 2, x2 3)" outputs
        #[1.0, 2.0, 3.0, 1.0, 4.0, 3.0, 2.0, 5.0]
  -- layer-total ranks e0 = 1, e1 = 2 → bary(p0) = -1, bary(p1) = -2 → [p1, p0]; then R's input
  -- ranks in the new order p1 = 2, p0 = 1 and e0/e1 get the barycenters +1/+2
  for m in allModes do
    if m.strategy != .layerTotal then continue
    let (after, ps, barys, ranks) ← runL (crossStep m (some .fixedSide))
    checkEqR s!"FIXED_SIDE ports sorted by barycenter ({m}) (hand: [p1, p0])" after #[ps[1]!, ps[0]!]
    checkRanks s!"FIXED_SIDE barycenters ({m}) (hand: e0 1, e1 2, p0 -1, p1 -2)" barys #[1.0, 2.0, -1.0, -2.0]
    checkRanks s!"FIXED_SIDE free-layer input ranks ({m}) (hand: p0 1, p1 2)" ranks #[1.0, 2.0, 1.0, 2.0]
    let (after, ps, barys, ranks) ← runL (crossStep m (some .fixedOrder))
    checkEqR s!"FIXED_ORDER keeps the port order ({m}) (hand: [p0, p1])" after ps
    checkRanks s!"FIXED_ORDER computes no barycenters on R ({m}) (hand: e0 +2, e1 +1, p0 0, p1 0)" barys #[2.0, 1.0, 0.0, 0.0]
    checkRanks s!"FIXED_ORDER input ranks in the kept order ({m}) (hand: p0 2, p1 1)" ranks #[1.0, 2.0, 2.0, 1.0]
    let (after, ps, _, _) ← runL (crossStep m (some .free))
    checkEqR s!"FREE ports sorted ({m}) (hand: [p1, p0])" after #[ps[1]!, ps[0]!]
    let (after, ps, _, _) ← runL (crossStep m none)
    checkEqR s!"UNDEFINED constraints sorted ({m}) (hand: [p1, p0])" after #[ps[1]!, ps[0]!]
  -- node-relative: e0 = 0.5, e1 = 1.5 → bary(p0) = -0.5, bary(p1) = -1.5 → [p1, p0]; R's input
  -- ranks p1 = 2/3, p0 = 1/3 give e0/e1 the barycenters 1/3 and 2/3
  for m in allModes do
    if m.strategy != .nodeRelative then continue
    let (after, ps, barys, _) ← runL (crossStep m (some .fixedSide))
    checkEqR s!"node-relative cross sorted ({m}) (hand: [p1, p0])" after #[ps[1]!, ps[0]!]
    checkRanks s!"node-relative barycenters ({m}) (hand: e0 1/3, e1 2/3, p0 -0.5, p1 -1.5)" barys
      #[1.0 / 3.0, 2.0 / 3.0, -0.5, -1.5]
  -- equal barycenters keep the current port order, also with a snapshot: Rust's `sort_ports`
  -- runs while `distribute_ports` holds the snapshot taken out of `self`, so its lock fallback
  -- sorts the live order (oracle trace: ptolemy_test_auto_GeneratorRegulatorProtectorWithProcessor,
  -- step 79 `LayerSweepCrossingMinimizer`)
  for m in allModes do
    let (after, ps) ← runL (tieStep m)
    checkEqR s!"tie keeps the current port order ({m}) (hand: [u1, u0])" after #[ps[1]!, ps[0]!]
  -- node-relative: a0 0.5, b0 1.25, b2 1.75 → p -1.25 < q (-0.5 - 1.75) / 2 = -1.125;
  -- layer-total: a0 1, b0 2, b2 4 → p -2 > q -2.5
  for m in allModes do
    let (pq, barys) ← runL (strategyStep m)
    match m.strategy with
    | .nodeRelative =>
      check s!"node-relative keeps [p, q] ({m})" pq
      checkFloat s!"node-relative bary(q) ({m}) (hand: -1.125)" (barys[5]?.getD 0.0) (-1.125) (eps := 1e-6)
    | .layerTotal =>
      check s!"layer-total switches to [q, p] ({m})" (!pq)
      checkFloat s!"layer-total bary(q) ({m}) (hand: -2.5)" (barys[5]?.getD 0.0) (-2.5) (eps := 1e-6)

/-! ## `greedy_port_distributor_test.rs` -/

/-- `prepare_distributor(graph, distributor)`. -/
def prepareGreedy (g : LGraphId) : LayeredM (GreedyPortDistributor × Array (Array LNodeId)) := do
  let d ← GreedyPortDistributor.new
  let order ← nodeArray g
  Initializable.init #[d.initializable] order
  return (d, order)

/-- `distribute_ports_cross_on_western_side_removes_crossing`. -/
def gWesternCross : LayeredM (Bool × Bool) := do
  let g ← newGraph gCfg
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let leftNodes ← addNodes gCfg g leftLayer 2
  let rightNode ← addNode gCfg g rightLayer
  eastWestEdgeFromTo gCfg leftNodes[0]! rightNode
  eastWestEdgeFromTo gCfg leftNodes[1]! rightNode
  let (d, order) ← prepareGreedy g
  let o ← portsOf rightNode
  let improved ← d.distributePortsWhileSweeping order 1 true
  return (improved, (← portsOf rightNode) == #[o[1]!, o[0]!])

/-- `distribute_ports_no_ports_on_right_side_no_change`. -/
def gNoPortsOnRightSide : LayeredM (Bool × Bool) := do
  let g ← newGraph gCfg
  let leftLayer ← makeLayer g
  let middleLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let leftNodes ← addNodes gCfg g leftLayer 2
  let middleNode ← addNode gCfg g middleLayer
  let _ ← addNodes gCfg g rightLayer 2
  eastWestEdgeFromTo gCfg leftNodes[0]! middleNode
  eastWestEdgeFromTo gCfg leftNodes[1]! middleNode
  let (d, order) ← prepareGreedy g
  let o ← portsOf middleNode
  let improved ← d.distributePortsWhileSweeping order 1 false
  return (improved, (← portsOf middleNode) == o)

/-- `distribute_ports_multiple_crossings_on_western_side_removes_crossing`. -/
def gMultipleWesternCrossings : LayeredM (Bool × Bool) := do
  let g ← newGraph gCfg
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let leftNodes ← addNodes gCfg g leftLayer 3
  let rightNode ← addNode gCfg g rightLayer
  eastWestEdgeFromTo gCfg leftNodes[0]! rightNode
  eastWestEdgeFromTo gCfg leftNodes[2]! rightNode
  eastWestEdgeFromTo gCfg leftNodes[1]! rightNode
  let (d, order) ← prepareGreedy g
  let o ← portsOf rightNode
  let improved ← d.distributePortsWhileSweeping order 1 true
  -- ELK Java's `GreedyPortDistributorTest.distributePorts_GivenMultipleCrossingsOnWesternSide_RemoveCrossing`
  -- expects `portsOrderedAs(rightNode, 1, 2, 0)`; elk-rs (which also permutes the slot indices of a
  -- switch, see `GreedyPortDistributor`) expected `[2, 0, 1]`
  return (improved, (← portsOf rightNode) == #[o[1]!, o[2]!, o[0]!])

/-- `distribute_ports_crossings_on_eastern_side_removes_them` (and the `FIXED_ORDER` variant
`distribute_ports_fixed_order_no_change`). -/
def gEasternCrossings (fixedOrder : Bool) : LayeredM (Bool × Array LPortId × Array LPortId) := do
  let g ← newGraph gCfg
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let leftNodes ← addNodes gCfg g leftLayer 1
  let rightNodes ← addNodes gCfg g rightLayer 2
  if fixedOrder then
    setNodeProp leftNodes[0]! LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedOrder
  eastWestEdgeFromNode gCfg leftNodes[0]! (← addPort gCfg rightNodes[1]! .west)
  eastWestEdgeFromNode gCfg leftNodes[0]! (← addPort gCfg rightNodes[0]! .west)
  let (d, order) ← prepareGreedy g
  let o ← portsOf leftNodes[0]!
  let improved ← d.distributePortsWhileSweeping order 0 false
  return (improved, ← portsOf leftNodes[0]!, o)

/-- `distribute_ports_no_change_in_ordered_case`. -/
def gOrderedCase : LayeredM Bool := do
  let g ← newGraph gCfg
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let leftNodes ← addNodes gCfg g leftLayer 1
  let rightNodes ← addNodes gCfg g rightLayer 2
  eastWestEdgeFromTo gCfg leftNodes[0]! rightNodes[0]!
  eastWestEdgeFromTo gCfg leftNodes[0]! rightNodes[1]!
  let (d, order) ← prepareGreedy g
  d.distributePortsWhileSweeping order 0 false

/-- The compound graph of the hierarchical tests: an outer node with `n` eastern ports wired to
`n` right nodes by `wiring` (port index, right node index), its nested graph with `n` inner nodes
connected to the external port dummies of the outer ports. -/
def gCompound (n : Nat) (wiring : Array (Nat × Nat)) : LayeredM (LGraphId × LNodeId × Array LPortId) := do
  let c := gCfg
  let g ← newGraph { options := true }
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let leftOuterNode ← addNode c g leftLayer
  let rightNodes ← addNodes c g rightLayer n
  let leftOuterPorts ← addPorts c leftOuterNode n .east
  for (pi, ri) in wiring do
    eastWestEdgeFromPort c leftOuterPorts[pi]! rightNodes[ri]!
  let innerGraph ← nestedGraph leftOuterNode
  let innerNodes ← addNodes c innerGraph (← makeLayer innerGraph) n
  let dummies ← addExternalPortDummies c (← makeLayer innerGraph) leftOuterPorts
  for i in [0:n] do
    eastWestEdgeFromTo c innerNodes[i]! dummies[i]!
  return (g, leftOuterNode, leftOuterPorts)

/-- `distribute_ports_double_cross_between_compound_and_non_compound_nodes_switches_ports`. -/
def gDoubleCrossCompound : LayeredM (Bool × Bool) := do
  let (g, outer, _) ← gCompound 2 #[(0, 1), (0, 1), (1, 0)]
  let (d, order) ← prepareGreedy g
  let o ← portsOf outer
  let improved ← d.distributePortsWhileSweeping order 0 false
  return (improved, (← portsOf outer) == #[o[1]!, o[0]!])

/-- `distribute_ports_single_cross_between_compound_and_non_compound_nodes_no_switch`. -/
def gSingleCrossCompound : LayeredM Bool := do
  let (g, outer, outerPorts) ← gCompound 2 #[(0, 1), (1, 0)]
  let (d, order) ← prepareGreedy g
  let _ ← d.distributePortsWhileSweeping order 0 false
  return (← portsOf outer) == outerPorts

/-- `distribute_ports_more_hierarchical_nodes_no_switch`. -/
def gMoreHierarchicalNodes : LayeredM Bool := do
  let (g, outer, outerPorts) ← gCompound 3 #[(0, 1), (1, 0), (2, 2)]
  let (d, order) ← prepareGreedy g
  let _ ← d.distributePortsWhileSweeping order 0 false
  return (← portsOf outer) == outerPorts

/-- `distribute_ports_more_hierarchical_nodes_variant_no_switch`: the nested graph has a left
inner node wired to the third of three right inner nodes, which feed the dummies. -/
def gMoreHierarchicalNodesVariant : LayeredM Bool := do
  let c := gCfg
  let g ← newGraph { options := true }
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let leftOuterNode ← addNode c g leftLayer
  let rightNodes ← addNodes c g rightLayer 3
  let leftOuterPorts ← addPorts c leftOuterNode 3 .east
  eastWestEdgeFromPort c leftOuterPorts[0]! rightNodes[1]!
  eastWestEdgeFromPort c leftOuterPorts[1]! rightNodes[0]!
  eastWestEdgeFromPort c leftOuterPorts[2]! rightNodes[2]!
  let innerGraph ← nestedGraph leftOuterNode
  let leftInnerNode ← addNode c innerGraph (← makeLayer innerGraph)
  let rightInnerNodes ← addNodes c innerGraph (← makeLayer innerGraph) 3
  let dummyNodes ← addExternalPortDummies c (← makeLayer innerGraph) leftOuterPorts
  eastWestEdgeFromTo c leftInnerNode rightInnerNodes[2]!
  eastWestEdgeFromTo c rightInnerNodes[0]! dummyNodes[0]!
  eastWestEdgeFromTo c rightInnerNodes[1]! dummyNodes[1]!
  eastWestEdgeFromTo c rightInnerNodes[2]! dummyNodes[2]!
  let (d, order) ← prepareGreedy g
  let o ← portsOf leftOuterNode
  let _ ← d.distributePortsWhileSweeping order 0 false
  return (← portsOf leftOuterNode) == o

/-- `distribute_ports_two_nodes_in_one_layer_no_switch`: two copies of a crossed pair; the first
left node's ports are switched. -/
def gTwoNodesInOneLayer : LayeredM Bool := do
  let c := gCfg
  let g ← newGraph { options := true }
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  for _ in [0:2] do
    let leftNodes ← addNodes c g leftLayer 1
    let rightNodes ← addNodes c g rightLayer 2
    eastWestEdgeFromTo c leftNodes[0]! rightNodes[1]!
    eastWestEdgeFromTo c leftNodes[0]! rightNodes[0]!
  let leftOuterNode := (← getLayer leftLayer).nodes[0]!
  let (d, order) ← prepareGreedy g
  let o ← portsOf leftOuterNode
  let _ ← d.distributePortsWhileSweeping order 0 false
  return (← portsOf leftOuterNode) == #[o[1]!, o[0]!]

def greedyTests : Suite := suite "layered.p3order.greedy_port_distributor" do
  let (improved, switched) ← runL gWesternCross
  check "distribute_ports_cross_on_western_side_removes_crossing (improved)" improved
  check "distribute_ports_cross_on_western_side_removes_crossing (order)" switched
  let (improved, unchanged) ← runL gNoPortsOnRightSide
  check "distribute_ports_no_ports_on_right_side_no_change (not improved)" (!improved)
  check "distribute_ports_no_ports_on_right_side_no_change (order)" unchanged
  let (improved, switched) ← runL gMultipleWesternCrossings
  check "distribute_ports_multiple_crossings_on_western_side_removes_crossing (improved)" improved
  check "distribute_ports_multiple_crossings_on_western_side_removes_crossing (order)" switched
  let (improved, after, o) ← runL (gEasternCrossings false)
  check "distribute_ports_crossings_on_eastern_side_removes_them (improved)" improved
  checkEqR "distribute_ports_crossings_on_eastern_side_removes_them (order)" after #[o[1]!, o[0]!]
  let (improved, after, o) ← runL (gEasternCrossings true)
  check "distribute_ports_fixed_order_no_change (not improved)" (!improved)
  checkEqR "distribute_ports_fixed_order_no_change (order)" after o
  check "distribute_ports_no_change_in_ordered_case" (!(← runL gOrderedCase))
  let (improved, switched) ← runL gDoubleCrossCompound
  check "distribute_ports_double_cross_between_compound_and_non_compound_nodes_switches_ports (improved)" improved
  check "distribute_ports_double_cross_between_compound_and_non_compound_nodes_switches_ports (order)" switched
  check "distribute_ports_single_cross_between_compound_and_non_compound_nodes_no_switch" (← runL gSingleCrossCompound)
  check "distribute_ports_more_hierarchical_nodes_no_switch" (← runL gMoreHierarchicalNodes)
  check "distribute_ports_more_hierarchical_nodes_variant_no_switch" (← runL gMoreHierarchicalNodesVariant)
  check "distribute_ports_two_nodes_in_one_layer_no_switch" (← runL gTwoNodesInOneLayer)
  -- a distributor used before `initAfterTraversal` has no counter (Rust `expect`)
  checkThrows "distribution before initialisation throws" (runL do
    let g ← newGraph gCfg
    let _ ← addNode gCfg g (← makeLayer g)
    let d ← GreedyPortDistributor.new
    discard <| d.distributePortsWhileSweeping (← nodeArray g) 0 true)

/-! ## `ISweepPortDistributor.create` and the `BarycenterPortDistributor` view -/

/-- Runs `create` on the strategy graph (one forward step on layer 1) and on the western cross of
the greedy tests; returns whether `R` kept `[p, q]`, the greedy result and the generator. -/
def createRun (t : CrossMinType) (random : Random) : LayeredM (Bool × Bool × Random) := do
  let rnd ← IO.mkRef random
  let (order, r, p, q) ← strategyGraph
  let sd ← SweepPortDistributor.create t rnd order.size
  Initializable.init #[sd.initializable] order
  let _ ← sd.distributePortsWhileSweeping order 1 true
  let kept := (← portsOf r) == #[p, q]
  let g ← newGraph gCfg
  let leftNodes ← addNodes gCfg g (← makeLayer g) 2
  let rightNode ← addNode gCfg g (← makeLayer g)
  eastWestEdgeFromTo gCfg leftNodes[0]! rightNode
  eastWestEdgeFromTo gCfg leftNodes[1]! rightNode
  let order2 ← nodeArray g
  let sd2 ← SweepPortDistributor.create t rnd order2.size
  Initializable.init #[sd2.initializable] order2
  let improved ← sd2.distributePortsWhileSweeping order2 1 true
  return (kept, improved, ← rnd.get)

/-- The `BarycenterPortDistributor` view shares the state of the sweep view. -/
def barycenterViewRun : LayeredM (Array Float × Array Float) := do
  let (order, _) ← rankGraph
  let d ← NodeRelativePortDistributor.new order.size
  let view := d.toBarycenterPortDistributor
  Initializable.init #[d.toSweepPortDistributor.initializable] order
  view.calculatePortRanks order[0]! .output
  return (← view.portRanks, ← d.portRanks)

def createTests : Suite := suite "layered.p3order.i_sweep_port_distributor.create" do
  let r0 := Random.ofInt 0
  let (kept, improved, rnd) ← runL (createRun .barycenter (r0.setMockNextBoolean true))
  check "nextBoolean true creates the node-relative distributor (hand: [p, q])" kept
  check "barycenter distributors never report a change" (!improved)
  checkEq "the mocked generator is not advanced" rnd.seed r0.seed
  let (kept, _, _) ← runL (createRun .oneSidedGreedySwitch (r0.setMockNextBoolean false))
  check "nextBoolean false creates the layer-total distributor (hand: [q, p])" (!kept)
  let (_, improved, rnd) ← runL (createRun .twoSidedGreedySwitch r0)
  check "TWO_SIDED_GREEDY_SWITCH creates the greedy distributor (reports the switch)" improved
  checkEq "the greedy choice draws no random number" rnd.seed r0.seed
  let (kept, _, rnd) ← runL (createRun .barycenter r0)
  check "Random(0).nextBoolean() = true picks node-relative" kept
  check "a real draw advances the shared generator" (rnd.seed != r0.seed)
  let (viewRanks, ranks) ← runL barycenterViewRun
  checkRanks "BarycenterPortDistributor.portRanks (hand: nx 0.25, x1 0.5, x2 0.75)" viewRanks
    #[0.25, 0.5, 0.75, 0.0, 0.0, 0.0, 0.0, 0.0]
  checkRanks "the view shares the distributor state" ranks viewRanks

/-! ## `forster_constraint_resolver_test.rs` -/

/-- `create_graph_with_layer()` with `count` normal nodes (`create_node`). -/
def forsterGraph (count : Nat) : LayeredM (LayerId × Array LNodeId) := do
  let g ← newGraph {}
  let l ← makeLayer g
  let nodes ← addNodes {} g l count
  return (l, nodes)

/-- `set_layout_unit(node, representative)`. -/
def setLayoutUnit (n unit : LNodeId) : LayeredM Unit :=
  modifyNode n fun x => { x with internal := { x.internal with inLayerLayoutUnit := some unit } }

/-- `prepare_resolver(nodes)`: layer `0` and its nodes initialised, barycenter = index. -/
def prepareResolver (nodes : Array LNodeId) (betweenNonDummies : Bool := false) : LayeredM ForsterConstraintResolver := do
  let order := #[nodes]
  let r ← ForsterConstraintResolver.new order betweenNonDummies
  r.initAtLayerLevel 0 order
  for i in [0:nodes.size] do
    r.initAtNodeLevel 0 i order
  r.barycenterStates.modify fun s => s.modify 0 fun l => l.mapIdx fun i o => o.map fun st => st.setBarycenter (some i.toFloat)
  return r

/-- `assert_successor_constraints_respected(nodes)`: no successor precedes its node. -/
def successorConstraintsRespected (nodes : Array LNodeId) : LayeredM Bool := do
  let mut encountered : Array LNodeId := #[]
  for n in nodes do
    let successors := (← getNode n).internal.inLayerSuccessorConstraints
    if successors.any (encountered.contains ·) then return false
    encountered := encountered.push n
  return true

/-- `assert_non_overlapping_layout_units(nodes)`: every layout unit is contiguous. -/
def nonOverlappingLayoutUnits (nodes : Array LNodeId) : LayeredM Bool := do
  let mut encountered : Array LNodeId := #[]
  let mut current : Option LNodeId := none
  for n in nodes do
    if let some unit := (← getNode n).internal.inLayerLayoutUnit then
      if some unit != current then
        if encountered.contains unit then return false
        if let some previous := current then encountered := encountered.push previous
        current := some unit
  return true

/-- The barycenters of the nodes' states (by node id). -/
def barycentersOf (r : ForsterConstraintResolver) (nodes : Array LNodeId) : LayeredM (Array (Option Float)) := do
  let states ← r.getBarycenterStates
  nodes.mapM fun n => do
    let nid := (← getNode n).id.toNat
    return ((states[0]?.bind (·[nid]?)).bind _root_.id).bind (·.barycenter)

/-- `test_successor_constraints`: `a → b` with order `[b, a, c]` (barycenters `0, 1, 2`). -/
def fSuccessorConstraints : LayeredM (Bool × Bool × Array (Option Float)) := do
  let (_, ns) ← forsterGraph 3
  let (a, b, c) := (ns[0]!, ns[1]!, ns[2]!)
  modifyNode a fun x => { x with internal := { x.internal with inLayerSuccessorConstraints := #[b] } }
  let r ← prepareResolver #[b, a, c]
  let result ← r.processConstraints #[b, a, c]
  return (← successorConstraintsRespected result, result == #[a, b, c], ← barycentersOf r #[a, b, c])

/-- `test_non_overlapping_layout_units`: units `{a1, a2}`, `{b1}`, `{c1}` in order `[a1, b1, a2, c1]`. -/
def fNonOverlappingLayoutUnits : LayeredM (Bool × Bool × Array (Option Float)) := do
  let (_, ns) ← forsterGraph 4
  let (a1, b1, a2, c1) := (ns[0]!, ns[1]!, ns[2]!, ns[3]!)
  setLayoutUnit a1 a1
  setLayoutUnit a2 a1
  setLayoutUnit b1 b1
  setLayoutUnit c1 c1
  let order := #[a1, b1, a2, c1]
  let r ← prepareResolver order
  let result ← r.processConstraints order
  return (← nonOverlappingLayoutUnits result, result == #[a1, a2, b1, c1], ← barycentersOf r #[a1, a2, b1, c1])

/-- A normal node `n` with a north/south dummy `d` (layout unit `n`, constraint `d → n`) in the
order `[n, d]` (barycenters `0, 1`). -/
def fNorthSouthDummy : LayeredM (Bool × Array (Option Float)) := do
  let (_, ns) ← forsterGraph 2
  let (n, d) := (ns[0]!, ns[1]!)
  setLayoutUnit n n
  setLayoutUnit d n
  modifyNode d fun x => { x with type := .northSouthPort, internal := { x.internal with inLayerSuccessorConstraints := #[n] } }
  let r ← prepareResolver #[n, d]
  let result ← r.processConstraints #[n, d]
  return (result == #[d, n], ← barycentersOf r #[d, n])

/-- `constraintsBetweenNonDummies`: `[b, a]` with `a → b` is resolved among normal nodes first;
after the re-initialisation the equal barycenters do not violate the constraint again. -/
def fBetweenNonDummies : LayeredM (Bool × Array (Option Float) × Nat) := do
  let (_, ns) ← forsterGraph 2
  let (a, b) := (ns[0]!, ns[1]!)
  modifyNode a fun x => { x with internal := { x.internal with inLayerSuccessorConstraints := #[b] } }
  let r ← prepareResolver #[b, a] true
  let result ← r.processConstraints #[b, a]
  return (result == #[a, b], ← barycentersOf r #[a, b], (← r.constraintGroupArena.get).size)

/-- With a snapshot the captured ids are used: the live ids are scrambled after building it. -/
def fSnapshotIds : LayeredM Bool := do
  let (_, ns) ← forsterGraph 3
  let (a, b, c) := (ns[0]!, ns[1]!, ns[2]!)
  modifyNode a fun x => { x with internal := { x.internal with inLayerSuccessorConstraints := #[b] } }
  let order := #[b, a, c]
  let r ← prepareResolver order
  r.setSnapshot (← CrossMinSnapshot.build #[order] 0)
  for n in order do
    modifyNode n fun x => { x with id := 99 }
  return (← r.processConstraints order) == #[a, b, c]

/-- `initAtLayerLevel` sets `Layer.id` to the layer index. -/
def fLayerIds : LayeredM (Array Int) := do
  let g ← newGraph {}
  let l0 ← makeLayer g
  let l1 ← makeLayer g
  let n0 ← addNode {} g l0
  let n1 ← addNode {} g l1
  modifyLayer l0 fun x => { x with id := 7 }
  modifyLayer l1 fun x => { x with id := 7 }
  let order := #[#[n0], #[n1]]
  let r ← ForsterConstraintResolver.new order false
  Initializable.init #[r.initializable] order
  return #[(← getLayer l0).id, (← getLayer l1).id]

def forsterTests : Suite := suite "layered.p3order.forster_constraint_resolver" do
  let (respected, order, barys) ← runL fSuccessorConstraints
  check "test_successor_constraints" respected
  check "test_successor_constraints order (hand: [a, b, c])" order
  checkEqR "test_successor_constraints barycenters (hand: merged (1 + 0) / 2)" barys #[some 0.5, some 0.5, some 2.0]
  let (nonOverlapping, order, barys) ← runL fNonOverlappingLayoutUnits
  check "test_non_overlapping_layout_units" nonOverlapping
  check "test_non_overlapping_layout_units order (hand: [a1, a2, b1, c1])" order
  checkEqR "test_non_overlapping_layout_units barycenters (hand: a2/b1 merged (2 + 1) / 2)" barys
    #[some 0.0, some 1.5, some 1.5, some 3.0]
  let (order, barys) ← runL fNorthSouthDummy
  check "north dummy moves above its node (hand: [d, n])" order
  checkEqR "north dummy group barycenter (hand: 0.5, 0.5)" barys #[some 0.5, some 0.5]
  let (order, barys, groups) ← runL fBetweenNonDummies
  check "constraints between non-dummies resolved first (hand: [a, b])" order
  checkEqR "constraints between non-dummies barycenters (hand: 0.5, 0.5)" barys #[some 0.5, some 0.5]
  checkEq "constraint groups created (hand: 2 + 1 merged + 2 re-initialised)" groups 5
  check "the snapshot's ids are used once set" (← runL fSnapshotIds)
  checkEqR "initAtLayerLevel sets the layer ids (hand: [0, 1])" (← runL fLayerIds) #[0, 1]
  checkThrows "a node without constraint group throws" (runL do
    let g ← newGraph {}
    let l0 ← makeLayer g
    let l1 ← makeLayer g
    let n0 ← addNode {} g l0
    let n1 ← addNode {} g l1
    let r ← ForsterConstraintResolver.new #[#[n0]] false
    Initializable.init #[r.initializable] #[#[n0]]
    modifyLayer l1 fun x => { x with id := 1 }
    discard <| r.processConstraints #[n1])

/-! ## Differential test: `ForsterFast` = `ForsterM` -/

/-- All fields of a barycenter state (float bits). -/
def stateKey : Option BarycenterState → Option (Nat × UInt64 × Int × UInt64 × Bool × Bool)
  | none => none
  | some st => some (st.node.idx, st.summedWeight.toBits, st.degree, st.barycenterValue.toBits, st.hasBarycenter, st.visited)

/-- All fields of a constraint group (float bits). -/
def groupKey (g : ConstraintGroup) : UInt64 × Int × Array Nat × Array Nat × Array Nat × Nat :=
  (g.summedWeight.toBits, g.degree, g.nodes.map (·.idx), g.outgoingConstraints, g.incomingConstraints,
    g.incomingConstraintsCount)

/-- Whether two resolvers have the same state (groups, barycenter states, group table, units). -/
def sameResolverState (r1 r2 : ForsterConstraintResolver) : BaseIO Bool := do
  let a1 := (← r1.constraintGroupArena.get).map groupKey
  let a2 := (← r2.constraintGroupArena.get).map groupKey
  let s1 := (← r1.barycenterStates.get).map (·.map stateKey)
  let s2 := (← r2.barycenterStates.get).map (·.map stateKey)
  let t1 ← r1.constraintGroups.get
  let t2 ← r2.constraintGroups.get
  let u1 := (← r1.layoutUnits.get).size
  let u2 := (← r2.layoutUnits.get).size
  return a1 == a2 && s1 == s2 && t1 == t2 && u1 == u2

/-- One random layer: north/south dummies in layout units of other nodes, random successor
constraints (cycles included), random barycenters with unknown ones and `f32` ties, and several
`process_constraints` calls on random permutations (sometimes without one node) through both
implementations. Whether results and states agree after every call, and the number of calls that
merged groups. -/
def forsterRandomRun (r : IO.Ref Random) : LayeredM (Bool × Nat) := do
  let n := 2 + (← rnd r 12)
  let (_, ns) ← forsterGraph n
  for h : i in [0:ns.size] do
    if i > 0 && (← rnd r 3) == 0 then
      let owner := ns[← rnd r i]!
      setLayoutUnit owner owner
      setLayoutUnit ns[i] owner
      if (← rnd r 4) != 0 then modifyNode ns[i] fun x => { x with type := .northSouthPort }
  for _ in [0:(← rnd r (2 * n + 1))] do
    let a := ns[← rnd r n]!
    let b := ns[← rnd r n]!
    if a != b then
      modifyNode a fun x => { x with internal := { x.internal with
        inLayerSuccessorConstraints := x.internal.inLayerSuccessorConstraints.push b } }
  let between := (← rnd r 2) == 0
  let order := #[ns]
  let r1 ← ForsterConstraintResolver.new order between
  let r2 ← ForsterConstraintResolver.new order between
  for res in [r1, r2] do
    res.initAtLayerLevel 0 order
    for i in [0:n] do
      res.initAtNodeLevel 0 i order
  let values : Array Float := #[0.0, 0.5, 1.0, 1.0 + 1e-12, 2.0]
  let mut same := true
  let mut merging := 0
  for _ in [0:4] do
    let mut barys : Array (Option Float) := #[]
    for _ in [0:n] do
      let k ← rnd r (values.size + 1)
      barys := barys.push values[k]?
    for res in [r1, r2] do
      res.barycenterStates.modify fun s => s.modify 0 fun l => l.mapIdx fun i o => o.map fun st => st.setBarycenter (barys[i]?.getD none)
    let mut perm ← shuffle r ns
    if (← rnd r 5) == 0 then perm := perm.pop
    let groupsBefore := (← r1.constraintGroupArena.get).size
    let out1 ← r1.processConstraints perm
    let out2 ← r2.processConstraintsPort perm
    same := same && out1 == out2 && (← sameResolverState r1 r2)
    if (← r1.constraintGroupArena.get).size > groupsBefore + (if between then perm.size else 0) then
      merging := merging + 1
  return (same, merging)

def forsterFastTests : Suite := suite "layered.p3order.forster_fast" do
  let mut mismatches := 0
  let mut merging := 0
  for seed in [0:500] do
    let r ← IO.mkRef (Random.ofInt seed)
    let (same, m) ← runL (forsterRandomRun r)
    if !same then mismatches := mismatches + 1
    merging := merging + m
  checkEq "forster fast = port (500 random layers, 2000 calls)" mismatches 0
  check s!"forster differential calls merge groups ({merging} calls)" (merging > 500)

/-! ## Suites -/

def suites : Array Suite := #[abstractBarycenterTests, handBarycenterTests, greedyTests, createTests, forsterTests,
  forsterFastTests]

end Tests.Layered.P3PortDistributors
