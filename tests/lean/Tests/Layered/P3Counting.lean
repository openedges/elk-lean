import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.P3Order.CrossMinSnapshot
import Elk.Alg.Layered.Intermediate.GreedySwitch
/-!
Tests of `org.eclipse.elk.alg.layered.p3order.counting` and the greedy switch counters, ported
from elk-rs `tests/p3_order/counting/*.rs` and `tests/p3_order/cross_min_util_test.rs` (check
names are the Rust test names). The graph builders mirror the per-file Rust helpers; their small
differences (layout unit on new nodes, `FIXED_SIDE` on new ports, graph property flags, the extra
north/south bookkeeping) are selected with a `Cfg`.
-/
namespace Tests.Layered.P3Counting

open Tests Elk.Graph Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open Elk.Alg.Layered.P3Order Elk.Alg.Layered.P3Order.Counting Elk.Alg.Layered.Intermediate.GreedySwitch
open LayeredM

/-! ## Graph builders -/

/-- Which variant of the Rust test helpers to use. -/
structure Cfg where
  /-- `new_graph()` sets `EDGE_ROUTING`, `HIERARCHY_HANDLING` and `RANDOM`. -/
  options : Bool := false
  /-- `add_node_to_layer` sets `IN_LAYER_LAYOUT_UNIT` to the node itself. -/
  selfUnit : Bool := false
  /-- `add_port_on_side` sets `PORT_CONSTRAINTS = FIXED_SIDE` unless the sides are fixed. -/
  fixSide : Bool := false
  /-- `set_fixed_order_constraint` also flags `NON_FREE_PORTS` on the graph. -/
  graphProps : Bool := false
  /-- `add_north_south_edge` also sets `BARYCENTER_ASSOCIATES` and successor constraints. -/
  full : Bool := false

/-- `new_graph()` / `LGraph::new()`. -/
def newGraph (c : Cfg) : LayeredM LGraphId := do
  let g ← createGraph
  if c.options then
    setGraphProp g LayeredOptions.EDGE_ROUTING EdgeRouting.orthogonal
    setGraphProp g LayeredOptions.HIERARCHY_HANDLING HierarchyHandling.includeChildren
    modifyGraph g fun x => { x with internal := { x.internal with random := some (Random.ofInt 0) } }
  return g

/-- `make_layer(graph)`. -/
def makeLayer (g : LGraphId) : LayeredM LayerId := do
  let l ← createLayer g
  modifyGraph g fun x => { x with layers := x.layers.push l }
  return l

/-- `make_layers(graph, count)`. -/
def makeLayers (g : LGraphId) (count : Nat) : LayeredM (Array LayerId) := do
  let mut ls := #[]
  for _ in [0:count] do ls := ls.push (← makeLayer g)
  return ls

/-- `add_node_to_layer(graph, layer)`. -/
def addNode (c : Cfg) (g : LGraphId) (l : LayerId) : LayeredM LNodeId := do
  let n ← createNode g
  if c.selfUnit then
    modifyNode n fun x => { x with internal := { x.internal with inLayerLayoutUnit := some n } }
  setNodeLayer n (some l)
  return n

/-- `add_nodes_to_layer(graph, layer, count)`. -/
def addNodes (c : Cfg) (g : LGraphId) (l : LayerId) (count : Nat) : LayeredM (Array LNodeId) := do
  let mut ns := #[]
  for _ in [0:count] do ns := ns.push (← addNode c g l)
  return ns

/-- `add_port_on_side(node, side)`. -/
def addPort (c : Cfg) (n : LNodeId) (side : PortSide) : LayeredM LPortId := do
  let p ← createPort
  modifyPort p (·.setSide side)
  setPortNode p (some n)
  if c.fixSide then
    let constraints ← getNodePropD n LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
    if !constraints.isSideFixed then setNodeProp n LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
  return p

/-- `add_ports_on_side(node, count, side)`. -/
def addPorts (c : Cfg) (n : LNodeId) (count : Nat) (side : PortSide) : LayeredM (Array LPortId) := do
  let mut ps := #[]
  for _ in [0:count] do ps := ps.push (← addPort c n side)
  return ps

/-- `add_edge_between_ports(source, target)` / `connect`. -/
def connect (s t : LPortId) : LayeredM Unit := do
  let e ← createEdge
  setEdgeSource e (some s)
  setEdgeTarget e (some t)

/-- `east_west_edge_from_to(left, right)`. -/
def eastWestEdgeFromTo (c : Cfg) (left right : LNodeId) : LayeredM Unit := do
  let s ← addPort c left .east
  let t ← addPort c right .west
  connect s t

/-- `east_west_edge_from_port(left_port, right)`. -/
def eastWestEdgeFromPort (c : Cfg) (leftPort : LPortId) (right : LNodeId) : LayeredM Unit := do
  connect leftPort (← addPort c right .west)

/-- `east_west_edge_from_node(left, right_port)`. -/
def eastWestEdgeFromNode (c : Cfg) (left : LNodeId) (rightPort : LPortId) : LayeredM Unit := do
  connect (← addPort c left .east) rightPort

/-- `add_in_layer_edge(node_one, node_two, side)`. -/
def addInLayerEdge (c : Cfg) (n1 n2 : LNodeId) (side : PortSide) : LayeredM Unit := do
  let p1 ← addPort c n1 side
  let p2 ← addPort c n2 side
  connect p1 p2

/-- `self_loop_on(node, side)`: two ports of the node connected. -/
def selfLoopOn (c : Cfg) (n : LNodeId) (side : PortSide) : LayeredM Unit := do
  let p ← addPort c n side
  let t ← addPort c n side
  connect p t

/-- `add_self_loop(node, side)` (crossings counter test): one port connected to itself. -/
def addSelfLoop (c : Cfg) (n : LNodeId) (side : PortSide) : LayeredM Unit := do
  let p ← addPort c n side
  connect p p

/-- Inserts a flag into the graph's `GRAPH_PROPERTIES`. -/
def addGraphProperty (n : LNodeId) (prop : GraphProperties) : LayeredM Unit := do
  if let some g ← nodeGraph n then
    modifyGraph g fun x => { x with internal := { x.internal with graphProperties := x.internal.graphProperties.insert prop } }

/-- `set_fixed_order_constraint(node)`. -/
def setFixedOrderConstraint (c : Cfg) (n : LNodeId) : LayeredM Unit := do
  setNodeProp n LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedOrder
  if c.graphProps then addGraphProperty n .nonFreePorts

/-- `set_as_long_edge_dummy(node)`: `LONG_EDGE` without layout unit. -/
def setAsLongEdgeDummy (n : LNodeId) : LayeredM Unit :=
  modifyNode n fun x => { x with type := .longEdge, internal := { x.internal with inLayerLayoutUnit := none } }

/-- `set_node_type_long_edge(node)`. -/
def setNodeTypeLongEdge (n : LNodeId) : LayeredM Unit := modifyNode n fun x => { x with type := .longEdge }

/-- Index of the node's layer (`0` without one). -/
def layerIndexOfNode (n : LNodeId) : LayeredM Nat := do
  let a ← get
  return ((a.node n).layer.bind a.layerIndex).getD 0

/-- `add_north_south_edge(side, node_with_ns_ports, north_south_dummy, node_with_east_west_ports,
node_with_east_west_ports_is_origin)`. -/
def addNorthSouthEdge (c : Cfg) (side : PortSide) (nsNode dummy ewNode : LNodeId) (ewIsOrigin : Bool) : LayeredM Unit := do
  let nsLayerIndex ← layerIndexOfNode nsNode
  let otherLayerIndex ← layerIndexOfNode ewNode
  let direction : PortSide := if otherLayerIndex < nsLayerIndex then .west else .east
  let normalNodePort ← addPort c ewNode direction.opposed
  let dummyNodePort ← addPort c dummy direction
  if ewIsOrigin then connect normalNodePort dummyNodePort else connect dummyNodePort normalNodePort
  modifyNode dummy fun x => { x with
    type := .northSouthPort
    internal := { x.internal with inLayerLayoutUnit := some nsNode, origin := some (.lNode nsNode) } }
  let originPort ← addPort c nsNode side
  modifyPort dummyNodePort fun x => { x with internal := { x.internal with origin := some (.lPort originPort) } }
  modifyPort originPort fun x => { x with internal := { x.internal with portDummy := some dummy } }
  if c.full then
    modifyNode nsNode fun x => { x with internal := { x.internal with barycenterAssociates := #[dummy] ++ x.internal.barycenterAssociates } }
    if side == .north then
      modifyNode dummy fun x => { x with internal := { x.internal with
        inLayerSuccessorConstraints := x.internal.inLayerSuccessorConstraints.push nsNode } }
    else
      modifyNode nsNode fun x => { x with internal := { x.internal with
        inLayerSuccessorConstraints := x.internal.inLayerSuccessorConstraints.push dummy } }
  addGraphProperty nsNode .northSouthPorts

/-- `assign_ids(graph)`: layer and node ids; port ids in traversal order when `withPorts`.
Returns the number of ports numbered. -/
def assignIds (g : LGraphId) (withPorts : Bool := true) : LayeredM Nat := do
  let mut portId : Nat := 0
  let layers := (← getGraph g).layers
  for h : li in [0:layers.size] do
    let l := layers[li]
    modifyLayer l fun x => { x with id := li }
    let nodes := (← getLayer l).nodes
    for h2 : ni in [0:nodes.size] do
      let n := nodes[ni]
      modifyNode n fun x => { x with id := ni }
      if withPorts then
        for p in (← getNode n).ports do
          let id : Int := portId
          modifyPort p fun x => { x with id := id }
          portId := portId + 1
  return portId

/-- `graph.to_node_array()`. -/
def nodeArray (g : LGraphId) : LayeredM (Array (Array LNodeId)) := do return (← get).graphToNodeArray g

/-- Runs a builder/counter on a fresh arena. -/
def runL {α : Type} (x : LayeredM α) : IO α := do
  let (r, _) ← LayeredM.run x
  return r

/-! ## `binary_indexed_tree_test.rs` -/

def bitTests : Suite := suite "layered.p3counting.binary_indexed_tree" do
  let ft := (((BinaryIndexedTree.new 5).add 1).add 2).add 1
  checkEq "sum_before rank(1)" (ft.rank 1) 0
  checkEq "sum_before rank(2)" (ft.rank 2) 2
  let ft := (((BinaryIndexedTree.new 5).add 2).add 1).add 1
  checkEq "size" ft.size 3
  let ft := ((((BinaryIndexedTree.new 5).add 0).add 2).add 1).add 1
  let ft := ft.removeAll 1
  checkEq "remove_all size" ft.size 2
  checkEq "remove_all rank(2)" (ft.rank 2) 1
  let ft := ft.removeAll 1
  checkEq "remove_all twice size" ft.size 2
  checkEq "remove_all twice rank(2)" (ft.rank 2) 1
  let ft := (((BinaryIndexedTree.new 2).add 0).add 1).add 1
  checkEq "rank_with_out_of_bounds_index_returns_prefix_sum_up_to_max" (ft.rank 18446744073709551615) 3
  let ft := ft.clear
  checkEq "clear empties" (ft.isEmpty, ft.rank 2) (true, 0)

/-! ## `cross_min_util_test.rs` -/

def crossMinUtilTests : Suite := suite "layered.p3counting.cross_min_util" do
  let c : Cfg := {}
  let r ← runL do
    let g ← newGraph c
    let node ← createNode g
    let northA ← addPort c node .north
    let northB ← addPort c node .north
    let eastA ← addPort c node .east
    let eastB ← addPort c node .east
    let southA ← addPort c node .south
    let southB ← addPort c node .south
    let westA ← addPort c node .west
    let westB ← addPort c node .west
    let a ← get
    return (CrossMinUtil.inNorthSouthEastWestOrder a node .north == #[northA, northB],
      CrossMinUtil.inNorthSouthEastWestOrder a node .east == #[eastA, eastB],
      CrossMinUtil.inNorthSouthEastWestOrder a node .south == #[southB, southA],
      CrossMinUtil.inNorthSouthEastWestOrder a node .west == #[westB, westA])
  checkEq "in_north_south_east_west_order_respects_side_direction" r (true, true, true, true)

/-! ## `crossings_counter_test.rs` -/

/-- Helper variant of `crossings_counter_test.rs`. -/
def ccCfg : Cfg := {}

/-- Two layers of the graph (`left_layer`, `right_layer`). -/
def twoLayers (g : LGraphId) : LayeredM (LayerId × LayerId) := do
  let l ← makeLayer g
  let r ← makeLayer g
  return (l, r)

/-- `count_crossings_between_layers` on the first two layers with a fresh counter. -/
def countBetweenFirstLayers (g : LGraphId) : LayeredM Int := do
  let order ← nodeArray g
  let counter ← CrossingsCounter.ofPositions #[]
  counter.countCrossingsBetweenLayers order[0]! order[1]!

def crossingsCounterTests : Suite := suite "layered.p3counting.crossings_counter" do
  let c := ccCfg
  -- init_for_counting_between_handles_empty_layer
  let ok ← runL do
    let g ← newGraph c
    let (l, _) ← twoLayers g
    let leftNode ← addNode c g l
    let _ ← addPort c leftNode .east
    let _ ← assignIds g
    let counter ← CrossingsCounter.ofPositions #[]
    counter.initForCountingBetween #[leftNode] #[]
    return true
  check "init_for_counting_between_handles_empty_layer" ok
  -- count_crossings_between_layers_simple
  let r ← runL do
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let lt ← addNode c g l; let lb ← addNode c g l
    let rt ← addNode c g r; let rb ← addNode c g r
    let ltp ← addPort c lt .east; let lbp ← addPort c lb .east
    let rtp ← addPort c rt .west; let rbp ← addPort c rb .west
    connect ltp rbp; connect lbp rtp
    let _ ← assignIds g
    countBetweenFirstLayers g
  checkEq "count_crossings_between_layers_simple" r 1
  -- count_in_layer_crossings_simple / long_in_layer_crossings
  for name in #["count_in_layer_crossings_simple", "long_in_layer_crossings"] do
    let r ← runL do
      let g ← newGraph c
      let l ← makeLayer g
      let nodes ← addNodes c g l 5
      addInLayerEdge c nodes[0]! nodes[1]! .east
      addInLayerEdge c nodes[1]! nodes[3]! .east
      addInLayerEdge c nodes[2]! nodes[4]! .east
      let _ ← assignIds g
      let counter ← CrossingsCounter.ofPositions #[]
      counter.countInLayerCrossingsOnSide (← nodeArray g)[0]! .east
    checkEq name r 1
  -- count_crossings_between_layers_parallel_edges
  let r ← runL do
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let left ← addNode c g l; let right ← addNode c g r
    let lpa ← addPort c left .east; let rpa ← addPort c right .west
    connect lpa rpa
    let lpb ← addPort c left .east; let rpb ← addPort c right .west
    connect lpb rpb
    let _ ← assignIds g
    countBetweenFirstLayers g
  checkEq "count_crossings_between_layers_parallel_edges" r 1
  -- count_crossings_between_layers_cross_with_middle_edge
  let r ← runL do
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let ln ← addNodes c g l 3; let rn ← addNodes c g r 3
    let lt ← addPort c ln[0]! .east; let lm ← addPort c ln[1]! .east; let lb ← addPort c ln[2]! .east
    let rt ← addPort c rn[0]! .west; let rm ← addPort c rn[1]! .west; let rb ← addPort c rn[2]! .west
    connect lt rb; connect lm rm; connect lb rt
    let _ ← assignIds g
    countBetweenFirstLayers g
  checkEq "count_crossings_between_layers_cross_with_middle_edge" r 3
  -- count_crossings_between_layers_ignore_self_loops
  let r ← runL do
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let tl ← addNode c g l; let bl ← addNode c g l
    let tr ← addNode c g r; let br ← addNode c g r
    let tlp ← addPort c tl .east; let blp ← addPort c bl .east
    let trp ← addPort c tr .west; let brp ← addPort c br .west
    connect tlp brp; connect blp trp
    for _ in [0:3] do
      addSelfLoop c tl .east; addSelfLoop c bl .east
      addSelfLoop c tr .west; addSelfLoop c br .west
    let _ ← assignIds g
    countBetweenFirstLayers g
  checkEq "count_crossings_between_layers_ignore_self_loops" r 1
  -- count_crossings_between_layers_into_same_port
  let r ← runL do
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let tl ← addNode c g l; let bl ← addNode c g l
    let tr ← addNode c g r; let br ← addNode c g r
    let tlp ← addPort c tl .east; let brp ← addPort c br .west
    connect tlp brp
    let bl1 ← addPort c bl .east; let bl2 ← addPort c bl .east
    let trp ← addPort c tr .west
    connect bl1 trp; connect bl2 trp
    let _ ← assignIds g
    countBetweenFirstLayers g
  checkEq "count_crossings_between_layers_into_same_port" r 2
  -- count_crossings_between_layers_cross_formed_multiple_edges_between_same_nodes
  let r ← runL do
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let tl ← addNode c g l; let bl ← addNode c g l
    let tr ← addNode c g r; let br ← addNode c g r
    let tltp ← addPort c tl .east; let tlbp ← addPort c tl .east
    let brbp ← addPort c br .west; let brtp ← addPort c br .west
    connect tltp brtp; connect tlbp brbp
    let bltp ← addPort c bl .east; let blbp ← addPort c bl .east
    let trbp ← addPort c tr .west; let trtp ← addPort c tr .west
    connect bltp trtp; connect blbp trbp
    let _ ← assignIds g
    countBetweenFirstLayers g
  checkEq "count_crossings_between_layers_cross_formed_multiple_edges_between_same_nodes" r 4
  -- count_crossings_between_ports_given_western_crossings_only_counts_for_given_ports
  let r ← runL do
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let ln ← addNodes c g l 2; let rn ← addNodes c g r 2
    let l0r1 ← addPort c ln[0]! .east; let r1p0 ← addPort c rn[1]! .west
    connect l0r1 r1p0
    let l1r1 ← addPort c ln[1]! .east; let r1p1 ← addPort c rn[1]! .west
    connect l1r1 r1p1
    let l1r0 ← addPort c ln[1]! .east; let r0p0 ← addPort c rn[0]! .west
    connect l1r0 r0p0
    let _ ← assignIds g
    let order ← nodeArray g
    let counter ← CrossingsCounter.ofPositions #[]
    counter.initForCountingBetween order[0]! order[1]!
    return (← counter.countCrossingsBetweenPortsInBothOrders r1p1 r1p0).1
  checkEq "count_crossings_between_ports_given_western_crossings_only_counts_for_given_ports" r 1
  -- count_crossings_between_ports_given_crossings_on_eastern_side
  let r ← runL do
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let leftNode ← addNode c g l; let rn ← addNodes c g r 2
    let lps ← addPorts c leftNode 2 .east
    let rt ← addPort c rn[0]! .west; let rb ← addPort c rn[1]! .west
    connect lps[0]! rb; connect lps[1]! rt
    let _ ← assignIds g
    let order ← nodeArray g
    let counter ← CrossingsCounter.ofPositions #[]
    counter.initForCountingBetween order[0]! order[1]!
    return (← counter.countCrossingsBetweenPortsInBothOrders lps[0]! lps[1]!).1
  checkEq "count_crossings_between_ports_given_crossings_on_eastern_side" r 1
  -- count_crossings_between_ports_two_edges_into_same_port
  let r ← runL do
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let tl ← addNode c g l; let bl ← addNode c g l
    let tr ← addNode c g r; let br ← addNode c g r
    let tlp ← addPort c tl .east; let brp ← addPort c br .west
    connect tlp brp
    let blp ← addPort c bl .east; let trp ← addPort c tr .west
    connect blp trp; connect blp trp
    let _ ← assignIds g
    let order ← nodeArray g
    let counter ← CrossingsCounter.ofPositions #[]
    counter.initForCountingBetween order[0]! order[1]!
    return (← counter.countCrossingsBetweenPortsInBothOrders blp tlp).1
  checkEq "count_crossings_between_ports_two_edges_into_same_port" r 2
  -- count_crossings_between_layers_fixed_port_order
  let r ← runL do
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let left ← addNode c g l; let right ← addNode c g r
    setNodeProp right LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedOrder
    let lpt ← addPort c left .east; let lpb ← addPort c left .east
    let rpt ← addPort c right .west; let rpb ← addPort c right .west
    connect lpt rpb; connect lpb rpt
    let _ ← assignIds g
    countBetweenFirstLayers g
  checkEq "count_crossings_between_layers_fixed_port_order" r 0
  -- count_crossings_between_layers_more_complex_three_layer_graph
  let r ← runL do
    let g ← newGraph c
    let l ← makeLayer g; let m ← makeLayer g; let r ← makeLayer g
    let ln ← addNodes c g l 3; let mn ← addNodes c g m 2; let rn ← addNodes c g r 3
    let l0 ← addPort c ln[0]! .east; let l1 ← addPort c ln[1]! .east; let l2 ← addPort c ln[2]! .east
    let m0a ← addPort c mn[0]! .west; let m0b ← addPort c mn[0]! .west; let m1a ← addPort c mn[1]! .west
    connect l0 m1a; connect l1 m0a; connect l2 m0b
    let m0e ← addPort c mn[0]! .east; let m1e ← addPort c mn[1]! .east
    let r0 ← addPort c rn[0]! .west; let r1 ← addPort c rn[1]! .west; let r2 ← addPort c rn[2]! .west
    connect m0e r0; connect m1e r2; connect m1e r1
    let _ ← assignIds g
    countBetweenFirstLayers g
  checkEq "count_crossings_between_layers_more_complex_three_layer_graph" r 3
  -- counting_two_different_graphs_does_not_interfere_with_each_other
  let r ← runL do
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let ln ← addNodes c g l 3; let rn ← addNodes c g r 3
    let lps ← addPorts c ln[1]! 2 .east
    eastWestEdgeFromTo c ln[2]! rn[1]!
    eastWestEdgeFromPort c lps[0]! rn[1]!
    eastWestEdgeFromPort c lps[1]! rn[0]!
    eastWestEdgeFromTo c ln[0]! rn[0]!
    let _ ← assignIds g
    let order ← nodeArray g
    let counter ← CrossingsCounter.ofPositions #[]
    counter.initForCountingBetween order[0]! order[1]!
    let first := (← counter.countCrossingsBetweenPortsInBothOrders lps[0]! lps[1]!).1
    counter.switchPorts lps[0]! lps[1]!
    let switched := (← counter.countCrossingsBetweenPortsInBothOrders lps[1]! lps[0]!).1
    return (first, switched)
  checkEq "counting_two_different_graphs_does_not_interfere_with_each_other" r (1, 0)

/-! ## `all_crossings_counter_test.rs` -/

/-- Helper variant of `all_crossings_counter_test.rs`. -/
def acCfg : Cfg := { selfUnit := true }

/-- `AllCrossingsCounter::new(order)` + `init_initializables` + `count_all_crossings(order)`. -/
def countAll (g : LGraphId) (order : Array (Array LNodeId)) : LayeredM Int := do
  let counter ← AllCrossingsCounter.new g order
  Initializable.init #[counter.initializable] order
  counter.countAllCrossings order

/-- The graph of `all_crossings_count_cross_form`. -/
def acCrossForm : LayeredM LGraphId := do
  let c := acCfg
  let g ← newGraph c
  let (l, r) ← twoLayers g
  let tl ← addNode c g l; let bl ← addNode c g l
  let tr ← addNode c g r; let br ← addNode c g r
  let tlp ← addPort c tl .east; let blp ← addPort c bl .east
  let trp ← addPort c tr .west; let brp ← addPort c br .west
  connect tlp brp; connect blp trp
  let _ ← assignIds g (withPorts := false)
  return g

/-- `graph_with_north_south_crossing(side, include_long_edge_dummy)`. -/
def acGraphWithNorthSouthCrossing (side : PortSide) (includeLongEdgeDummy : Bool) : LayeredM LGraphId := do
  let c := acCfg
  let g ← newGraph c
  let l ← makeLayer g; let m ← makeLayer g; let r ← makeLayer g
  let ln ← addNodes c g l 1; let mn ← addNodes c g m 4; let rn ← addNodes c g r 3
  let ltd ← addPort c ln[0]! .east; let dfl ← addPort c mn[2]! .west
  connect ltd dfl
  let dtr ← addPort c mn[2]! .east; let rfd ← addPort c rn[2]! .west
  connect dtr rfd
  if includeLongEdgeDummy then setAsLongEdgeDummy mn[2]!
  addNorthSouthEdge c side mn[3]! mn[0]! rn[0]! false
  addNorthSouthEdge c side mn[3]! mn[1]! rn[1]! false
  let _ ← assignIds g (withPorts := false)
  return g

/-- `graph_multiple_north_south_and_long_edge_dummies_on_both_sides()` (all crossings variant). -/
def acGraphMultipleNorthSouthAndLongEdgeDummies : LayeredM LGraphId := do
  let c := acCfg
  let g ← newGraph c
  let l ← makeLayer g; let m ← makeLayer g; let r ← makeLayer g
  let ln ← addNodes c g l 2; let mn ← addNodes c g m 7; let rn ← addNodes c g r 6
  let a ← addPort c ln[0]! .east; let b ← addPort c mn[2]! .west
  connect a b
  let a ← addPort c mn[2]! .east; let b ← addPort c rn[2]! .west
  connect a b
  let a ← addPort c ln[1]! .east; let b ← addPort c mn[4]! .west
  connect a b
  let a ← addPort c mn[4]! .east; let b ← addPort c rn[3]! .west
  connect a b
  setAsLongEdgeDummy mn[2]!
  setAsLongEdgeDummy mn[4]!
  addNorthSouthEdge c .north mn[3]! mn[0]! rn[0]! false
  addNorthSouthEdge c .north mn[3]! mn[1]! rn[1]! false
  addNorthSouthEdge c .south mn[3]! mn[5]! rn[4]! false
  addNorthSouthEdge c .south mn[3]! mn[6]! rn[5]! false
  let _ ← assignIds g (withPorts := false)
  return g

def allCrossingsCounterTests : Suite := suite "layered.p3counting.all_crossings_counter" do
  let c := acCfg
  let r ← runL do
    let g ← acCrossForm
    countAll g (← nodeArray g)
  checkEq "all_crossings_count_cross_form" r 1
  let r ← runL do
    let g ← newGraph c
    countAll g (← nodeArray g)
  checkEq "all_crossings_count_empty_graph" r 0
  let r ← runL do
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let tl ← addNode c g l; let bl ← addNode c g l
    let tr ← addNode c g r; let br ← addNode c g r
    let tltp ← addPort c tl .east; let tlbp ← addPort c tl .east
    let brbp ← addPort c br .west; let brtp ← addPort c br .west
    connect tltp brtp; connect tlbp brbp
    let bltp ← addPort c bl .east; let blbp ← addPort c bl .east
    let trbp ← addPort c tr .west; let trtp ← addPort c tr .west
    connect bltp trtp; connect blbp trbp
    let _ ← assignIds g (withPorts := false)
    countAll g (← nodeArray g)
  checkEq "all_crossings_count_multiple_edges_between_same_nodes" r 4
  let r ← runL do
    let g ← acCrossForm
    let order ← nodeArray g
    let first ← countAll g order
    let switchedOrder := order.modify 1 (·.swapIfInBounds 0 1)
    let second ← countAll g switchedOrder
    return (first, second)
  checkEq "all_crossings_switch_and_count_twice" r (1, 0)
  for name in #["all_crossings_count_in_layer_crossing", "all_crossings_count_in_layer_crossing_and_switch"] do
    let r ← runL do
      let g ← newGraph c
      let l ← makeLayer g; let m ← makeLayer g; let r ← makeLayer g
      let leftNode ← addNode c g l; let mn ← addNodes c g m 3; let rightNode ← addNode c g r
      let mtr ← addPort c mn[1]! .east; let rfm ← addPort c rightNode .west
      connect mtr rfm
      let ltm ← addPort c leftNode .east; let mfl ← addPort c mn[1]! .west
      connect ltm mfl
      addInLayerEdge c mn[0]! mn[2]! .west
      let _ ← assignIds g (withPorts := false)
      countAll g (← nodeArray g)
    checkEq name r 1
  let r ← runL do
    let g ← newGraph c
    let l ← makeLayer g
    let nodes ← addNodes c g l 3
    setFixedOrderConstraint c nodes[1]!
    addInLayerEdge c nodes[0]! nodes[1]! .west
    addInLayerEdge c nodes[1]! nodes[2]! .west
    let _ ← assignIds g (withPorts := false)
    countAll g (← nodeArray g)
  checkEq "all_crossings_in_layer_crossings_on_far_left" r 1
  let r ← runL do
    let g ← newGraph c
    let l ← makeLayer g
    let nodes ← addNodes c g l 4
    addInLayerEdge c nodes[0]! nodes[1]! .east
    addInLayerEdge c nodes[2]! nodes[3]! .east
    let _ ← assignIds g (withPorts := false)
    countAll g (← nodeArray g)
  checkEq "all_crossings_too_many_in_layer_crossings_with_the_old_method" r 0
  let nsCase (side : PortSide) (longEdge : Bool) : IO Int := runL do
    let g ← acGraphWithNorthSouthCrossing side longEdge
    countAll g (← nodeArray g)
  checkEq "all_crossings_count_north_south_crossing" (← nsCase .north false) 0
  checkEq "all_crossings_count_northern_north_south_crossing" (← nsCase .south false) 0
  checkEq "all_crossings_north_south_dummy_edge_crossing" (← nsCase .north true) 2
  checkEq "all_crossings_one_node_is_long_edge_dummy" (← nsCase .north true) 2
  checkEq "all_crossings_one_node_is_long_edge_dummy_northern" (← nsCase .south true) 0
  let r ← runL do
    let g ← acGraphMultipleNorthSouthAndLongEdgeDummies
    countAll g (← nodeArray g)
  checkEq "all_crossings_multiple_north_south_and_long_edge_dummies_on_both_sides" r 4
  -- the initialisation numbers the ports in traversal order
  let r ← runL do
    let g ← acCrossForm
    let order ← nodeArray g
    let _ ← countAll g order
    let a ← get
    return order.flatten.flatMap fun n => (a.node n).ports.map fun p => (a.port p).id
  checkEq "init assigns port ids in traversal order" r #[0, 1, 2, 3]

/-! ## `north_south_edge_all_crossings_counter_test.rs` -/

/-- Helper variant of the north/south tests (`new_graph` options, layout units, `FIXED_SIDE`). -/
def nsCfg : Cfg := { options := true, selfUnit := true, fixSide := true, graphProps := true, full := true }

/-- `count_crossings_in_layer(graph, layer_index)`. -/
def countNorthSouthInLayer (g : LGraphId) (layerIndex : Nat) : LayeredM Int := do
  let numPorts ← assignIds g
  let layerNodes ← do
    let l := (← getGraph g).layers[layerIndex]!
    pure (← getLayer l).nodes
  let counter ← CrossingsCounter.ofPositions (Array.replicate numPorts 0)
  counter.countNorthSouthPortCrossingsInLayer layerNodes

/-- Graph with `n` left and `m` right nodes (two layers). -/
def nsTwoLayerGraph (n m : Nat) : LayeredM (LGraphId × Array LNodeId × Array LNodeId) := do
  let c := nsCfg
  let g ← newGraph c
  let (l, r) ← twoLayers g
  let ln ← addNodes c g l n
  let rn ← addNodes c g r m
  return (g, ln, rn)

/-- Graph with `n` left, `k` middle and `m` right nodes (three layers). -/
def nsThreeLayerGraph (n k m : Nat) : LayeredM (LGraphId × Array LNodeId × Array LNodeId × Array LNodeId) := do
  let c := nsCfg
  let g ← newGraph c
  let l ← makeLayer g; let mid ← makeLayer g; let r ← makeLayer g
  let ln ← addNodes c g l n
  let mn ← addNodes c g mid k
  let rn ← addNodes c g r m
  return (g, ln, mn, rn)

def nsGraphNorthSouthUpwardCrossing : LayeredM LGraphId := do
  let (g, ln, rn) ← nsTwoLayerGraph 3 2
  addNorthSouthEdge nsCfg .north ln[2]! ln[1]! rn[1]! false
  addNorthSouthEdge nsCfg .north ln[2]! ln[0]! rn[0]! false
  setFixedOrderConstraint nsCfg ln[2]!
  return g

def nsGraphNorthSouthUpwardMultipleCrossing : LayeredM LGraphId := do
  let (g, ln, rn) ← nsTwoLayerGraph 4 3
  addNorthSouthEdge nsCfg .north ln[3]! ln[2]! rn[2]! false
  addNorthSouthEdge nsCfg .north ln[3]! ln[1]! rn[1]! false
  addNorthSouthEdge nsCfg .north ln[3]! ln[0]! rn[0]! false
  setFixedOrderConstraint nsCfg ln[3]!
  return g

def nsGraphNorthSouthDownwardCrossing : LayeredM LGraphId := do
  let (g, ln, rn) ← nsTwoLayerGraph 3 2
  addNorthSouthEdge nsCfg .south ln[0]! ln[2]! rn[1]! false
  addNorthSouthEdge nsCfg .south ln[0]! ln[1]! rn[0]! false
  setFixedOrderConstraint nsCfg ln[0]!
  return g

def nsGraphNorthSouthDownwardMultipleCrossing : LayeredM LGraphId := do
  let (g, ln, rn) ← nsTwoLayerGraph 4 3
  addNorthSouthEdge nsCfg .south ln[0]! ln[3]! rn[2]! false
  addNorthSouthEdge nsCfg .south ln[0]! ln[2]! rn[1]! false
  addNorthSouthEdge nsCfg .south ln[0]! ln[1]! rn[0]! false
  setFixedOrderConstraint nsCfg ln[0]!
  return g

def nsGraphSouthernTwoWesternEdges : LayeredM LGraphId := do
  let (g, ln, mn) ← nsTwoLayerGraph 2 3
  setFixedOrderConstraint nsCfg mn[0]!
  addNorthSouthEdge nsCfg .south mn[0]! mn[1]! ln[0]! true
  addNorthSouthEdge nsCfg .south mn[0]! mn[2]! ln[1]! true
  return g

def nsGraphSouthernThreeWesternEdges : LayeredM LGraphId := do
  let (g, ln, mn) ← nsTwoLayerGraph 3 4
  setFixedOrderConstraint nsCfg mn[0]!
  addNorthSouthEdge nsCfg .south mn[0]! mn[1]! ln[0]! true
  addNorthSouthEdge nsCfg .south mn[0]! mn[2]! ln[1]! true
  addNorthSouthEdge nsCfg .south mn[0]! mn[3]! ln[2]! true
  return g

def nsGraphSouthernEdgesFromEastAndWestNoCrossings : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 1
  setFixedOrderConstraint nsCfg mn[0]!
  addNorthSouthEdge nsCfg .south mn[0]! mn[1]! rn[0]! false
  addNorthSouthEdge nsCfg .south mn[0]! mn[2]! ln[0]! true
  return g

def nsGraphSouthernEdgesBothToEast : LayeredM LGraphId := do
  let (g, mn, rn) ← nsTwoLayerGraph 3 2
  setFixedOrderConstraint nsCfg mn[0]!
  addNorthSouthEdge nsCfg .south mn[0]! mn[1]! rn[0]! false
  addNorthSouthEdge nsCfg .south mn[0]! mn[2]! rn[1]! false
  return g

def nsGraphEdgesFromEastAndWestAndCross : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 1
  setFixedOrderConstraint nsCfg mn[0]!
  addNorthSouthEdge nsCfg .south mn[0]! mn[1]! ln[0]! true
  addNorthSouthEdge nsCfg .south mn[0]! mn[2]! rn[0]! false
  return g

def nsGraphNorthernWesternEdges : LayeredM LGraphId := do
  let (g, ln, mn) ← nsTwoLayerGraph 2 3
  setFixedOrderConstraint nsCfg mn[2]!
  addNorthSouthEdge nsCfg .north mn[2]! mn[1]! ln[1]! true
  addNorthSouthEdge nsCfg .north mn[2]! mn[0]! ln[0]! true
  return g

def nsGraphNorthernEasternPortToWestWesternPortToEast : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 1
  setFixedOrderConstraint nsCfg mn[2]!
  addNorthSouthEdge nsCfg .north mn[2]! mn[1]! rn[0]! false
  addNorthSouthEdge nsCfg .north mn[2]! mn[0]! ln[0]! true
  return g

def nsGraphAllSidesMultipleCrossings : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 7 5
  setFixedOrderConstraint nsCfg mn[3]!
  addNorthSouthEdge nsCfg .north mn[3]! mn[1]! rn[1]! false
  addNorthSouthEdge nsCfg .north mn[3]! mn[2]! ln[0]! true
  addNorthSouthEdge nsCfg .north mn[3]! mn[0]! rn[0]! false
  addNorthSouthEdge nsCfg .south mn[3]! mn[6]! rn[4]! false
  addNorthSouthEdge nsCfg .south mn[3]! mn[4]! rn[2]! false
  addNorthSouthEdge nsCfg .south mn[3]! mn[5]! rn[3]! false
  return g

def nsGraphSouthernDummyEdgeCrossing : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 2
  eastWestEdgeFromTo nsCfg ln[0]! mn[1]!
  eastWestEdgeFromTo nsCfg mn[1]! rn[0]!
  setAsLongEdgeDummy mn[1]!
  addNorthSouthEdge nsCfg .south mn[0]! mn[2]! rn[1]! true
  return g

def nsGraphSouthernDummyEdgeTwoCrossing : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 4 3
  eastWestEdgeFromTo nsCfg ln[0]! mn[1]!
  eastWestEdgeFromTo nsCfg mn[1]! rn[0]!
  setAsLongEdgeDummy mn[1]!
  addNorthSouthEdge nsCfg .south mn[0]! mn[2]! rn[1]! true
  addNorthSouthEdge nsCfg .south mn[0]! mn[3]! rn[2]! true
  return g

def nsGraphSouthernTwoDummyEdgeAndNorthSouthCrossing : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 2 5 4
  eastWestEdgeFromTo nsCfg ln[0]! mn[1]!
  eastWestEdgeFromTo nsCfg mn[1]! rn[0]!
  setAsLongEdgeDummy mn[1]!
  eastWestEdgeFromTo nsCfg ln[1]! mn[3]!
  eastWestEdgeFromTo nsCfg mn[3]! rn[2]!
  setAsLongEdgeDummy mn[3]!
  setFixedOrderConstraint nsCfg mn[0]!
  addNorthSouthEdge nsCfg .south mn[0]! mn[4]! rn[3]! true
  addNorthSouthEdge nsCfg .south mn[0]! mn[2]! rn[1]! true
  return g

def nsGraphMultipleNorthSouthAndLongEdgeDummiesOnBothSides : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 2 7 6
  eastWestEdgeFromTo nsCfg ln[0]! mn[2]!
  eastWestEdgeFromTo nsCfg mn[2]! rn[2]!
  eastWestEdgeFromTo nsCfg ln[1]! mn[4]!
  eastWestEdgeFromTo nsCfg mn[4]! rn[4]!
  setAsLongEdgeDummy mn[2]!
  setAsLongEdgeDummy mn[4]!
  addNorthSouthEdge nsCfg .north mn[3]! mn[0]! rn[0]! false
  addNorthSouthEdge nsCfg .north mn[3]! mn[1]! rn[1]! false
  addNorthSouthEdge nsCfg .south mn[3]! mn[5]! rn[4]! false
  addNorthSouthEdge nsCfg .south mn[3]! mn[6]! rn[5]! false
  return g

def nsGraphLongEdgeDummyAndNormalNodeWithUnusedPortsOnSouthernSide : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 2 1
  setFixedOrderConstraint nsCfg mn[0]!
  eastWestEdgeFromTo nsCfg ln[0]! mn[1]!
  eastWestEdgeFromTo nsCfg mn[1]! rn[0]!
  setAsLongEdgeDummy mn[1]!
  let _ ← addPort nsCfg mn[0]! .south
  let _ ← addPort nsCfg mn[0]! .south
  return g

def nsGraphCrossFormed : LayeredM LGraphId := do
  let (g, ln, rn) ← nsTwoLayerGraph 2 2
  eastWestEdgeFromTo nsCfg ln[0]! rn[1]!
  eastWestEdgeFromTo nsCfg ln[1]! rn[0]!
  return g

def northSouthAllCrossingsTests : Suite := suite "layered.p3counting.north_south_edge_all_crossings_counter" do
  let case (name : String) (graph : LayeredM LGraphId) (layerIndex : Nat) (expected : Int) : TestM Unit := do
    let r ← runL do countNorthSouthInLayer (← graph) layerIndex
    checkEq name r expected
  case "northern_north_south_node_single_crossing" nsGraphNorthSouthUpwardCrossing 0 1
  case "northern_north_south_node_multiple_crossings" nsGraphNorthSouthUpwardMultipleCrossing 0 3
  case "southern_two_edge_east_crossing" nsGraphNorthSouthDownwardCrossing 0 1
  case "southern_north_south_multiple_node_crossing" nsGraphNorthSouthDownwardMultipleCrossing 0 3
  case "southern_two_western_edges" nsGraphSouthernTwoWesternEdges 1 1
  case "southern_three_western_edges" nsGraphSouthernThreeWesternEdges 1 3
  case "north_south_edges_come_from_both_sides_dont_cross" nsGraphSouthernEdgesFromEastAndWestNoCrossings 1 0
  case "southern_north_south_edges_both_to_east_dont_cross" nsGraphSouthernEdgesBothToEast 0 0
  case "north_south_edges_come_from_both_sides_do_cross" nsGraphEdgesFromEastAndWestAndCross 1 1
  case "northern_both_edges_western" nsGraphNorthernWesternEdges 0 0
  case "northern_eastern_port_to_west_western_port_to_east" nsGraphNorthernEasternPortToWestWesternPortToEast 1 1
  case "all_sides_multiple_crossings" nsGraphAllSidesMultipleCrossings 1 4
  case "one_edge_dummy_is_crossed_by_one_southern_north_south_port_edge" nsGraphSouthernDummyEdgeCrossing 1 1
  case "one_edge_dummy_is_crossed_by_two_southern_north_south_port_edges" nsGraphSouthernDummyEdgeTwoCrossing 1 2
  case "southern_two_dummy_edge_and_two_north_south_should_cross_four_times" nsGraphSouthernTwoDummyEdgeAndNorthSouthCrossing 1 4
  case "normal_nodes_north_south_edges_have_crossings_to_long_edge_dummy_on_both_sides"
    nsGraphMultipleNorthSouthAndLongEdgeDummiesOnBothSides 1 4
  case "ignores_unconnected_ports_for_normal_node_and_long_edge_dummies"
    nsGraphLongEdgeDummyAndNormalNodeWithUnusedPortsOnSouthernSide 1 0
  case "no_north_south_node" nsGraphCrossFormed 0 0
  case "more_than_one_edge_into_ns_node_counts_these_too" (do
    let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 2
    setFixedOrderConstraint nsCfg mn[2]!
    addNorthSouthEdge nsCfg .north mn[2]! mn[1]! rn[0]! false
    addNorthSouthEdge nsCfg .north mn[2]! mn[0]! ln[0]! true
    let middleNodePort := (← getNode mn[1]!).ports[0]!
    let rightNodePort ← addPort nsCfg rn[1]! .west
    connect middleNodePort rightNodePort
    return g) 1 2
  case "the_one_that_failed_with_the_old_counting" (do
    let (g, ln, mn) ← nsTwoLayerGraph 4 5
    setFixedOrderConstraint nsCfg mn[4]!
    for k in [0:4] do
      let idx := 3 - k
      addNorthSouthEdge nsCfg .north mn[4]! mn[idx]! ln[idx]! false
    return g) 1 0

/-! ## `in_layer_edge_two_node_crossing_counter_test.rs` -/

/-- Helper variant of the in-layer and between-layer tests. -/
def ilCfg : Cfg := { options := true, graphProps := true }

/-- `InLayerCrossingHarness`: west/east in-layer counters over one layer's order. -/
structure InLayerHarness where
  nodeOrder : IO.Ref (Array LNodeId)
  leftCounter : CrossingsCounter
  rightCounter : CrossingsCounter

namespace InLayerHarness

/-- `InLayerCrossingHarness::new(graph, layer_index)`. -/
def new (g : LGraphId) (layerIndex : Nat) : LayeredM InLayerHarness := do
  let totalPorts ← assignIds g
  let order := (← nodeArray g)[layerIndex]!
  for h : idx in [0:order.size] do
    modifyNode order[idx] fun x => { x with id := idx }
  let leftCounter ← CrossingsCounter.ofPositions (Array.replicate totalPorts 0)
  let rightCounter ← CrossingsCounter.ofPositions (Array.replicate totalPorts 0)
  let _ ← leftCounter.initPortPositionsForInLayerCrossings order .west
  let _ ← rightCounter.initPortPositionsForInLayerCrossings order .east
  return { nodeOrder := ← IO.mkRef order, leftCounter, rightCounter }

/-- `count_crossings(upper_index, lower_index)`: `(upper_lower, lower_upper)`. -/
def countCrossings (h : InLayerHarness) (upperIndex lowerIndex : Nat) : LayeredM (Int × Int) := do
  let order ← h.nodeOrder.get
  let upper := order[upperIndex]!
  let lower := order[lowerIndex]!
  let left ← h.leftCounter.countInLayerCrossingsBetweenNodesInBothOrders upper lower .west
  let right ← h.rightCounter.countInLayerCrossingsBetweenNodesInBothOrders upper lower .east
  return (left.1 + right.1, left.2 + right.2)

/-- `switch_order(index_one, index_two)`. -/
def switchOrder (h : InLayerHarness) (indexOne indexTwo : Nat) : LayeredM Unit := do
  let order ← h.nodeOrder.get
  h.leftCounter.switchNodes order[indexOne]! order[indexTwo]! .west
  h.rightCounter.switchNodes order[indexOne]! order[indexTwo]! .east
  h.nodeOrder.set (order.swapIfInBounds indexOne indexTwo)

end InLayerHarness

def ilGraphCrossFormed : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let (l, r) ← twoLayers g
  let ln ← addNodes c g l 2; let rn ← addNodes c g r 2
  eastWestEdgeFromTo c ln[0]! rn[1]!
  eastWestEdgeFromTo c ln[1]! rn[0]!
  return g

def ilGraphInLayerEdges : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let l ← makeLayer g; let m ← makeLayer g; let r ← makeLayer g
  let leftNode ← addNode c g l; let mn ← addNodes c g m 3; let rightNode ← addNode c g r
  eastWestEdgeFromTo c mn[1]! rightNode
  eastWestEdgeFromTo c leftNode mn[1]!
  addInLayerEdge c mn[0]! mn[2]! .west
  return g

def ilGraphInLayerEdgesCrossingsWhenSwitched : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let (l, r) ← twoLayers g
  let leftNode ← addNode c g l; let rn ← addNodes c g r 3
  addInLayerEdge c rn[0]! rn[1]! .west
  eastWestEdgeFromTo c leftNode rn[2]!
  return g

def ilGraphCrossingsToBetweenLayerEdgeWithFixedPortOrder : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let layers ← makeLayers g 2
  let leftNode ← addNode c g layers[0]!; let rn ← addNodes c g layers[1]! 2
  setFixedOrderConstraint c rn[0]!
  eastWestEdgeFromTo c leftNode rn[0]!
  addInLayerEdge c rn[0]! rn[1]! .west
  eastWestEdgeFromTo c leftNode rn[0]!
  eastWestEdgeFromTo c leftNode rn[0]!
  return g

def ilGraphFixedPortOrderAndNormalEdgeCrossings : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let layers ← makeLayers g 2
  let leftNode ← addNode c g layers[0]!; let rn ← addNodes c g layers[1]! 3
  setFixedOrderConstraint c rn[0]!
  eastWestEdgeFromTo c leftNode rn[0]!
  addInLayerEdge c rn[0]! rn[2]! .west
  eastWestEdgeFromTo c leftNode rn[1]!
  return g

/-- `graph_cross_with_many_self_loops()` (also used by the between-layer tests). -/
def graphCrossWithManySelfLoops (c : Cfg) : LayeredM LGraphId := do
  let g ← newGraph c
  let (l, r) ← twoLayers g
  let ln ← addNodes c g l 2; let rn ← addNodes c g r 2
  let tlp ← addPort c ln[0]! .east
  let blp ← addPort c ln[1]! .east
  for layer in (← getGraph g).layers do
    for node in (← getLayer layer).nodes do
      selfLoopOn c node .east; selfLoopOn c node .east; selfLoopOn c node .east
      selfLoopOn c node .west; selfLoopOn c node .west; selfLoopOn c node .west
  let trp ← addPort c rn[0]! .west
  let brp ← addPort c rn[1]! .west
  connect tlp brp
  connect blp trp
  return g

def ilGraphInLayerCrossingsOnBothSides : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let layers ← makeLayers g 3
  let leftNode ← addNode c g layers[0]!; let mn ← addNodes c g layers[1]! 3; let rightNode ← addNode c g layers[2]!
  addInLayerEdge c mn[0]! mn[2]! .east
  addInLayerEdge c mn[0]! mn[2]! .west
  eastWestEdgeFromTo c mn[1]! rightNode
  eastWestEdgeFromTo c leftNode mn[1]!
  return g

def ilGraphFixedPortOrderInLayerEdgesDontCrossEachOther : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let l ← makeLayer g
  let nodes ← addNodes c g l 2
  setFixedOrderConstraint c nodes[0]!
  setFixedOrderConstraint c nodes[1]!
  let upu ← addPort c nodes[0]! .east; let lpu ← addPort c nodes[0]! .east
  let upl ← addPort c nodes[1]! .east; let lpl ← addPort c nodes[1]! .east
  connect upu lpl
  connect lpu upl
  return g

def ilGraphFixedPortOrderInLayerEdgesWithCrossings : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let l ← makeLayer g
  let nodes ← addNodes c g l 2
  setFixedOrderConstraint c nodes[0]!
  setFixedOrderConstraint c nodes[1]!
  addInLayerEdge c nodes[0]! nodes[1]! .east
  addInLayerEdge c nodes[0]! nodes[1]! .east
  return g

def ilGraphOneNode : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let l ← makeLayer g
  let _ ← addNode c g l
  return g

def ilGraphMoreComplexInLayer : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let layers ← makeLayers g 3
  let ln ← addNodes c g layers[0]! 4; let mn ← addNodes c g layers[1]! 3; let rightNode ← addNode c g layers[2]!
  setFixedOrderConstraint c mn[0]!
  setFixedOrderConstraint c mn[1]!
  eastWestEdgeFromTo c ln[1]! mn[0]!
  eastWestEdgeFromTo c ln[3]! mn[1]!
  eastWestEdgeFromTo c ln[2]! mn[1]!
  addInLayerEdge c mn[0]! mn[1]! .west
  eastWestEdgeFromTo c ln[0]! mn[0]!
  addInLayerEdge c mn[0]! mn[2]! .west
  addInLayerEdge c mn[0]! mn[1]! .east
  eastWestEdgeFromTo c mn[0]! rightNode
  return g

def ilGraphFixedPortOrderInLayerAndInBetweenLayerCrossing : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let layers ← makeLayers g 2
  let leftNode ← addNode c g layers[0]!; let rn ← addNodes c g layers[1]! 3
  setFixedOrderConstraint c rn[1]!
  eastWestEdgeFromTo c leftNode rn[1]!
  addInLayerEdge c rn[0]! rn[1]! .west
  addInLayerEdge c rn[1]! rn[2]! .west
  return g

def ilGraphOneLayerWithInLayerCrossings : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let l ← makeLayer g
  let nodes ← addNodes c g l 4
  addInLayerEdge c nodes[0]! nodes[2]! .west
  addInLayerEdge c nodes[1]! nodes[3]! .west
  return g

def ilGraphMultipleEdgesIntoSinglePort : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let layerTwo ← makeLayer g
  let leftNode ← addNode c g layerTwo
  let layerOne ← makeLayer g
  let rn ← addNodes c g layerOne 4
  addInLayerEdge c rn[1]! rn[3]! .west
  let leftPort ← addPort c leftNode .east
  let rightTopPort ← addPort c rn[0]! .west
  let rightMiddlePort ← addPort c rn[2]! .west
  connect leftPort rightMiddlePort
  connect rightTopPort rightMiddlePort
  return g

def ilGraphOneLayerNoCrossings : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let l ← makeLayer g
  let nodes ← addNodes c g l 4
  addInLayerEdge c nodes[0]! nodes[3]! .west
  addInLayerEdge c nodes[1]! nodes[2]! .west
  return g

def ilGraphFixedPortOrderInLayerCrossing : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let l ← makeLayer g
  let nodes ← addNodes c g l 3
  setFixedOrderConstraint c nodes[1]!
  addInLayerEdge c nodes[0]! nodes[1]! .west
  addInLayerEdge c nodes[1]! nodes[2]! .west
  return g

def ilGraphFixedPortOrderTwoInLayerEdgesCrossEachOther : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let l ← makeLayer g
  let nodes ← addNodes c g l 3
  setFixedOrderConstraint c nodes[0]!
  addInLayerEdge c nodes[0]! nodes[2]! .west
  addInLayerEdge c nodes[0]! nodes[1]! .west
  return g

def ilGraphMultipleBetweenLayerEdgesIntoNodeWithoutFixedPortOrder : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let l ← makeLayer g
  let ln ← addNodes c g l 2
  let r ← makeLayer g
  let rn ← addNodes c g r 3
  addInLayerEdge c rn[0]! rn[2]! .west
  eastWestEdgeFromTo c ln[0]! rn[1]!
  eastWestEdgeFromTo c ln[0]! rn[1]!
  return g

/-- A harness step: `count u l` or `switch i j`. -/
inductive HStep where
  | count (u l : Nat)
  | switch (i j : Nat)

/-- Runs harness steps on a graph's layer and returns the results of the `count` steps. -/
def runHarness (graph : LayeredM LGraphId) (layerIndex : Nat) (steps : Array HStep) : IO (Array (Int × Int)) := runL do
  let h ← InLayerHarness.new (← graph) layerIndex
  let mut results := #[]
  for s in steps do
    match s with
    | .count u l => results := results.push (← h.countCrossings u l)
    | .switch i j => h.switchOrder i j
  return results

def inLayerTwoNodeTests : Suite := suite "layered.p3counting.in_layer_edge_two_node_crossing_counter" do
  let case (name : String) (graph : LayeredM LGraphId) (layerIndex : Nat) (steps : Array HStep)
      (expected : Array (Int × Int)) : TestM Unit := do
    checkEq name (← runHarness graph layerIndex steps) expected
  case "ignores_in_between_layer_edges" ilGraphCrossFormed 1 #[.count 0 1] #[(0, 0)]
  case "count_in_layer_edge_with_normal_edge_crossing" ilGraphInLayerEdges 1 #[.count 0 1] #[(1, 0)]
  case "crossings_when_switched" ilGraphInLayerEdgesCrossingsWhenSwitched 1 #[.count 1 2] #[(0, 1)]
  case "in_layer_edge_on_lower_node" ilGraphInLayerEdges 1 #[.count 0 1] #[(1, 0)]
  case "switch_node_order" ilGraphInLayerEdges 1 #[.switch 1 2, .count 0 1] #[(0, 0)]
  case "fixed_port_order_crossing_to_in_between_layer_edge" ilGraphCrossingsToBetweenLayerEdgeWithFixedPortOrder 1
    #[.count 0 1, .switch 0 1, .count 0 1] #[(1, 2), (2, 1)]
  case "fixed_port_order_crossings_and_normal_edge_crossings" ilGraphFixedPortOrderAndNormalEdgeCrossings 1
    #[.count 0 1, .switch 0 1, .count 0 1] #[(2, 1), (1, 2)]
  case "ignores_self_loops" (graphCrossWithManySelfLoops ilCfg) 1 #[.count 0 1] #[(0, 0)]
  case "crossings_on_both_sides" ilGraphInLayerCrossingsOnBothSides 1 #[.count 0 1] #[(2, 0)]
  case "fixed_port_order_in_layer_no_crossings" ilGraphFixedPortOrderInLayerEdgesDontCrossEachOther 0 #[.count 0 1] #[(0, 0)]
  case "fixed_port_order_in_layer_with_always_remaining_crossings_not_counted"
    ilGraphFixedPortOrderInLayerEdgesWithCrossings 0 #[.count 0 1] #[(1, 1)]
  case "one_node" ilGraphOneNode 0 #[.count 0 0] #[(0, 0)]
  case "more_complex" ilGraphMoreComplexInLayer 1 #[.count 0 1] #[(6, 6)]
  case "downward_in_layer_edges_on_lower_node" ilGraphFixedPortOrderInLayerAndInBetweenLayerCrossing 1 #[.count 0 1] #[(2, 2)]
  case "one_layer_in_layer_crossing_should_disappear_after_any_switch" ilGraphOneLayerWithInLayerCrossings 0
    #[.count 0 1, .count 1 2, .count 2 3, .switch 0 1, .count 0 1, .switch 0 1, .switch 1 2, .count 1 2,
      .switch 1 2, .switch 2 3, .count 2 3]
    #[(1, 0), (1, 0), (1, 0), (0, 1), (0, 1), (0, 1)]
  case "more_than_one_edge_into_a_port" ilGraphMultipleEdgesIntoSinglePort 1 #[.count 1 2] #[(2, 0)]
  case "in_between_layer_edges_into_node_with_no_fixed_port_order_cause_crossings"
    ilGraphMultipleBetweenLayerEdgesIntoNodeWithoutFixedPortOrder 1 #[.count 0 1, .count 1 2] #[(2, 0), (2, 0)]
  case "in_layer_edges_pass_each_other" ilGraphOneLayerNoCrossings 0 #[.count 0 1, .count 1 2, .count 2 3]
    #[(0, 1), (0, 0), (0, 1)]
  case "fixed_port_order_crossing_to_in_layer_edge" ilGraphFixedPortOrderInLayerCrossing 0 #[.count 1 2] #[(1, 0)]
  case "fixed_port_order_two_in_layer_edges_cross_each_other" ilGraphFixedPortOrderTwoInLayerEdgesCrossEachOther 0
    #[.count 0 1] #[(1, 0)]
  case "multiple_edges_into_one_port_should_not_cause_crossing" (do
    let c := ilCfg
    let g ← newGraph c
    let l ← makeLayer g
    let nodes ← addNodes c g l 3
    let p1 ← addPort c nodes[0]! .east
    let p2 ← addPort c nodes[1]! .east
    let p3 ← addPort c nodes[2]! .east
    connect p1 p3
    connect p2 p3
    return g) 0 #[.count 0 1] #[(0, 0)]

/-! ## `between_layer_edge_two_node_crossings_counter_test.rs` -/

/-- `setup_counter(graph, free_layer_index, upper_index, lower_index)` followed by counting steps
(`'e'` eastern, `'w'` western, `'b'` both sides); returns `(upper_lower, lower_upper)` per step. -/
def runBetweenLayer (graph : LayeredM LGraphId) (freeLayerIndex upperIndex lowerIndex : Nat) (steps : Array Char) :
    IO (Array (Int × Int)) := runL do
  let g ← graph
  let order ← nodeArray g
  let layerNodes := order[freeLayerIndex]!
  let upper := layerNodes[upperIndex]!
  let lower := layerNodes[lowerIndex]!
  let counter ← BetweenLayerEdgeTwoNodeCrossingsCounter.new order freeLayerIndex
  let mut results := #[]
  for s in steps do
    match s with
    | 'e' => counter.countEasternEdgeCrossings upper lower
    | 'w' => counter.countWesternEdgeCrossings upper lower
    | _ => counter.countBothSideCrossings upper lower
    results := results.push (← counter.upperLowerCrossings, ← counter.lowerUpperCrossings)
  return results

def blGraphTwoNodesNoConnection : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let l ← makeLayer g
  let _ ← addNode c g l
  let _ ← addNode c g l
  return g

def blGraphMultipleEdgesBetweenSameNodes : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let (l, r) ← twoLayers g
  let ln ← addNodes c g l 2; let rn ← addNodes c g r 2
  eastWestEdgeFromTo c ln[0]! rn[1]!
  eastWestEdgeFromTo c ln[0]! rn[1]!
  eastWestEdgeFromTo c ln[1]! rn[0]!
  eastWestEdgeFromTo c ln[1]! rn[0]!
  return g

def blGraphCrossWithExtraEdgeInBetween : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let (l, r) ← twoLayers g
  let ln ← addNodes c g l 3; let rn ← addNodes c g r 3
  eastWestEdgeFromTo c ln[0]! rn[2]!
  eastWestEdgeFromTo c ln[1]! rn[1]!
  eastWestEdgeFromTo c ln[2]! rn[0]!
  return g

def blGraphMoreComplexThreeLayer : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let l ← makeLayer g; let m ← makeLayer g; let r ← makeLayer g
  let ln ← addNodes c g l 3; let mn ← addNodes c g m 2; let rn ← addNodes c g r 3
  let leftMiddlePort ← addPort c ln[1]! .east
  let middleLowerEast ← addPort c mn[1]! .east
  let middleUpperEast ← addPort c mn[0]! .east
  let rightUpper ← addPort c rn[0]! .west
  let rightMiddle ← addPort c rn[1]! .west
  connect middleUpperEast rightUpper
  connect middleUpperEast rightMiddle
  connect middleUpperEast rightMiddle
  eastWestEdgeFromPort c middleLowerEast rn[2]!
  eastWestEdgeFromPort c leftMiddlePort mn[0]!
  eastWestEdgeFromNode c mn[1]! rightUpper
  eastWestEdgeFromPort c leftMiddlePort mn[1]!
  eastWestEdgeFromTo c ln[2]! mn[0]!
  eastWestEdgeFromTo c ln[0]! mn[0]!
  return g

def blGraphFixedPortOrder : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let (l, r) ← twoLayers g
  let leftNode ← addNode c g l
  setFixedOrderConstraint c leftNode
  let rn ← addNodes c g r 2
  eastWestEdgeFromTo c leftNode rn[1]!
  eastWestEdgeFromTo c leftNode rn[0]!
  return g

def blGraphTwoEdgesIntoSamePort : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let (l, r) ← twoLayers g
  let ln ← addNodes c g l 2; let rn ← addNodes c g r 2
  eastWestEdgeFromTo c ln[0]! rn[1]!
  let bl1 ← addPort c ln[1]! .east; let bl2 ← addPort c ln[1]! .east
  let tr1 ← addPort c rn[0]! .west; let tr2 ← addPort c rn[0]! .west
  connect bl1 tr1
  connect bl2 tr2
  return g

def blGraphTwoEdgesIntoSamePortCrossesWhenSwitched : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let (l, r) ← twoLayers g
  let ln ← addNodes c g l 2; let rn ← addNodes c g r 2
  let trp ← addPort c rn[0]! .west
  let blp ← addPort c ln[1]! .east
  connect blp trp
  let tlp ← addPort c ln[0]! .east
  connect tlp trp
  eastWestEdgeFromTo c ln[1]! rn[1]!
  return g

def blGraphTwoEdgesIntoSamePortResolvesCrossingWhenSwitched : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let (l, r) ← twoLayers g
  let ln ← addNodes c g l 2; let rn ← addNodes c g r 2
  let tlp ← addPort c ln[0]! .east
  let blp ← addPort c ln[1]! .east
  let brp ← addPort c rn[1]! .west
  connect tlp brp
  connect blp brp
  eastWestEdgeFromTo c ln[1]! rn[0]!
  return g

def blGraphTwoEdgesIntoSamePortFromEastWithFixedPortOrder : LayeredM LGraphId := do
  let c := ilCfg
  let g ← newGraph c
  let (l, r) ← twoLayers g
  let ln ← addNodes c g l 2; let rn ← addNodes c g r 2
  setFixedOrderConstraint c ln[1]!
  setFixedOrderConstraint c rn[0]!
  let tlp ← addPort c ln[0]! .east
  let blp ← addPort c ln[1]! .east
  let trp ← addPort c rn[0]! .west
  let brp ← addPort c rn[1]! .west
  connect blp brp
  connect blp trp
  connect tlp trp
  return g

def betweenLayerTwoNodeTests : Suite := suite "layered.p3counting.between_layer_edge_two_node_crossings_counter" do
  let case (name : String) (graph : LayeredM LGraphId) (freeLayer upper lower : Nat) (steps : Array Char)
      (expected : Array (Int × Int)) : TestM Unit := do
    checkEq name (← runBetweenLayer graph freeLayer upper lower steps) expected
  case "two_node_no_edges" blGraphTwoNodesNoConnection 0 0 1 #['b', 'w', 'e'] #[(0, 0), (0, 0), (0, 0)]
  case "cross_formed" ilGraphCrossFormed 1 0 1 #['b', 'w', 'e'] #[(1, 0), (1, 0), (0, 0)]
  case "one_node" ilGraphOneNode 0 0 0 #['b', 'w', 'e'] #[(0, 0), (0, 0), (0, 0)]
  case "cross_formed_multiple_edges_between_same_nodes" blGraphMultipleEdgesBetweenSameNodes 1 0 1 #['b', 'w', 'e']
    #[(4, 0), (4, 0), (0, 0)]
  case "cross_with_extra_edge_in_between" blGraphCrossWithExtraEdgeInBetween 1 0 2 #['b', 'w', 'e'] #[(1, 0), (1, 0), (0, 0)]
  case "ignore_in_layer_edges" ilGraphInLayerEdges 1 0 2 #['b', 'w', 'e'] #[(0, 0), (0, 0), (0, 0)]
  case "ignore_self_loops" (graphCrossWithManySelfLoops ilCfg) 1 0 1 #['b', 'w', 'e'] #[(1, 0), (1, 0), (0, 0)]
  case "more_complex_three_layer_graph" blGraphMoreComplexThreeLayer 1 0 1 #['w', 'e', 'b'] #[(1, 1), (2, 3), (3, 4)]
  case "fixed_port_order" blGraphFixedPortOrder 1 0 1 #['e', 'w', 'b'] #[(0, 0), (1, 0), (1, 0)]
  case "switch_three_times" (do
    let c := ilCfg
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let ln ← addNodes c g l 2; let rn ← addNodes c g r 4
    let ltp ← addPort c ln[0]! .east
    let llp ← addPort c ln[1]! .east
    let rtp ← addPort c rn[0]! .west
    connect llp rtp
    eastWestEdgeFromPort c llp rn[2]!
    connect ltp rtp
    eastWestEdgeFromPort c ltp rn[1]!
    eastWestEdgeFromPort c ltp rn[3]!
    return g) 0 0 1 #['e', 'w', 'b'] #[(3, 2), (0, 0), (3, 2)]
  case "into_same_port" blGraphTwoEdgesIntoSamePort 1 0 1 #['e', 'w', 'b'] #[(0, 0), (2, 0), (2, 0)]
  case "into_same_port_causes_crossings_on_switch" blGraphTwoEdgesIntoSamePortCrossesWhenSwitched 0 0 1 #['e', 'w', 'b']
    #[(0, 1), (0, 0), (0, 1)]
  case "into_same_port_reduces_crossings_on_switch" blGraphTwoEdgesIntoSamePortResolvesCrossingWhenSwitched 0 0 1
    #['e', 'w', 'b'] #[(1, 0), (0, 0), (1, 0)]
  case "into_same_port_from_east_switch_with_fixed_port_order" blGraphTwoEdgesIntoSamePortFromEastWithFixedPortOrder 0 0 1
    #['e', 'w', 'b'] #[(0, 1), (0, 0), (0, 1)]
  case "multiple_edges_into_same_port_causes_no_crossings" (do
    let c := ilCfg
    let g ← newGraph c
    let (l, r) ← twoLayers g
    let topLeft ← addNode c g l
    let bottomLeft ← addNode c g l
    let bottomRight ← addNode c g r
    let brp ← addPort c bottomRight .west
    eastWestEdgeFromNode c topLeft brp
    eastWestEdgeFromNode c topLeft brp
    eastWestEdgeFromNode c bottomLeft brp
    return g) 0 0 1 #['e', 'e'] #[(0, 0), (0, 0)]

/-! ## `north_south_edge_neighbouring_node_crossings_counter_test.rs` -/

/-- `layer_nodes(graph, layer_index)`. -/
def layerNodes (g : LGraphId) (layerIndex : Nat) : LayeredM (Array LNodeId) := do
  return (← nodeArray g)[layerIndex]!

/-- `count_crossings(layer, upper_index, lower_index)`: a fresh counter over `layer`. -/
def countNeighbouring (layer : Array LNodeId) (upperIndex lowerIndex : Nat) : LayeredM (Int × Int) := do
  let counter ← NorthSouthEdgeNeighbouringNodeCrossingsCounter.new layer
  counter.countCrossings layer[upperIndex]! layer[lowerIndex]!
  return (← counter.upperLowerCrossings, ← counter.lowerUpperCrossings)

def nnGraphNorthernDummyEdgeCrossing : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 2
  eastWestEdgeFromTo nsCfg ln[0]! mn[1]!
  eastWestEdgeFromTo nsCfg mn[1]! rn[1]!
  setAsLongEdgeDummy mn[1]!
  addNorthSouthEdge nsCfg .north mn[2]! mn[0]! rn[0]! true
  return g

def nnGraphNorthernEdgesFromEastAndWestNoCrossings : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 1
  setFixedOrderConstraint nsCfg mn[2]!
  addNorthSouthEdge nsCfg .north mn[2]! mn[0]! ln[0]! true
  addNorthSouthEdge nsCfg .north mn[2]! mn[1]! rn[0]! false
  return g

def nnGraphNorthernEdgesFromEastAndWestNoCrossingsUpperEdgeEast : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 1
  setFixedOrderConstraint nsCfg mn[2]!
  addNorthSouthEdge nsCfg .north mn[2]! mn[1]! ln[0]! true
  addNorthSouthEdge nsCfg .north mn[2]! mn[0]! rn[0]! false
  return g

def nnGraphWhereLayoutUnitPreventsSwitch : LayeredM LGraphId := do
  let (g, ln, rn) ← nsTwoLayerGraph 4 2
  setFixedOrderConstraint nsCfg ln[0]!
  setFixedOrderConstraint nsCfg ln[3]!
  addNorthSouthEdge nsCfg .south ln[0]! ln[1]! rn[1]! false
  addNorthSouthEdge nsCfg .north ln[3]! ln[2]! rn[0]! false
  return g

def nnGraphSouthPortOnNormalNodeBelowLongEdgeDummy : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 2
  eastWestEdgeFromTo nsCfg ln[0]! mn[0]!
  eastWestEdgeFromTo nsCfg mn[0]! rn[0]!
  setNodeTypeLongEdge mn[0]!
  addNorthSouthEdge nsCfg .south mn[1]! mn[2]! rn[1]! false
  return g

def nnGraphNorthPortOnNormalNodeAboveLongEdgeDummy : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 2
  eastWestEdgeFromTo nsCfg ln[0]! mn[2]!
  eastWestEdgeFromTo nsCfg mn[2]! rn[1]!
  setNodeTypeLongEdge mn[2]!
  addNorthSouthEdge nsCfg .north mn[1]! mn[0]! rn[0]! false
  return g

def nnGraphSouthernWesternPortToEastAndEasternPortToWest : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 1
  setFixedOrderConstraint nsCfg mn[0]!
  addNorthSouthEdge nsCfg .south mn[0]! mn[2]! ln[0]! true
  addNorthSouthEdge nsCfg .south mn[0]! mn[1]! rn[0]! false
  return g

def nnGraphLongEdgeDummyAndNormalNodeWithUnusedPortsOnNorthernSide : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 2 1
  eastWestEdgeFromTo nsCfg ln[0]! mn[0]!
  eastWestEdgeFromTo nsCfg mn[0]! rn[0]!
  setNodeTypeLongEdge mn[0]!
  let _ ← addPort nsCfg mn[1]! .north
  let _ ← addPort nsCfg mn[1]! .north
  return g

/-- Counts on `layer_nodes(graph, layer)` for each `(upper, lower, swapBefore)` step; `swapBefore`
swaps the two positions in the local order first (Rust `layer.swap`). -/
def runNeighbouring (graph : LayeredM LGraphId) (layerIndex : Nat) (steps : Array (Nat × Nat × Bool)) :
    IO (Array (Int × Int)) := runL do
  let g ← graph
  let mut layer ← layerNodes g layerIndex
  let mut results := #[]
  for (u, l, swapBefore) in steps do
    if swapBefore then layer := layer.swapIfInBounds u l
    results := results.push (← countNeighbouring layer u l)
  return results

/-- Origin port helper of the multi-edge tests: `node.ports[index]`. -/
def portAt (n : LNodeId) (index : Nat) : LayeredM LPortId := do return (← getNode n).ports[index]!

/-- Sets the dummy port's `ORIGIN` to `originPort`. -/
def setPortOrigin (p originPort : LPortId) : LayeredM Unit :=
  modifyPort p fun x => { x with internal := { x.internal with origin := some (.lPort originPort) } }

def northSouthNeighbouringTests : Suite := suite "layered.p3counting.north_south_edge_neighbouring_node_crossings_counter" do
  let case (name : String) (graph : LayeredM LGraphId) (layerIndex : Nat) (steps : Array (Nat × Nat × Bool))
      (expected : Array (Int × Int)) : TestM Unit := do
    checkEq name (← runNeighbouring graph layerIndex steps) expected
  case "no_north_south_node" nsGraphCrossFormed 0 #[(0, 1, false)] #[(0, 0)]
  case "southern_north_south_node_crossing" nsGraphNorthSouthDownwardCrossing 0 #[(1, 2, false)] #[(1, 0)]
  case "northern_north_south_node_crossings" nsGraphNorthSouthUpwardCrossing 0 #[(0, 1, false)] #[(1, 0)]
  case "one_node_is_long_edge_dummy" nsGraphSouthernDummyEdgeCrossing 1 #[(1, 2, false), (1, 2, true)] #[(1, 0), (0, 1)]
  case "one_node_is_long_edge_dummy_northern" nnGraphNorthernDummyEdgeCrossing 1 #[(0, 1, false), (0, 1, true)]
    #[(1, 0), (0, 1)]
  case "with_normal_node" nsGraphNorthSouthDownwardCrossing 0 #[(0, 1, false)] #[(0, 0)]
  case "north_south_edges_come_from_both_sides_dont_cross (southern)" nsGraphSouthernEdgesFromEastAndWestNoCrossings 1
    #[(1, 2, false)] #[(0, 0)]
  case "north_south_edges_come_from_both_sides_dont_cross (northern)" nnGraphNorthernEdgesFromEastAndWestNoCrossings 1
    #[(0, 1, false)] #[(0, 0)]
  case "southern_north_south_edges_both_to_east" nsGraphSouthernEdgesBothToEast 0 #[(1, 2, false)] #[(0, 1)]
  case "crossings_with_north_south_ports_belonging_to_different_nodes_should_not_be_counted"
    nnGraphWhereLayoutUnitPreventsSwitch 0 #[(1, 2, false)] #[(0, 0)]
  case "north_south_edges_come_from_both_sides_do_cross" nsGraphEdgesFromEastAndWestAndCross 1 #[(1, 2, false)] #[(1, 1)]
  case "switch_nodes_and_recount" nsGraphNorthSouthUpwardCrossing 0 #[(0, 1, false), (0, 1, true)] #[(1, 0), (0, 1)]
  case "south_port_on_normal_node_below_long_edge_dummy" nnGraphSouthPortOnNormalNodeBelowLongEdgeDummy 1
    #[(0, 1, false), (0, 1, true)] #[(0, 1), (1, 0)]
  case "north_port_on_normal_node_above_long_edge_dummy" nnGraphNorthPortOnNormalNodeAboveLongEdgeDummy 1
    #[(1, 2, false), (1, 2, true)] #[(0, 1), (1, 0)]
  case "southern_two_western_edges" nsGraphSouthernTwoWesternEdges 1 #[(1, 2, false), (1, 2, true)] #[(1, 0), (0, 1)]
  case "southern_western_port_to_east_and_eastern_port_to_west" nnGraphSouthernWesternPortToEastAndEasternPortToWest 1
    #[(1, 2, false), (1, 2, true)] #[(1, 1), (1, 1)]
  case "northern_both_edges_western" nsGraphNorthernWesternEdges 1 #[(0, 1, false), (0, 1, true)] #[(0, 1), (1, 0)]
  case "northern_eastern_port_to_west_western_port_to_east" nsGraphNorthernEasternPortToWestWesternPortToEast 1
    #[(0, 1, false), (0, 1, true)] #[(1, 1), (1, 1)]
  case "normal_nodes_north_south_edges_have_crossings_to_long_edge_dummy (northern)" nnGraphNorthernDummyEdgeCrossing 1
    #[(0, 1, false), (1, 2, false)] #[(1, 0), (1, 0)]
  case "normal_nodes_north_south_edges_have_crossings_to_long_edge_dummy (southern)" nsGraphSouthernDummyEdgeCrossing 1
    #[(0, 1, false), (1, 2, false)] #[(1, 0), (1, 0)]
  case "normal_nodes_north_south_edges_have_crossings_to_long_edge_dummy_on_both_sides"
    nsGraphMultipleNorthSouthAndLongEdgeDummiesOnBothSides 1 #[(2, 3, false)] #[(2, 2)]
  let r ← runL do
    let layer ← layerNodes (← nsGraphLongEdgeDummyAndNormalNodeWithUnusedPortsOnSouthernSide) 1
    let southern := (← countNeighbouring layer 0 1).1
    let layer ← layerNodes (← nnGraphLongEdgeDummyAndNormalNodeWithUnusedPortsOnNorthernSide) 1
    return (southern, (← countNeighbouring layer 0 1).1)
  checkEq "ignores_unconnected_ports_for_normal_node_and_long_edge_dummies" r (0, 0)
  case "one_edge_west_one_edge_east_dont_cross" nnGraphNorthernEdgesFromEastAndWestNoCrossings 1 #[(0, 1, false)] #[(0, 0)]
  case "one_edge_east_one_edge_west_dont_cross" nnGraphNorthernEdgesFromEastAndWestNoCrossingsUpperEdgeEast 1
    #[(0, 1, false)] #[(0, 0)]
  case "given_polyline_routing_when_more_than_one_edge_into_ns_node_counts_these_too" (do
    let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 2
    setFixedOrderConstraint nsCfg mn[2]!
    addNorthSouthEdge nsCfg .north mn[2]! mn[1]! rn[0]! false
    addNorthSouthEdge nsCfg .north mn[2]! mn[0]! ln[0]! true
    eastWestEdgeFromPort nsCfg (← portAt mn[1]! 0) rn[1]!
    setGraphProp g LayeredOptions.EDGE_ROUTING EdgeRouting.polyline
    return g) 1 #[(0, 1, false)] #[(2, 1)]
  case "given_multiple_edges_in_one_ns_node_counts_crossings" (do
    let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 2
    setFixedOrderConstraint nsCfg mn[2]!
    addNorthSouthEdge nsCfg .north mn[2]! mn[1]! ln[0]! true
    let normalNodePort ← addPort nsCfg rn[1]! .west
    let dummyNodePort ← addPort nsCfg mn[1]! .east
    connect dummyNodePort normalNodePort
    setPortOrigin dummyNodePort (← portAt mn[2]! 0)
    addNorthSouthEdge nsCfg .north mn[2]! mn[0]! rn[0]! false
    return g) 1 #[(0, 1, false)] #[(1, 0)]
  case "edges_in_both_directions" (do
    let (g, ln, mn, rn) ← nsThreeLayerGraph 2 3 2
    setFixedOrderConstraint nsCfg mn[2]!
    addNorthSouthEdge nsCfg .north mn[2]! mn[1]! ln[1]! true
    let normalNodePort ← addPort nsCfg rn[1]! .west
    let dummyNodePort ← addPort nsCfg mn[1]! .east
    connect dummyNodePort normalNodePort
    setPortOrigin dummyNodePort (← portAt mn[2]! 0)
    addNorthSouthEdge nsCfg .north mn[2]! mn[0]! ln[0]! true
    let normalNodePort ← addPort nsCfg rn[0]! .west
    let dummyNodePort ← addPort nsCfg mn[0]! .east
    connect dummyNodePort normalNodePort
    setPortOrigin dummyNodePort (← portAt mn[2]! 1)
    return g) 1 #[(0, 1, false)] #[(1, 1)]
  case "multiple_edges_in_both_directions_ns_node" (do
    let (g, ln, mn, rn) ← nsThreeLayerGraph 2 3 2
    setFixedOrderConstraint nsCfg mn[2]!
    addNorthSouthEdge nsCfg .north mn[2]! mn[1]! ln[1]! true
    let normalNodePort ← addPort nsCfg rn[1]! .west
    let dummyNodePort ← addPort nsCfg mn[1]! .east
    connect dummyNodePort normalNodePort
    connect dummyNodePort normalNodePort
    setPortOrigin dummyNodePort (← portAt mn[2]! 0)
    addNorthSouthEdge nsCfg .north mn[2]! mn[0]! rn[0]! false
    let normalNodePort ← addPort nsCfg rn[0]! .east
    let dummyNodePort ← addPort nsCfg mn[0]! .west
    connect dummyNodePort normalNodePort
    connect dummyNodePort normalNodePort
    setPortOrigin dummyNodePort (← portAt mn[2]! 1)
    return g) 1 #[(0, 1, false)] #[(2, 2)]

/-! ## `tests/intermediate/greedyswitch/switch_decider_test.rs` -/

/-- `assign_ids(root)` of the switch decider test: every graph reachable through nested graphs,
port ids restarting at 0 per graph. -/
partial def assignIdsRec (root : LGraphId) : LayeredM Unit := do
  let _ ← assignIds root
  for l in (← getGraph root).layers do
    for n in (← getLayer l).nodes do
      if let some nested := (← getNode n).nestedGraph then assignIdsRec nested

/-- `count_ports(node_order)`. -/
def countPorts (order : Array (Array LNodeId)) : LayeredM Nat := do
  let a ← get
  return order.foldl (fun acc layer => layer.foldl (fun acc n => acc + (a.node n).ports.size) acc) 0

/-- `get_decider(graph, greedy_type, free_layer_index, direction)`. -/
def getDecider (g : LGraphId) (greedyType : CrossMinType) (freeLayerIndex : Nat) (direction : CrossingCountSide) :
    LayeredM (SwitchDecider × Array (Array LNodeId)) := do
  assignIdsRec g
  let order ← nodeArray g
  let nPorts ← countPorts order
  let filler ← CrossingMatrixFiller.new greedyType order freeLayerIndex direction
  let decider ← SwitchDecider.new ((order[freeLayerIndex]?).getD #[]) filler (Array.replicate nPorts 0) none false
  return (decider, order)

/-- `get_decider_with_parent(graph, parent_graph, parent_node, greedy_type, free_layer_index, direction)`. -/
def getDeciderWithParent (g parentGraph : LGraphId) (parentNode : LNodeId) (greedyType : CrossMinType)
    (freeLayerIndex : Nat) (direction : CrossingCountSide) : LayeredM (SwitchDecider × Array (Array LNodeId)) := do
  assignIdsRec g
  assignIdsRec parentGraph
  let order ← nodeArray g
  let nPorts ← countPorts order
  let parentNodeOrder ← nodeArray parentGraph
  let parentPorts ← countPorts parentNodeOrder
  let parentLayerIndex ← layerIndexOfNode parentNode
  let context : ParentCrossingContext := {
    parentNodeOrder, parentPortPositions := Array.replicate parentPorts 0, parentLayerIndex,
    rightMostLayer := freeLayerIndex + 1 == order.size }
  let filler ← CrossingMatrixFiller.new greedyType order freeLayerIndex direction
  let decider ← SwitchDecider.new ((order[freeLayerIndex]?).getD #[]) filler (Array.replicate nPorts 0) (some context) true
  return (decider, order)

/-- `nested_graph(node)`: the node's nested graph, created with the test options. -/
def nestedGraphOf (n : LNodeId) : LayeredM LGraphId := do
  if let some g := (← getNode n).nestedGraph then return g
  let g ← newGraph nsCfg
  modifyGraph g fun x => { x with parentNode := some n }
  modifyNode n fun x => { x with nestedGraph := some g }
  return g

/-- `add_external_port_dummy_node_to_layer(layer, port)`. -/
def addExternalPortDummyNodeToLayer (layer : LayerId) (port : LPortId) : LayeredM LNodeId := do
  let g := (← getLayer layer).owner
  let node ← addNode nsCfg g layer
  let portSide := (← getPort port).side
  modifyNode node fun x => { x with
    type := .externalPort
    internal := { x.internal with origin := some (.lPort port), extPortSide := portSide } }
  modifyPort port fun x => { x with internal := { x.internal with portDummy := some node, insideConnections := true } }
  addGraphProperty node .externalPorts
  return node

/-- `add_external_port_dummies_to_layer(layer, ports)`: eastern ports top-down, others reversed. -/
def addExternalPortDummiesToLayer (layer : LayerId) (ports : Array LPortId) : LayeredM (Array LNodeId) := do
  if ports.isEmpty then return #[]
  let side := (← getPort ports[0]!).side
  let mut nodes := #[]
  for i in [0:ports.size] do
    let portIndex := if side == .east then i else ports.size - 1 - i
    nodes := nodes.push (← addExternalPortDummyNodeToLayer layer ports[portIndex]!)
  return nodes

def sdGraphCrossFormed : LayeredM LGraphId := do
  let (g, ln, rn) ← nsTwoLayerGraph 2 2
  eastWestEdgeFromTo nsCfg ln[0]! rn[1]!
  eastWestEdgeFromTo nsCfg ln[1]! rn[0]!
  return g

def sdGraphOneNode : LayeredM LGraphId := do
  let g ← newGraph nsCfg
  let l ← makeLayer g
  let _ ← addNode nsCfg g l
  return g

def sdGraphMultipleEdgesBetweenSameNodes : LayeredM LGraphId := do
  let (g, ln, rn) ← nsTwoLayerGraph 2 2
  eastWestEdgeFromTo nsCfg ln[0]! rn[1]!
  eastWestEdgeFromTo nsCfg ln[0]! rn[1]!
  eastWestEdgeFromTo nsCfg ln[1]! rn[0]!
  eastWestEdgeFromTo nsCfg ln[1]! rn[0]!
  return g

def sdGraphInLayerEdges : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 1
  eastWestEdgeFromTo nsCfg mn[1]! rn[0]!
  eastWestEdgeFromTo nsCfg ln[0]! mn[1]!
  addInLayerEdge nsCfg mn[0]! mn[2]! .west
  return g

def sdGraphMoreComplexThreeLayer : LayeredM LGraphId := do
  let c := nsCfg
  let (g, ln, mn, rn) ← nsThreeLayerGraph 3 2 3
  let leftMiddlePort ← addPort c ln[1]! .east
  let middleLowerEast ← addPort c mn[1]! .east
  let middleUpperEast ← addPort c mn[0]! .east
  let rightUpper ← addPort c rn[0]! .west
  let rightMiddle ← addPort c rn[1]! .west
  connect middleUpperEast rightUpper
  connect middleUpperEast rightMiddle
  connect middleUpperEast rightMiddle
  eastWestEdgeFromPort c middleLowerEast rn[2]!
  eastWestEdgeFromPort c leftMiddlePort mn[0]!
  eastWestEdgeFromNode c mn[1]! rightUpper
  eastWestEdgeFromPort c leftMiddlePort mn[1]!
  eastWestEdgeFromTo c ln[2]! mn[0]!
  eastWestEdgeFromTo c ln[0]! mn[0]!
  return g

def sdGraphSwitchOnlyOneSided : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 2 2 2
  eastWestEdgeFromTo nsCfg mn[0]! rn[0]!
  eastWestEdgeFromTo nsCfg mn[1]! rn[1]!
  eastWestEdgeFromTo nsCfg ln[0]! mn[1]!
  eastWestEdgeFromTo nsCfg ln[1]! mn[0]!
  return g

def sdGraphSwitchOnlyEastOneSided : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 2 2 2
  eastWestEdgeFromTo nsCfg ln[0]! mn[0]!
  eastWestEdgeFromTo nsCfg ln[1]! mn[1]!
  eastWestEdgeFromTo nsCfg mn[0]! rn[1]!
  eastWestEdgeFromTo nsCfg mn[1]! rn[0]!
  return g

def sdGraphCrossFormedWithConstraintsInSecondLayer : LayeredM LGraphId := do
  let g ← sdGraphCrossFormed
  let nodes := (← getLayer (← getGraph g).layers[1]!).nodes
  -- set_in_layer_order_constraint(nodes[0], nodes[1])
  modifyNode nodes[0]! fun x => { x with internal := { x.internal with inLayerSuccessorConstraints := #[nodes[1]!] } }
  return g

def sdGraphThreeLayerNorthSouthCrossing : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 3 1
  setFixedOrderConstraint nsCfg mn[0]!
  setFixedOrderConstraint nsCfg rn[0]!
  addNorthSouthEdge nsCfg .south mn[0]! mn[2]! rn[0]! false
  addNorthSouthEdge nsCfg .south mn[0]! mn[1]! rn[0]! false
  eastWestEdgeFromTo nsCfg ln[0]! mn[0]!
  return g

def sdGraphSwitchedProblem : LayeredM LGraphId := do
  let (g, ln, rn) ← nsTwoLayerGraph 2 4
  eastWestEdgeFromTo nsCfg ln[1]! rn[2]!
  eastWestEdgeFromTo nsCfg ln[1]! rn[3]!
  eastWestEdgeFromTo nsCfg ln[0]! rn[0]!
  eastWestEdgeFromTo nsCfg ln[0]! rn[1]!
  eastWestEdgeFromTo nsCfg ln[0]! rn[2]!
  return g

def sdGraphLayoutUnitPreventsSwitchWithNodeWithNorthernEdges : LayeredM LGraphId := do
  let (g, ln, rn) ← nsTwoLayerGraph 3 3
  addNorthSouthEdge nsCfg .north ln[1]! ln[0]! rn[0]! false
  eastWestEdgeFromTo nsCfg ln[1]! rn[2]!
  eastWestEdgeFromTo nsCfg ln[2]! rn[1]!
  return g

def sdGraphLayoutUnitPreventsSwitchWithNodeWithSouthernEdges : LayeredM LGraphId := do
  let (g, ln, rn) ← nsTwoLayerGraph 4 3
  eastWestEdgeFromTo nsCfg ln[0]! rn[1]!
  eastWestEdgeFromTo nsCfg ln[1]! rn[0]!
  addNorthSouthEdge nsCfg .south ln[1]! ln[2]! rn[2]! false
  return g

def sdGraphLayoutUnitDoesNotPreventSwitchWithLongEdgeDummy : LayeredM LGraphId := do
  let (g, ln, mn, rn) ← nsThreeLayerGraph 1 4 3
  setAsLongEdgeDummy mn[0]!
  eastWestEdgeFromTo nsCfg ln[0]! mn[0]!
  eastWestEdgeFromTo nsCfg mn[0]! rn[1]!
  eastWestEdgeFromTo nsCfg mn[1]! rn[0]!
  eastWestEdgeFromTo nsCfg mn[1]! rn[0]!
  addNorthSouthEdge nsCfg .south mn[1]! mn[2]! rn[2]! false
  return g

/-- A decider query on the free layer's current order: `ask u l` or `notifyAndSwitch u l`
(Rust `notify_of_switch` + `switch_nodes`). -/
inductive DStep where
  | ask (u l : Nat)
  | notifyAndSwitch (u l : Nat)

/-- `get_decider(graph, type, free_layer, direction)` then the steps; returns the `ask` answers. -/
def runDecider (graph : LayeredM LGraphId) (greedyType : CrossMinType) (freeLayerIndex : Nat)
    (direction : CrossingCountSide) (steps : Array DStep) : IO (Array Bool) := runL do
  let (decider, order) ← getDecider (← graph) greedyType freeLayerIndex direction
  let mut layer := order[freeLayerIndex]!
  let mut answers := #[]
  for s in steps do
    match s with
    | .ask u l => answers := answers.push (← decider.doesSwitchReduceCrossings layer[u]! layer[l]!)
    | .notifyAndSwitch u l =>
      decider.notifyOfSwitch layer[u]! layer[l]!
      layer := layer.swapIfInBounds u l
  return answers

def switchDeciderTests : Suite := suite "layered.greedyswitch.switch_decider" do
  for t in #[CrossMinType.oneSidedGreedySwitch, CrossMinType.twoSidedGreedySwitch] do
    let oneSided := t == .oneSidedGreedySwitch
    let case (name : String) (graph : LayeredM LGraphId) (freeLayer : Nat) (direction : CrossingCountSide)
        (steps : Array DStep) (expected : Array Bool) : TestM Unit := do
      checkEq s!"{name} ({t})" (← runDecider graph t freeLayer direction steps) expected
    case "cross_formed west" sdGraphCrossFormed 1 .west #[.ask 0 1] #[true]
    case "cross_formed east" sdGraphCrossFormed 0 .east #[.ask 0 1] #[true]
    case "one_node west" sdGraphOneNode 0 .west #[.ask 0 0] #[false]
    case "one_node east" sdGraphOneNode 0 .east #[.ask 0 0] #[false]
    case "in_layer_switchable west" sdGraphInLayerEdges 1 .west #[.ask 0 1] #[true]
    case "in_layer_switchable east" sdGraphInLayerEdges 1 .east #[.ask 0 1] #[true]
    case "multiple_edges_between_same_nodes west" sdGraphMultipleEdgesBetweenSameNodes 1 .west #[.ask 0 1] #[true]
    case "multiple_edges_between_same_nodes east" sdGraphMultipleEdgesBetweenSameNodes 0 .east #[.ask 0 1] #[true]
    case "self_loops west" (graphCrossWithManySelfLoops nsCfg) 1 .west #[.ask 0 1] #[true]
    case "self_loops east" (graphCrossWithManySelfLoops nsCfg) 0 .east #[.ask 0 1] #[true]
    case "north_south_port_crossing" sdGraphThreeLayerNorthSouthCrossing 1 .west #[.ask 1 2] #[oneSided]
    case "more_complex (1, west)" sdGraphMoreComplexThreeLayer 1 .west #[.ask 0 1] #[false]
    case "more_complex (2, west)" sdGraphMoreComplexThreeLayer 2 .west #[.ask 0 1, .ask 1 2] #[true, false]
    case "more_complex (1, east)" sdGraphMoreComplexThreeLayer 1 .east #[.ask 0 1] #[false]
    case "more_complex (0, east)" sdGraphMoreComplexThreeLayer 0 .east #[.ask 0 1, .ask 1 2] #[false, true]
    case "switch_only_true_for_one_sided" sdGraphSwitchOnlyOneSided 1 .west #[.ask 0 1] #[oneSided]
    case "switch_only_true_for_one_sided_eastern_side" sdGraphSwitchOnlyEastOneSided 1 .east #[.ask 0 1] #[oneSided]
    case "constraints_prevent_switch" sdGraphCrossFormedWithConstraintsInSecondLayer 1 .west #[.ask 0 1] #[false]
    case "in_layer_unit_constraints_prevent_switch" nnGraphWhereLayoutUnitPreventsSwitch 0 .west #[.ask 1 2] #[false]
    case "switch_and_recount west" sdGraphCrossFormed 1 .west #[.ask 0 1] #[true]
    case "switch_and_recount east" sdGraphCrossFormed 0 .east #[.ask 0 1, .notifyAndSwitch 0 1, .ask 0 1] #[true, false]
    case "switch_and_recount_counter_bug" (do
      let c := nsCfg
      let (g, ln, rn) ← nsTwoLayerGraph 2 4
      let ltp ← addPort c ln[0]! .east
      let llp ← addPort c ln[1]! .east
      let rtp ← addPort c rn[0]! .west
      connect llp rtp
      eastWestEdgeFromPort c llp rn[2]!
      connect ltp rtp
      eastWestEdgeFromPort c ltp rn[1]!
      eastWestEdgeFromPort c ltp rn[3]!
      return g) 1 .west
      #[.ask 0 1, .ask 1 2, .ask 2 3, .notifyAndSwitch 0 1, .ask 0 1, .ask 1 2, .ask 2 3,
        .notifyAndSwitch 2 3, .ask 0 1, .ask 1 2, .ask 2 3, .notifyAndSwitch 1 2, .ask 0 1, .ask 1 2, .ask 2 3]
      #[true, false, true, false, false, true, false, true, false, false, false, false]
    case "switch_and_recount_reduced_counter_bug" sdGraphSwitchedProblem 1 .west #[.ask 0 1, .ask 1 2, .ask 2 3]
      #[false, false, false]
    case "should_switch_with_long_edge_dummies (northern)" nnGraphNorthernDummyEdgeCrossing 1 .west
      (if oneSided then #[.ask 1 2, .ask 0 1] else #[.ask 1 2]) (if oneSided then #[true, true] else #[true])
    case "should_switch_with_long_edge_dummies (southern)" nsGraphSouthernDummyEdgeCrossing 1 .west
      (if oneSided then #[.ask 0 1, .ask 1 2] else #[.ask 0 1]) (if oneSided then #[true, true] else #[true])
    case "layout_unit_constraint_prevents_switch_with_node_with_northern_ports"
      sdGraphLayoutUnitPreventsSwitchWithNodeWithNorthernEdges 0 .east #[.ask 1 2] #[false]
    case "layout_unit_constraint_prevents_switch_with_node_with_southern_ports"
      sdGraphLayoutUnitPreventsSwitchWithNodeWithSouthernEdges 0 .east #[.ask 0 1] #[false]
    case "layout_unit_constraint_does_not_prevent_switch_with_long_edge_dummy"
      sdGraphLayoutUnitDoesNotPreventSwitchWithLongEdgeDummy 1 .east #[.ask 0 1] #[true]
    if t == .twoSidedGreedySwitch then
      let r ← runL do
        let g ← newGraph nsCfg
        let leftNode ← addNode nsCfg g (← makeLayer g)
        let rn ← addNodes nsCfg g (← makeLayer g) 2
        let leftPorts ← addPorts nsCfg leftNode 2 .east
        let nested ← nestedGraphOf leftNode
        let nestedLayer ← makeLayer nested
        let dummies ← addExternalPortDummiesToLayer nestedLayer leftPorts
        eastWestEdgeFromPort nsCfg leftPorts[0]! rn[1]!
        eastWestEdgeFromPort nsCfg leftPorts[1]! rn[0]!
        let (decider, _) ← getDeciderWithParent nested g leftNode t 0 .east
        let before ← decider.doesSwitchReduceCrossings dummies[0]! dummies[1]!
        decider.notifyOfSwitch dummies[0]! dummies[1]!
        let after ← decider.doesSwitchReduceCrossings dummies[0]! dummies[1]!
        return (before, after)
      checkEq s!"switching_dummy_nodes_notifies_port_switch ({t})" r (true, false)

/-! ## Lean-only smoke tests (no elk-rs counterpart) -/

def greedySwitchHeuristicTests : Suite := suite "layered.greedyswitch.greedy_switch_heuristic" do
  for t in #[CrossMinType.oneSidedGreedySwitch, CrossMinType.twoSidedGreedySwitch] do
    let r ← runL do
      let g ← sdGraphCrossFormed
      let _ ← assignIds g
      let order ← nodeArray g
      let h ← GreedySwitchHeuristic.new t false g
      Initializable.init #[h.initializable] order
      let (forward, changedForward) ← h.minimizeCrossings order 1 true false
      let (first, changedFirst) ← h.setFirstLayerOrder order false
      let a ← get
      let layerIds := (a.graph g).layers.map fun l => (a.layer l).id
      return (forward == order.modify 1 (·.swapIfInBounds 0 1), changedForward,
        first == order.modify 1 (·.swapIfInBounds 0 1), changedFirst, layerIds, ← h.alwaysImproves, ← h.isDeterministic)
    -- a backward `setFirstLayerOrder` sweeps the last layer counting eastern edges only (one-sided:
    -- none there, so no switch) or both sides (two-sided)
    let twoSided := t == .twoSidedGreedySwitch
    checkEq s!"minimize crossings switches the cross ({t})" r
      (true, true, twoSided, twoSided, #[(0 : Int), 1], twoSided, true)

def crossMinSnapshotTests : Suite := suite "layered.p3order.cross_min_snapshot" do
  let r ← runL do
    let g ← acCrossForm
    let order ← nodeArray g
    let counter ← AllCrossingsCounter.new g order
    Initializable.init #[counter.initializable] order
    let s ← CrossMinSnapshot.build order 4
    let a ← get
    let n := order[1]![1]!
    let p := (a.node order[0]![0]!).ports[0]!
    return (s.nNodes, s.nPorts, s.nodeFlatIndex n, s.nodeId n, s.nodeLayerIndex n, s.portId p,
      s.portSuccessors (s.portId p), s.portPredecessors 3, s.portOwnerLayer 3, s.portSideOf 0, s.nodePorts 2,
      s.nodeRef 3 == n, s.portRefOpt 0 == some p, s.sameLayer order[0]![0]! order[0]![1]!)
  checkEq "build on the cross-formed graph" r
    (4, 4, 3, 1, 1, 0, #[3], #[0], 1, PortSide.east, #[2], true, true, true)

/-! ## Differential tests of the Lean fast paths -/

/-- A random number in `[0, bound)` (`bound > 0`). -/
def rnd (r : IO.Ref Random) (bound : Nat) : BaseIO Nat := do
  return (← r.modifyGet (·.nextInt bound)).toNat

/-- A random permutation of `xs` (Fisher-Yates). -/
def shuffle {α : Type} [Inhabited α] (r : IO.Ref Random) (xs : Array α) : BaseIO (Array α) := do
  let mut a := xs
  for k in [0:a.size] do
    let i := a.size - 1 - k
    if i > 0 then
      let j ← rnd r (i + 1)
      a := a.swapIfInBounds i j
  return a

/-- A random layered graph of `layers` layers: nodes with ports on random sides in random order,
edges between consecutive layers (several per port: hyperedges), in-layer edges, edges skipping a
layer and ports without edges; ids assigned in traversal order. -/
def randomLayers (r : IO.Ref Random) (layers : Nat) : LayeredM (LGraphId × Nat) := do
  let g ← newGraph {}
  let ls ← makeLayers g layers
  let mut ports : Array (Array LPortId) := Array.replicate layers #[]
  for h : li in [0:ls.size] do
    let n := 1 + (← rnd r 6)
    for _ in [0:n] do
      let node ← addNode {} g ls[li]
      for _ in [0:(← rnd r 5)] do
        let side := match ← rnd r 6 with
          | 0 => PortSide.north
          | 1 => .south
          | 2 | 3 => .east
          | _ => .west
        let p ← addPort {} node side
        ports := ports.modify li (·.push p)
  for _ in [0:(← rnd r 30)] do
    let kind ← rnd r 12
    let la ← rnd r layers
    let lb := if kind < 8 then la + 1 else if kind < 10 then la else la + 2
    if h1 : la < ports.size then
      if h2 : lb < ports.size then
        let pa := ports[la]
        let pb := ports[lb]
        if pa.size > 0 && pb.size > 0 then
          let s := pa[← rnd r pa.size]!
          let t := pb[← rnd r pb.size]!
          if (← rnd r 4) == 0 then connect t s else connect s t
  let nPorts ← Tests.Layered.P3Counting.assignIds g
  return (g, nPorts)

/-- Runs `countCrossingsPure` and `countCrossingsFast` on random layer pairs (with persisting
positions and shuffled node orders): the number of differing results (crossings, positions, or a
scratch that is not zero afterwards) and of runs with crossings. -/
def hyperedgeDifferential (seeds : Nat) : IO (Nat × Nat) := do
  let mut mismatches := 0
  let mut nonZero := 0
  for seed in [0:seeds] do
    let r ← IO.mkRef (Random.ofInt seed)
    let (m, nz) ← runL do
      let (g, nPorts) ← randomLayers r 3
      let mut order ← nodeArray g
      let mut posA : Array Int := Array.replicate nPorts 0
      let mut posB : Array Int := Array.replicate nPorts 0
      let mut scratch : HyperedgeCrossingsCounter.Scratch := {}
      let mut m := 0
      let mut nz := 0
      for _ in [0:4] do
        for li in [0:order.size - 1] do
          let a ← get
          let (ca, pa) := HyperedgeCrossingsCounter.countCrossingsPure a posA order[li]! order[li + 1]!
          let (cb, pb, sc) := HyperedgeCrossingsCounter.countCrossingsFast a posB scratch order[li]! order[li + 1]!
          posA := pa
          posB := pb
          scratch := sc
          let clean := sc.marks.toList.all (· == 0) && sc.slots.all (· == 0)
          if ca != cb || pa != pb || !clean then m := m + 1
          if ca != 0 then nz := nz + 1
        order ← order.mapM fun layer => shuffle r layer
      return (m, nz)
    mismatches := mismatches + m
    nonZero := nonZero + nz
  return (mismatches, nonZero)

def fastPathTests : Suite := suite "layered.p3counting.fast_paths" do
  let (mismatches, nonZero) ← hyperedgeDifferential 400
  checkEq "hyperedge fast = port (400 random graphs, 3200 layer pairs)" mismatches 0
  check s!"hyperedge differential runs count crossings ({nonZero} with crossings)" (nonZero > 400)

/-! ## Suites -/

def suites : Array Suite := #[bitTests, crossMinUtilTests, crossingsCounterTests, allCrossingsCounterTests,
  northSouthAllCrossingsTests, inLayerTwoNodeTests, betweenLayerTwoNodeTests, northSouthNeighbouringTests,
  switchDeciderTests, greedySwitchHeuristicTests, crossMinSnapshotTests, fastPathTests]

end Tests.Layered.P3Counting
