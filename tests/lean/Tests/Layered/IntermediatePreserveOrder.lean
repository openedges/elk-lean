import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Intermediate.ModelOrderProcessors
/-!
Tests of `org.eclipse.elk.alg.layered.intermediate.preserveorder` and `SortByInputModelProcessor`.

Ported from elk-rs: `tests/p3_order/sort_by_input_model_processor_test.rs`,
`tests/p3_order/concrete_sort_by_input_model_test.rs` (all hand-built-graph tests) and the
`relation_tests` modules of `model_order_node_comparator.rs` / `model_order_port_comparator.rs`
(dense relations against the original set-based updates). The comparator case tests build small
graphs by hand; the expected values are derived by hand from the Rust code paths ("hand: …").
-/
namespace Tests.Layered.IntermediatePreserveOrder

open Tests Elk.Graph Elk.Core.Util Elk.Core.Options Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
  Elk.Alg.Layered.Intermediate Elk.Alg.Layered.Intermediate.Preserveorder
open Elk (ElkEnum)

/-! ## Graph building helpers (Rust test helpers) -/

/-- Rust `graph_with_layers(count)`: `CONSIDER_MODEL_ORDER_STRATEGY = NODES_AND_EDGES`,
`LONG_EDGE_STRATEGY = EQUAL`, `PORT_MODEL_ORDER = false`. -/
def graphWithLayers (count : Nat) (strategy : OrderingStrategy := .nodesAndEdges) :
    LayeredM (LGraphId × Array LayerId) := do
  let g ← LayeredM.createGraph
  let mut layers : Array LayerId := #[]
  for _ in [0:count] do
    layers := layers.push (← LayeredM.createLayer g)
  LayeredM.modifyGraph g fun x => { x with layers := layers }
  LayeredM.setGraphProp g LayeredOptions.CONSIDER_MODEL_ORDER_STRATEGY strategy
  LayeredM.setGraphProp g LayeredOptions.CONSIDER_MODEL_ORDER_LONG_EDGE_STRATEGY LongEdgeOrderingStrategy.equal
  LayeredM.setGraphProp g LayeredOptions.CONSIDER_MODEL_ORDER_PORT_MODEL_ORDER false
  return (g, layers)

/-- Rust `add_node(graph, layer, model_order)` (optionally without model order / as a dummy). -/
def addNode (g : LGraphId) (layer : LayerId) (modelOrder : Option Int) (type : NodeType := .normal) : LayeredM LNodeId := do
  let n ← LayeredM.createNode g { type := type }
  LayeredM.modifyNode n fun x => { x with internal.modelOrder := modelOrder }
  LayeredM.setNodeLayer n (some layer)
  return n

/-- Rust `add_port(node, side)` (optionally with a port model order). -/
def addPort (n : LNodeId) (side : PortSide) (modelOrder : Option Int := none) : LayeredM LPortId := do
  let p ← LayeredM.createPort
  LayeredM.modifyPort p fun x => { x.setSide side with internal.modelOrder := modelOrder }
  LayeredM.setPortNode p (some n)
  return p

/-- Rust `connect_with_model_order(source, target, model_order)`. -/
def connect (s t : LPortId) (modelOrder : Option Int := none) : LayeredM LEdgeId := do
  let e ← LayeredM.createEdge
  LayeredM.setEdgeSource e (some s)
  LayeredM.setEdgeTarget e (some t)
  LayeredM.modifyEdge e fun x => { x with internal.modelOrder := modelOrder }
  return e

/-- Sets `Layer.id` to the layer index (what `SortByInputModelProcessor` does before comparing). -/
def setLayerIds (layers : Array LayerId) : LayeredM Unit := do
  let mut i : Int := 0
  for l in layers do
    LayeredM.modifyLayer l fun x => { x with id := i }
    i := i + 1

/-- Sets `LONG_EDGE_TARGET_NODE` of a port. -/
def setLongEdgeTargetNode (p : LPortId) (t : LNodeId) : LayeredM Unit :=
  LayeredM.modifyPort p fun x => { x with internal.longEdgeTargetNode := some t }

/-- Rust `run_sorter_direct(graph)`. -/
def runSorter (g : LGraphId) : LayeredM Unit :=
  SortByInputModelProcessor.processor.process g ProgressMonitor.null

/-- One comparison on a fresh copy of the arena. -/
def nodeCmp (a : LGraphArena) (c : ModelOrderNodeComparator) (n1 n2 : LNodeId) : IO Int := do
  let ((r, _), _) ← LayeredM.run (c.compare n1 n2) a
  return r

/-- One comparison on a fresh copy of the arena. -/
def portCmp (a : LGraphArena) (c : ModelOrderPortComparator) (p1 p2 : LPortId) : IO Int := do
  let ((r, _), _) ← LayeredM.run (c.compare p1 p2) a
  return r

/-- A node comparator with an empty context. -/
def nodeComparator (previousLayer : Array LNodeId := #[]) (strategy : OrderingStrategy := .nodesAndEdges)
    (longEdge : LongEdgeOrderingStrategy := .equal) (graph : ModelOrderGraphContext := {}) (beforePorts : Bool := false) :
    ModelOrderNodeComparator :=
  ModelOrderNodeComparator.new graph previousLayer strategy longEdge .onlyWithinGroup beforePorts

/-- A port comparator with an empty context. -/
def portComparator (previousLayer : Array LNodeId := #[]) (strategy : OrderingStrategy := .nodesAndEdges)
    (targets : Option (Array (LNodeId × Int)) := none) (portModelOrder : Bool := false)
    (graph : ModelOrderGraphContext := {}) : ModelOrderPortComparator :=
  ModelOrderPortComparator.new graph previousLayer strategy targets portModelOrder

/-! ## CMGroupModelOrderCalculator -/

def cmGroupTests : Suite := suite "layered.intermediate.preserveorder.cmGroupModelOrder" do
  let withMo (mo : Option Int) (group : Option Int) : LNode :=
    let n : LNode := { internal := { modelOrder := mo } }
    match group with
    | some gid => { n with props := n.props.set LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID gid }
    | none => n
  let enforced : ModelOrderGraphContext := { groupOrderStrategy := .enforced, enforcedGroupOrders := #[1, 2] }
  let calcMo := CMGroupModelOrderCalculator.calculateModelOrderOrGroupModelOrderOf
  checkEq "no MODEL_ORDER gives -1 (hand)" (calcMo enforced (withMo none (some 1)) (withMo (some 3) (some 2)) 10) (-1)
  checkEq "ONLY_WITHIN_GROUP uses the model order (hand)" (calcMo {} (withMo (some 5) (some 1)) (withMo (some 3) (some 2)) 10) 5
  checkEq "ENFORCED with both groups enforced: offset * group + order (hand: 10*1+5)"
    (calcMo enforced (withMo (some 5) (some 1)) (withMo (some 3) (some 2)) 10) 15
  checkEq "ENFORCED but the other group is not enforced: model order (hand)"
    (calcMo enforced (withMo (some 5) (some 1)) (withMo (some 3) (some 6)) 10) 5
  checkEq "ENFORCED with default group ids 0 not enforced (hand)"
    (calcMo enforced (withMo (some 5) none) (withMo (some 3) none) 10) 5
  checkEqR "unavailable context = Rust try_lock failure defaults" ModelOrderGraphContext.unavailable
    { maxModelOrderNodes := 0, groupOrderStrategy := .onlyWithinGroup, enforcedGroupOrders := #[] }
  let ((ctxDefault, ctxSet), _) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let d ← ModelOrderGraphContext.ofGraph g
      LayeredM.setGraphProp g LayeredOptions.GROUP_MODEL_ORDER_CM_GROUP_ORDER_STRATEGY GroupOrderStrategy.enforced
      LayeredM.setGraphProp g LayeredOptions.GROUP_MODEL_ORDER_CM_ENFORCED_GROUP_ORDERS #[3, 4]
      LayeredM.modifyGraph g fun x => { x with internal.maxModelOrderNodes := 12 }
      let s ← ModelOrderGraphContext.ofGraph g
      return (d, s))
  checkEqR "ofGraph defaults (enforced orders default [1,2,6,7,10,11])" ctxDefault
    { maxModelOrderNodes := 0, groupOrderStrategy := .onlyWithinGroup, enforcedGroupOrders := #[1, 2, 6, 7, 10, 11] }
  checkEqR "ofGraph reads the graph options" ctxSet
    { maxModelOrderNodes := 12, groupOrderStrategy := .enforced, enforcedGroupOrders := #[3, 4] }

/-! ## ModelOrderNodeComparator -/

/-- Two layers: `s0, s1` (model orders 0, 1, one east port each) in layer 0; in layer 1 `u` (model
order 0) connected from `s1`, `v` (model order 1) from `s0`, and a long edge dummy `d` from `s1`. -/
def previousLayerGraph : LayeredM (Array LNodeId) := do
  let (g, layers) ← graphWithLayers 2
  setLayerIds layers
  let s0 ← addNode g layers[0]! (some 0)
  let s1 ← addNode g layers[0]! (some 1)
  let s0e ← addPort s0 .east
  let s1e ← addPort s1 .east
  let u ← addNode g layers[1]! (some 0)
  let v ← addNode g layers[1]! (some 1)
  let d ← addNode g layers[1]! none .longEdge
  let _ ← connect s1e (← addPort u .west) (some 0)
  let _ ← connect s0e (← addPort v .west) (some 1)
  let _ ← connect s1e (← addPort d .west) (some 2)
  return #[s0, s1, u, v, d]

/-- Layer 0: `s` with east ports `qa, qb`; layer 1: dummies `d1` (from `qb`) and `d2` (from `qa`). -/
def sameSourceGraph : LayeredM (Array LNodeId) := do
  let (g, layers) ← graphWithLayers 2
  setLayerIds layers
  let s ← addNode g layers[0]! (some 0)
  let qa ← addPort s .east
  let qb ← addPort s .east
  let d1 ← addNode g layers[1]! none .longEdge
  let d2 ← addNode g layers[1]! none .longEdge
  let _ ← connect qb (← addPort d1 .west) (some 7)
  let _ ← connect qa (← addPort d2 .west) (some 1)
  return #[s, d1, d2]

/-- Feedback dummy: layer 1 holds `x` (model order 5), `n` (model order 2, no ports) and a long edge
dummy `d` with an in-layer edge `x → d` and an edge `d → t` (`t` in layer 2). -/
def feedbackGraph : LayeredM (Array LNodeId) := do
  let (g, layers) ← graphWithLayers 3
  setLayerIds layers
  let x ← addNode g layers[1]! (some 5)
  let n ← addNode g layers[1]! (some 2)
  let d ← addNode g layers[1]! none .longEdge
  let t ← addNode g layers[2]! (some 9)
  let _ ← connect (← addPort x .east) (← addPort d .west) (some 0)
  let _ ← connect (← addPort d .east) (← addPort t .west) (some 0)
  return #[x, n, d, t]

/-- `s` (layer 0) → long edge dummy `d` (layer 1, incoming edge model order 4) → `t` (layer 2); `n`
(model order 1) in layer 1 without ports. -/
def longEdgeStrategyGraph : LayeredM (Array LNodeId) := do
  let (g, layers) ← graphWithLayers 3
  setLayerIds layers
  let s ← addNode g layers[0]! (some 0)
  let d ← addNode g layers[1]! none .longEdge
  let n ← addNode g layers[1]! (some 1)
  let t ← addNode g layers[2]! (some 2)
  let _ ← connect (← addPort s .east) (← addPort d .west) (some 4)
  let _ ← connect (← addPort d .east) (← addPort t .west) (some 4)
  return #[s, d, n, t]

def nodeComparatorTests : Suite := suite "layered.intermediate.preserveorder.nodeComparator" do
  -- plain model order
  let (ns, a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let n3 ← addNode g layers[0]! (some 3)
      let n1 ← addNode g layers[0]! (some 1)
      return #[n3, n1])
  checkEq "two normal nodes: bigger model order is bigger (hand)" (← nodeCmp a (nodeComparator) ns[0]! ns[1]!) 1
  checkEq "two normal nodes: smaller model order is smaller (hand)" (← nodeCmp a (nodeComparator) ns[1]! ns[0]!) (-1)
  -- no model orders and transitivity
  let (ns, a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let na ← addNode g layers[0]! none
      let nb ← addNode g layers[0]! none
      let nc ← addNode g layers[0]! none
      return #[na, nb, nc])
  let ((r1, r2, r3, r4), _) ← LayeredM.run (do
      let c0 := nodeComparator
      let (r1, c) ← c0.compare ns[0]! ns[1]!
      let (r2, c) ← c.compare ns[1]! ns[0]!
      let (_, c) ← c.compare ns[1]! ns[2]!
      let (r3, _) ← c.compare ns[2]! ns[0]!
      let (r4, _) ← c0.compare ns[2]! ns[0]!
      return (r1, r2, r3, r4)) a
  checkEq "no model orders: first argument is smaller (hand: fallback -1)" r1 (-1)
  checkEq "recorded relation answers the reversed comparison (hand: b > a)" r2 1
  checkEq "transitivity: a < b, b < c gives c > a without model orders (hand)" r3 1
  checkEq "without the recorded relations c vs a falls back to -1 (hand)" r4 (-1)
  -- previous layer, ordering strategies, dummy vs normal
  let (ns, a) ← LayeredM.run previousLayerGraph
  let prev := #[ns[0]!, ns[1]!]
  let u := ns[2]!; let v := ns[3]!; let d := ns[4]!
  checkEq "NODES_AND_EDGES: model order decides (hand: 0 < 1)" (← nodeCmp a (nodeComparator prev .nodesAndEdges) u v) (-1)
  checkEq "NONE: model order decides (hand)" (← nodeCmp a (nodeComparator prev .none) u v) (-1)
  checkEq "PREFER_NODES: model order decides (hand)" (← nodeCmp a (nodeComparator prev .preferNodes) u v) (-1)
  checkEq "PREFER_EDGES: previous layer position decides (hand: s1 after s0)"
    (← nodeCmp a (nodeComparator prev .preferEdges) u v) 1
  checkEq "dummy vs normal: previous layer position decides (hand)" (← nodeCmp a (nodeComparator prev) d v) 1
  checkEq "normal vs dummy: previous layer position decides (hand)" (← nodeCmp a (nodeComparator prev) v d) (-1)
  checkEq "same source port: first argument is smaller (hand)" (← nodeCmp a (nodeComparator prev) d u) (-1)
  checkEq "previous layer unknown: falls through to the no-model-order fallback (hand)"
    (← nodeCmp a (nodeComparator #[]) d v) (-1)
  -- same source node: its port order decides
  let (ns, a) ← LayeredM.run sameSourceGraph
  checkEq "same source node: first source port wins (hand: qa before qb)"
    (← nodeCmp a (nodeComparator #[ns[0]!]) ns[1]! ns[2]!) 1
  checkEq "same source node reversed (hand)" (← nodeCmp a (nodeComparator #[ns[0]!]) ns[2]! ns[1]!) (-1)
  -- helper dummies (feedback long edges)
  let (ns, a) ← LayeredM.run feedbackGraph
  let x := ns[0]!; let n := ns[1]!; let d := ns[2]!
  checkEq "feedback dummy vs its source node: dummy below (hand)" (← nodeCmp a (nodeComparator) d x) 1
  checkEq "feedback dummy vs other node: compared via its source x (hand: 5 > 2)" (← nodeCmp a (nodeComparator) d n) 1
  checkEq "other node vs feedback dummy (hand)" (← nodeCmp a (nodeComparator) n d) (-1)
  let ((rRec, rRel), _) ← LayeredM.run (do
      let (r, c) ← (nodeComparator).compare d n
      let (r2, _) ← c.compare n x
      return (r, r2)) a
  checkEq "recursive comparison result" rRec 1
  checkEq "recursive comparison recorded x > n (hand)" rRel (-1)
  -- LongEdgeOrderingStrategy
  let (ns, a) ← LayeredM.run longEdgeStrategyGraph
  let prevS := #[ns[0]!]
  let d := ns[1]!; let n := ns[2]!
  checkEq "DUMMY_NODE_OVER: dummy before unconnected node (hand: 4 < MAX)"
    (← nodeCmp a (nodeComparator prevS .nodesAndEdges .dummyNodeOver) d n) (-1)
  checkEq "DUMMY_NODE_UNDER: dummy after unconnected node (hand: 4 > MIN)"
    (← nodeCmp a (nodeComparator prevS .nodesAndEdges .dummyNodeUnder) d n) 1
  checkEq "EQUAL: edge order 4 > 0 (hand)" (← nodeCmp a (nodeComparator prevS .nodesAndEdges .equal) d n) 1
  -- group model order
  let (ns, a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let n1 ← addNode g layers[0]! (some 5)
      let n2 ← addNode g layers[0]! (some 3)
      LayeredM.setNodeProp n1 LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID 1
      LayeredM.setNodeProp n2 LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID 2
      return #[n1, n2])
  let enforced : ModelOrderGraphContext :=
    { maxModelOrderNodes := 10, groupOrderStrategy := .enforced, enforcedGroupOrders := #[1, 2] }
  checkEq "enforced group order (hand: 10*1+5 < 10*2+3)" (← nodeCmp a (nodeComparator (graph := enforced)) ns[0]! ns[1]!) (-1)
  checkEq "group order not enforced (hand: 5 > 3)" (← nodeCmp a (nodeComparator) ns[0]! ns[1]!) 1

/-! ## ModelOrderPortComparator -/

/-- Port test graph: layer 0 `s0, s1` (east ports), layer 1 node `n` and the dummies `d1, d2`, layer 2
targets `t1` (model order 7), `t2` (model order 2). Returns the named elements. -/
structure PortFixture where
  s0 : LNodeId
  s1 : LNodeId
  n : LNodeId
  t1 : LNodeId
  t2 : LNodeId
  ports : Array LPortId
  deriving Inhabited

/-- Ports of `n` (indices into `PortFixture.ports`): 0 north, 1 east, 2 south, 3 west (unconnected);
4/5 east outgoing (edge model orders 5/2); 6/7 west outgoing (5/2); 8/9 east incoming from s1/s0;
10/11 west incoming from s1/s0; 12/13 west incoming from s0's ports qb/qa; 14/15 east incoming from
the in-layer dummies d1/d2; 16/17 east outgoing to t1/t2 (edge model orders 1/3, long edge targets
t1/t2); 18/19 east outgoing both to t1 (edge model orders 4/2); 20/21 east outgoing with port model
orders 1/0 (edge model orders 0/5); 22 east incoming only, 23 east outgoing only; 24/25 east
unconnected with model orders 2/1; 26/27 west unconnected with model orders 2/1; 28/29 west incoming
from the dummies d1/d2; 30/31 east unconnected without model order. -/
def portFixture : LayeredM PortFixture := do
  let (g, layers) ← graphWithLayers 3
  setLayerIds layers
  let s0 ← addNode g layers[0]! (some 0)
  let s1 ← addNode g layers[0]! (some 1)
  let d1 ← addNode g layers[1]! none .longEdge
  let d2 ← addNode g layers[1]! none .longEdge
  let n ← addNode g layers[1]! (some 0)
  let t1 ← addNode g layers[2]! (some 7)
  let t2 ← addNode g layers[2]! (some 2)
  let s0e ← addPort s0 .east
  let qa ← addPort s0 .east
  let qb ← addPort s0 .east
  let s1e ← addPort s1 .east
  let d1e ← addPort d1 .east
  let d2e ← addPort d2 .east
  let t1w ← addPort t1 .west
  let t2w ← addPort t2 .west
  let mut ps : Array LPortId := #[]
  for side in #[PortSide.north, .east, .south, .west] do
    ps := ps.push (← addPort n side)
  -- 4..7 outgoing by edge model order
  for (side, mo) in (#[(.east, 5), (.east, 2), (.west, 5), (.west, 2)] : Array (PortSide × Int)) do
    let p ← addPort n side
    let _ ← connect p t1w (some mo)
    ps := ps.push p
  -- 8..11 incoming from the previous layer
  for (side, src) in #[(PortSide.east, s1e), (.east, s0e), (.west, s1e), (.west, s0e)] do
    let p ← addPort n side
    let _ ← connect src p (some 0)
    ps := ps.push p
  -- 12/13 incoming from the same source node
  for src in #[qb, qa] do
    let p ← addPort n .west
    let _ ← connect src p (some 0)
    ps := ps.push p
  -- 14/15 incoming from in-layer long edge dummies
  for src in #[d1e, d2e] do
    let p ← addPort n .east
    let _ ← connect src p (some 0)
    ps := ps.push p
  -- 16/17 long edge targets t1/t2
  for (tgt, tp, mo) in (#[(t1, t1w, 1), (t2, t2w, 3)] : Array (LNodeId × LPortId × Int)) do
    let p ← addPort n .east
    let _ ← connect p tp (some mo)
    setLongEdgeTargetNode p tgt
    ps := ps.push p
  -- 18/19 same target t1
  for mo in (#[4, 2] : Array Int) do
    let p ← addPort n .east
    let _ ← connect p t1w (some mo)
    setLongEdgeTargetNode p t1
    ps := ps.push p
  -- 20/21 port model orders
  for (pmo, emo) in (#[(1, 0), (0, 5)] : Array (Int × Int)) do
    let p ← addPort n .east (some pmo)
    let _ ← connect p t2w (some emo)
    ps := ps.push p
  -- 22 incoming only, 23 outgoing only
  let pin ← addPort n .east
  let _ ← connect s0e pin (some 0)
  let pout ← addPort n .east
  let _ ← connect pout t1w (some 0)
  ps := (ps.push pin).push pout
  -- 24..27 unconnected with model orders
  for (side, mo) in (#[(.east, 2), (.east, 1), (.west, 2), (.west, 1)] : Array (PortSide × Int)) do
    ps := ps.push (← addPort n side (some mo))
  -- 28/29 west incoming from in-layer long edge dummies
  for src in #[d1e, d2e] do
    let p ← addPort n .west
    let _ ← connect src p (some 0)
    ps := ps.push p
  -- 30/31 east unconnected without model order
  ps := ps.push (← addPort n .east)
  ps := ps.push (← addPort n .east)
  return { s0, s1, n, t1, t2, ports := ps }

def portComparatorTests : Suite := suite "layered.intermediate.preserveorder.portComparator" do
  let (f, a) ← LayeredM.run portFixture
  let p := f.ports
  let prev := #[f.s0, f.s1]
  let pc := portComparator prev
  checkEq "sides: NORTH before EAST (hand: ordinals 1 < 2)" (← portCmp a pc p[0]! p[1]!) (-1)
  checkEq "sides: WEST after SOUTH (hand: ordinals 4 > 3)" (← portCmp a pc p[3]! p[2]!) 1
  checkEq "east outgoing: edge model order (hand: 5 > 2)" (← portCmp a pc p[4]! p[5]!) 1
  checkEq "west outgoing: reversed edge model order (hand)" (← portCmp a pc p[6]! p[7]!) (-1)
  checkEq "east incoming: previous layer order (hand: s1 after s0)" (← portCmp a pc p[8]! p[9]!) 1
  checkEq "west incoming: reversed previous layer order (hand)" (← portCmp a pc p[10]! p[11]!) (-1)
  checkEq "incoming sources not in the previous layer: falls through (hand: -reverse = 1)"
    (← portCmp a (portComparator #[]) p[10]! p[11]!) 1
  checkEq "same source node: its port order, west reversed (hand: qa first)" (← portCmp a pc p[12]! p[13]!) (-1)
  checkEq "east incoming from in-layer long edge dummies: reversed layer order (hand)" (← portCmp a pc p[14]! p[15]!) 1
  checkEq "west incoming from in-layer long edge dummies (hand)" (← portCmp a pc p[28]! p[29]!) 1
  checkEq "PREFER_NODES: long edge target model order (hand: 7 > 2)"
    (← portCmp a (portComparator prev .preferNodes) p[16]! p[17]!) 1
  checkEq "NODES_AND_EDGES: edge model order for different targets (hand: 1 < 3)" (← portCmp a pc p[16]! p[17]!) (-1)
  checkEq "target node model order map overrides edge orders (hand: 9 > 3)"
    (← portCmp a (portComparator prev .nodesAndEdges (some #[(f.t1, 9), (f.t2, 3)])) p[16]! p[17]!) 1
  checkEq "same long edge target: edge model order despite the map (hand: 4 > 2)"
    (← portCmp a (portComparator prev .nodesAndEdges (some #[(f.t1, 0)])) p[18]! p[19]!) 1
  checkEq "port model order before edge order (hand: 1 > 0)"
    (← portCmp a (portComparator prev .nodesAndEdges none true) p[20]! p[21]!) 1
  checkEq "without port model order the edge order decides (hand: 0 < 5)" (← portCmp a pc p[20]! p[21]!) (-1)
  checkEq "incoming port after outgoing port (hand)" (← portCmp a pc p[22]! p[23]!) 1
  checkEq "outgoing port before incoming port (hand)" (← portCmp a pc p[23]! p[22]!) (-1)
  checkEq "unconnected east ports: port model order (hand: 2 > 1)" (← portCmp a pc p[24]! p[25]!) 1
  checkEq "unconnected west ports: reversed port model order (hand)" (← portCmp a pc p[26]! p[27]!) (-1)
  checkEq "unconnected ports without model order: -1 (hand)" (← portCmp a pc p[30]! p[31]!) (-1)
  -- transitive relations, including a reversed recording
  let ((r1, r2, r3, r4), _) ← LayeredM.run (do
      let (r1, c) ← pc.compare p[8]! p[9]!
      let (r2, c) ← c.compare p[9]! p[8]!
      let (r3, c) ← c.compare p[10]! p[11]!
      let (r4, _) ← c.compare p[11]! p[10]!
      return (r1, r2, r3, r4)) a
  checkEq "relation: first comparison" r1 1
  checkEq "relation: reversed comparison answered from the relations (hand)" r2 (-1)
  checkEq "relation: west comparison recorded with reverse order" r3 (-1)
  checkEq "relation: reversed west comparison is consistent (hand)" r4 1
  -- group-enforced port model order (offset = number of ports of the node)
  let ((rEnf, rPlain), _) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let m ← addNode g layers[0]! (some 0)
      let g1 ← addPort m .east (some 1)
      let g2 ← addPort m .east (some 2)
      LayeredM.setPortProp g1 LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID 2
      LayeredM.setPortProp g2 LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID 1
      let enforced : ModelOrderGraphContext := { groupOrderStrategy := .enforced, enforcedGroupOrders := #[1, 2] }
      let (r1, _) ← (portComparator #[] .nodesAndEdges none false enforced).compare g1 g2
      let (r2, _) ← (portComparator #[]).compare g1 g2
      return (r1, r2))
  checkEq "enforced port group order (hand: 2*2+1 > 2*1+2)" rEnf 1
  checkEq "port group order not enforced (hand: 1 < 2)" rPlain (-1)

/-! ## Relations (Rust `relation_tests`) -/

/-- The set-based original (`Reference` in the Rust `relation_tests`): `biggerThan`/`smallerThan`
sets per key (keys are `0 … 129`, so the maps are arrays indexed by key). -/
structure RefRelations where
  biggerThan : Array (Std.HashSet Nat) := Array.replicate 130 {}
  smallerThan : Array (Std.HashSet Nat) := Array.replicate 130 {}

/-- `Reference::update_bigger_and_smaller`. -/
def RefRelations.update (r : RefRelations) (bigger smaller : Nat) : RefRelations := Id.run do
  let ⟨bt, st⟩ := r
  let smallerSet := bt[smaller]!
  let biggerSmaller := st[bigger]!
  let mut bt := bt.modify bigger (·.insert smaller)
  let mut st := st.modify smaller (·.insert bigger)
  for verySmall in smallerSet do
    bt := bt.modify bigger (·.insert verySmall)
    st := st.modify verySmall fun x => (x.insert bigger).insertMany biggerSmaller
  for veryBig in biggerSmaller do
    st := st.modify smaller (·.insert veryBig)
    bt := bt.modify veryBig fun x => (x.insert smaller).insertMany smallerSet
  return ⟨bt, st⟩

/-- Whether the dense bit set `bits` (over dense indices, `keyOf` maps them back) equals `ref`. -/
def bitsMatchSet (bits : Nat) (keyOf : Array Nat) (ref : Std.HashSet Nat) : Bool :=
  let members := bitSetMembers bits
  members.size == ref.size && members.all fun j =>
    match keyOf[j]? with
    | some k => ref.contains k
    | none => false

/-- Whether the dense relations equal the reference sets (for every indexed key, like the Rust check
over `dense.indices`). -/
def relationsMatch {κ : Type} [BEq κ] [Hashable κ] (dense : ModelOrderRelations κ) (keyNat : κ → Nat)
    (ref : RefRelations) : Bool := Id.run do
  let mut keyOf : Array Nat := Array.replicate dense.indices.size 0
  for (k, i) in dense.indices.toList do
    keyOf := keyOf.set! i (keyNat k)
  for i in [0:keyOf.size] do
    let k := keyOf[i]!
    if !bitsMatchSet (dense.bigger[i]?.getD 0) keyOf (ref.biggerThan[k]?.getD {}) ||
        !bitsMatchSet (dense.smaller[i]?.getD 0) keyOf (ref.smallerThan[k]?.getD {}) then
      return false
  return true

/-- The pseudo-random pair of the Rust tests (`state * 6364136223846793005 + 1`, wrapping). -/
def lcgPair (state : UInt64) (len : Nat) : UInt64 × Nat × Nat :=
  let state := state * 6364136223846793005 + 1
  (state, (state >>> 32).toNat % len, state.toNat % len)

def relationTests : Suite := suite "layered.intermediate.preserveorder.relations" do
  checkEq "bit set members across words" (bitSetMembers (bitSetBit 3 ||| bitSetBit 64 ||| bitSetBit 129)) #[3, 64, 129]
  -- dense_relations_match_original_sets_through_word_growth_and_cycles
  let mut dense : ModelOrderRelations LNodeId := {}
  let mut original : RefRelations := {}
  let mut state : UInt64 := 17
  let mut allMatch := true
  for step in [0:400] do
    let mut bigger := step + 1
    let mut smaller := step
    if step >= 129 then
      let (s, b, sm) := lcgPair state 130
      state := s
      bigger := b
      smaller := sm
    let (ia, d) := dense.index ⟨bigger⟩
    let (ib, d) := d.index ⟨smaller⟩
    dense := d.record ia ib
    original := original.update bigger smaller
    if !relationsMatch dense (·.idx) original then
      allMatch := false
  check "dense_relations_match_original_sets_through_word_growth_and_cycles" allMatch
  -- port_relations_match_original_sets_through_reversal_growth_and_resets
  let ports : Array LPortId := (Array.range 130).map fun i => ⟨i⟩
  let indexAll : PortComparatorM Unit := do
    for q in ports do
      let _ ← ModelOrderPortComparator.withRelations (·.index q)
  let mut comparator := portComparator #[] .none
  let mut originalPorts : RefRelations := {}
  let mut portState : UInt64 := 29
  let mut portsMatch := true
  let mut resetsClear := true
  for step in [0:400] do
    let mut pa := step + 1
    let mut pb := step
    if step >= 129 then
      let (s, b, sm) := lcgPair portState 130
      portState := s
      pa := b
      pb := sm
    let reverse : Int := if step % 3 == 0 then -1 else 1
    let (c, _) ← LayeredM.run (do
        let ((), c) ← (ModelOrderPortComparator.updateBiggerAndSmaller ports[pa]! ports[pb]! reverse).run comparator
        let ((), c) ← indexAll.run c
        return c)
    comparator := c
    originalPorts := if reverse < 0 then originalPorts.update pb pa else originalPorts.update pa pb
    if !relationsMatch comparator.relations (·.idx) originalPorts then
      portsMatch := false
    let reset : Option ModelOrderPortComparator :=
      match step with
      | 240 => some comparator.clearTransitiveOrdering
      | 280 => some (comparator.resetForPreviousLayer #[])
      | 320 => some (comparator.resetForPreviousLayerSlice #[])
      | 360 => some (comparator.resetForNodeTargetModelOrder none)
      | _ => none
    if let some c := reset then
      let (((), c), _) ← LayeredM.run (indexAll.run c)
      comparator := c
      if !relationsMatch comparator.relations (·.idx) {} then
        resetsClear := false
      originalPorts := {}
  check "port_relations_match_original_sets_through_reversal_growth_and_resets: relations" portsMatch
  check "port_relations_match_original_sets_through_reversal_growth_and_resets: resets forget relations" resetsClear

/-! ## SortByInputModelProcessor -/

/-- Rust `assert_node_order(orders)`: four nodes in one layer end up sorted by model order. -/
def nodeOrderSorted (orders : Array Int) : IO Bool := do
  let ((layer, inserted), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let mut inserted := #[]
      for o in orders do
        inserted := inserted.push (← addNode g layers[0]! (some o))
      runSorter g
      return (layers[0]!, inserted))
  let expected := stableSortByKey inserted fun n => (a.node n).internal.modelOrder.getD 2147483647
  return (a.layer layer).nodes == expected

/-- Rust `assert_port_order(edge_orders, constraints)`: the ports of the source node. Returns the
sorted ports and the ports in insertion order. -/
def portOrderAfterSort (edgeOrders : Array Int) (constraints : PortConstraints) : IO (Array LPortId × Array LPortId) := do
  let ((source, ports), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 2
      let source ← addNode g layers[0]! (some 0)
      LayeredM.setNodeProp source LayeredOptions.PORT_CONSTRAINTS constraints
      let mut ports := #[]
      for _ in [0:3] do
        ports := ports.push (← addPort source .east)
      for i in [0:3] do
        let t ← addNode g layers[1]! (some (i : Int))
        let _ ← connect ports[i]! (← addPort t .west) (some edgeOrders[i]!)
      runSorter g
      return (source, ports))
  return ((a.node source).ports, ports)

/-- Expected order of `assert_port_order`: by the first outgoing edge's model order. -/
def expectedPortOrder (ports : Array LPortId) (edgeOrders : Array Int) : Array LPortId :=
  let indexed := (Array.range ports.size).map fun i => (ports[i]!, edgeOrders[i]!)
  (stableSortByKey indexed (·.2)).map (·.1)

def sortProcessorRustTests : Suite := suite "layered.intermediate.sortByInputModelProcessor.rust" do
  -- sort_by_input_model_processor_test.rs
  let ((layer, n0, n1, n2), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 1
      let n2 ← addNode g layers[0]! (some 2)
      let n0 ← addNode g layers[0]! (some 0)
      let n1 ← addNode g layers[0]! (some 1)
      runSorter g
      return (layers[0]!, n0, n1, n2))
  checkEq "sort_by_input_model_processor_sorts_nodes_by_model_order" (a.layer layer).nodes #[n0, n1, n2]
  let ((source, pLow, pHigh), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 2
      let source ← addNode g layers[0]! (some 0)
      LayeredM.setNodeProp source LayeredOptions.PORT_CONSTRAINTS PortConstraints.free
      let pHigh ← addPort source .east
      let pLow ← addPort source .east
      let tLow ← addNode g layers[1]! (some 0)
      let tHigh ← addNode g layers[1]! (some 1)
      let tLowWest ← addPort tLow .west
      let tHighWest ← addPort tHigh .west
      let _ ← connect pHigh tHighWest (some 10)
      let _ ← connect pLow tLowWest (some 1)
      runSorter g
      return (source, pLow, pHigh))
  checkEq "sort_by_input_model_processor_sorts_ports_by_edge_model_order" (a.node source).ports #[pLow, pHigh]
  -- concrete_sort_by_input_model_test.rs
  let perms : Array (String × Array Int) := #[
    ("0123", #[0, 1, 2, 3]), ("0132", #[0, 1, 3, 2]), ("0213", #[0, 2, 1, 3]), ("0231", #[0, 2, 3, 1]),
    ("0312", #[0, 3, 1, 2]), ("0321", #[0, 3, 2, 1]), ("1023", #[1, 0, 2, 3]), ("1203", #[1, 2, 0, 3]),
    ("1230", #[1, 2, 3, 0]), ("1302", #[1, 3, 0, 2]), ("2013", #[2, 0, 1, 3]), ("2301", #[2, 3, 0, 1]),
    ("3012", #[3, 0, 1, 2]), ("3210", #[3, 2, 1, 0])]
  for (name, orders) in perms do
    check s!"sort_nodes_perm_{name}" (← nodeOrderSorted orders)
  for (name, orders) in #[("ascending", #[1, 2, 3]), ("descending", #[9, 3, 1]), ("mixed", #[5, 1, 3])] do
    let (sorted, ports) ← portOrderAfterSort orders .free
    checkEq s!"sort_ports_by_edge_model_order_{name}" sorted (expectedPortOrder ports orders)
  let (sorted, ports) ← portOrderAfterSort #[9, 1, 5] .fixedOrder
  checkEq "sort_ports_keeps_order_when_fixed_order" sorted ports
  let (sorted, ports) ← portOrderAfterSort #[9, 1, 5] .fixedPos
  checkEq "sort_ports_keeps_order_when_fixed_pos" sorted ports

/-- Two layers: layer 0 holds `b` (model order 1, east port `b1`) and `a` (model order 0, east ports
`a1`, `a2`); layer 1 holds `y` (3, west port `yw`) and `x` (2, west ports `xw1`, `xw2`). Edges
`a1 → yw` (1), `a2 → xw1` (0), `b1 → xw2` (2). -/
def twoLayerGraph (strategy : OrderingStrategy := .nodesAndEdges) :
    LayeredM (LGraphId × Array LayerId × Array LNodeId × Array LPortId) := do
  let (g, layers) ← graphWithLayers 2 strategy
  let b ← addNode g layers[0]! (some 1)
  let na ← addNode g layers[0]! (some 0)
  let y ← addNode g layers[1]! (some 3)
  let x ← addNode g layers[1]! (some 2)
  let b1 ← addPort b .east
  let a1 ← addPort na .east
  let a2 ← addPort na .east
  let yw ← addPort y .west
  let xw1 ← addPort x .west
  let xw2 ← addPort x .west
  let _ ← connect a1 yw (some 1)
  let _ ← connect a2 xw1 (some 0)
  let _ ← connect b1 xw2 (some 2)
  return (g, layers, #[na, b, x, y], #[a1, a2, b1, xw1, xw2, yw])

def sortProcessorTests : Suite := suite "layered.intermediate.sortByInputModelProcessor" do
  checkEq "registered for SORT_BY_INPUT_ORDER_OF_MODEL" (← IntermediateProcessorStrategy.isAvailable .sortByInputOrderOfModel) true
  checkEq "registered processor name" (← IntermediateProcessorStrategy.create .sortByInputOrderOfModel).name
    "SortByInputModelProcessor"
  let ((_, layers, ns, ps), a) ← LayeredM.run (do
      let r ← twoLayerGraph
      runSorter r.1
      return r)
  let na := ns[0]!; let b := ns[1]!; let x := ns[2]!; let y := ns[3]!
  let a1 := ps[0]!; let a2 := ps[1]!; let b1 := ps[2]!; let xw1 := ps[3]!; let xw2 := ps[4]!
  checkEq "two layers: layer 0 by model order (hand)" (a.layer layers[0]!).nodes #[na, b]
  checkEq "two layers: layer 1 by model order (hand)" (a.layer layers[1]!).nodes #[x, y]
  checkEq "two layers: east ports by target model order (hand: x(0) before y(1))" (a.node na).ports #[a2, a1]
  checkEq "two layers: west ports reversed by previous layer order (hand)" (a.node x).ports #[xw2, xw1]
  checkEq "layer ids are set to the layer indices" ((a.layer layers[0]!).id, (a.layer layers[1]!).id) ((0 : Int), (1 : Int))
  checkEq "LONG_EDGE_TARGET_NODE set on a1" (a.port a1).internal.longEdgeTargetNode (some y)
  checkEq "LONG_EDGE_TARGET_NODE set on b1" (a.port b1).internal.longEdgeTargetNode (some x)
  check "port sides cached after sorting" (a.node na).portSidesCached
  let (cached, _) ← LayeredM.run (SortByInputModelProcessor.getTargetNodeModelOrder na) a
  checkEq "TARGET_NODE_MODEL_ORDER cached on the node (hand: y ↦ 1, x ↦ 0)" cached (some #[(y, 1), (x, 0)])
  -- PREFER_EDGES: layer 1 follows the previous layer instead of the model order
  let ((_, layers, ns), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 2 .preferEdges
      let s0 ← addNode g layers[0]! (some 0)
      let s1 ← addNode g layers[0]! (some 1)
      let u ← addNode g layers[1]! (some 0)
      let v ← addNode g layers[1]! (some 1)
      let _ ← connect (← addPort s1 .east) (← addPort u .west) (some 0)
      let _ ← connect (← addPort s0 .east) (← addPort v .west) (some 1)
      runSorter g
      return (g, layers, #[s0, s1, u, v]))
  checkEq "PREFER_EDGES: layer 0 by model order (hand)" (a.layer layers[0]!).nodes #[ns[0]!, ns[1]!]
  checkEq "PREFER_EDGES: layer 1 by previous layer (hand: v from s0 first)" (a.layer layers[1]!).nodes #[ns[3]!, ns[2]!]
  -- getTargetNode / longEdgeTargetNodePreprocessing
  let ((s, t, w, sp), a) ← LayeredM.run (do
      let (g, layers) ← graphWithLayers 4
      let s ← addNode g layers[0]! (some 0)
      let d1 ← addNode g layers[1]! none .longEdge
      let d2 ← addNode g layers[2]! none .longEdge
      let d3 ← addNode g layers[1]! none .longEdge
      let t ← addNode g layers[3]! (some 1)
      let w ← addNode g layers[1]! (some 2)
      let tw ← addPort t .west
      let p ← addPort s .east
      let q ← addPort s .east
      let r ← addPort s .east
      let u ← addPort s .east
      let deadEnd ← addPort s .east
      let _ ← connect p (← addPort d1 .west) (some 5)
      let _ ← connect (← addPort d1 .east) (← addPort d2 .west) (some 5)
      let _ ← connect (← addPort d2 .east) tw (some 5)
      LayeredM.modifyNode d2 fun x => { x with internal.longEdgeTarget := some tw }
      let _ ← connect q tw (some 3)
      let re ← connect r tw (some 1)
      LayeredM.modifyEdge re fun x => { x with internal.reversed := true }
      let _ ← connect u (← addPort w .west) (some 4)
      let _ ← connect deadEnd (← addPort d3 .west) (some 0)
      return (s, t, w, #[p, q, r, u, deadEnd]))
  let ((tp, td), _) ← LayeredM.run (do
      return (← SortByInputModelProcessor.getTargetNode sp[0]!, ← SortByInputModelProcessor.getTargetNode sp[4]!)) a
  checkEq "getTargetNode through dummies to LONG_EDGE_TARGET's node (hand)" tp (some t)
  checkEq "getTargetNode: dummy without outgoing edge gives none (hand)" td none
  let ((m1, m2, targets), _) ← LayeredM.run (do
      let m1 ← SortByInputModelProcessor.longEdgeTargetNodePreprocessing s
      -- change an edge model order: the cached map must be returned unchanged
      let e := (← LayeredM.getPort sp[1]!).outgoingEdges[0]!
      LayeredM.modifyEdge e fun x => { x with internal.modelOrder := some 0 }
      let m2 ← SortByInputModelProcessor.longEdgeTargetNodePreprocessing s
      let mut targets := #[]
      for q in sp do
        targets := targets.push (← LayeredM.getPort q).internal.longEdgeTargetNode
      return (m1, m2, targets)) a
  checkEq "long edge target map: minimum non-reversed order per target (hand: t ↦ 3, w ↦ 4)" m1
    #[(t, 3), (w, 4)]
  checkEq "long edge target map is cached on the node" m2 m1
  checkEq "LONG_EDGE_TARGET_NODE on every port with a target (hand)" targets #[some t, some t, some t, some w, none]
  -- Java `Math.min(edge.getProperty(MODEL_ORDER), previousOrder)`: a non-reversed first edge without a
  -- model order is the unboxing `NullPointerException` (elk-rs used `Integer.MAX_VALUE`)
  let npe ← try
      let _ ← LayeredM.run (do
        let (g, layers) ← graphWithLayers 2
        let s ← addNode g layers[0]! (some 0)
        let w ← addNode g layers[1]! (some 1)
        let _ ← connect (← addPort s .east) (← addPort w .west) none
        SortByInputModelProcessor.longEdgeTargetNodePreprocessing s)
      pure "no exception"
    catch e => pure (toString e)
  checkEq "edge without MODEL_ORDER: Java's unboxing NullPointerException" npe edgeModelOrderNullError

def suites : Array Suite :=
  #[cmGroupTests, nodeComparatorTests, portComparatorTests, relationTests, sortProcessorRustTests, sortProcessorTests]

end Tests.Layered.IntermediatePreserveOrder
