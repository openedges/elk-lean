import Tests.Framework
import Tests.Layered.P3Counting
import Elk.Alg.Layered
import Elk.Alg.Layered.P3Order.LayerSweep
/-!
Tests of the layer sweep crossing minimisation of `p3order` (`LayerSweepCrossingMinimizer`,
`GraphInfoHolder`, `LayerSweepTypeDecider`) and of the greedy switch processors (the minimiser with
the greedy switch heuristics), ported from elk-rs
`tests/p3_order/{layer_sweep_crossing_minimizer_test,layer_sweep_type_decider_test,basic_crossing_minimization_test}.rs`
and `tests/intermediate/greedyswitch/{greedy_switch_processor_test,layer_sweep_hierarchical_two_sided_greedy_switch_test}.rs`
(check names are the Rust test names). The graph builders follow the per-file Rust helpers; nested
graphs of `layer_sweep_crossing_minimizer_test.rs` clone the parent's `RANDOM` (shared state in
elk-rs), modelled with `LGraphInternals.randomOwner`.
-/
namespace Tests.Layered.P3LayerSweep

open Tests Elk.Graph Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open Elk.Alg.Layered.P3Order Elk.Alg.Layered.P3Order.Counting
open Tests.Layered.P3Counting (Cfg makeLayer makeLayers addNode addNodes addPort addPorts connect
  eastWestEdgeFromTo eastWestEdgeFromPort eastWestEdgeFromNode addInLayerEdge selfLoopOn
  setFixedOrderConstraint addGraphProperty addNorthSouthEdge nodeArray runL)
open LayeredM

/-! ## Builders -/

/-- Layout unit on new nodes, `FIXED_SIDE` on new ports, `NON_FREE_PORTS` with fixed orders. -/
def cfg : Cfg := { selfUnit := true, fixSide := true, graphProps := true }

/-- `mock_random(next_boolean)`: `Random(0)` with a fixed `nextBoolean` and the double sequence
`0.01, 0.02, …`. -/
def mockRandom (nextBoolean : Bool) : Random :=
  ((Random.ofInt 0).setMockNextBoolean nextBoolean).setMockDoubleSequence 0.01 0.01

/-- `set_property(RANDOM, random)` (an own, unshared state). -/
def setRandom (g : LGraphId) (r : Random) : LayeredM Unit :=
  modifyGraph g fun x => { x with internal := { x.internal with random := some r, randomOwner := none } }

/-- `new_graph()`: `RANDOM`, `EDGE_ROUTING = ORTHOGONAL`, `HIERARCHY_HANDLING = INCLUDE_CHILDREN`. -/
def newGraph (random : Random := mockRandom true) : LayeredM LGraphId := do
  let g ← createGraph
  setRandom g random
  setGraphProp g LayeredOptions.EDGE_ROUTING EdgeRouting.orthogonal
  setGraphProp g LayeredOptions.HIERARCHY_HANDLING HierarchyHandling.includeChildren
  return g

/-- `nested_graph(node)` of `layer_sweep_crossing_minimizer_test.rs`: the nested graph shares the
parent graph's `RANDOM`. -/
def nestedGraphShared (node : LNodeId) : LayeredM LGraphId := do
  if let some g := (← getNode node).nestedGraph then return g
  let nested ← createGraph
  setGraphProp nested LayeredOptions.EDGE_ROUTING EdgeRouting.orthogonal
  setGraphProp nested LayeredOptions.HIERARCHY_HANDLING HierarchyHandling.includeChildren
  if let some parentGraph ← nodeGraph node then
    if (← graphRandom? parentGraph).isSome then
      let holder ← randomHolder parentGraph
      modifyGraph nested fun x => { x with internal := { x.internal with random := none, randomOwner := some holder } }
  modifyGraph nested fun x => { x with parentNode := some node }
  modifyNode node fun x => { x with nestedGraph := some nested }
  return nested

/-- `nested_graph(node)` with an own `RANDOM` (`set_up_graph`/`new_graph` of the other test files). -/
def nestedGraphOwn (node : LNodeId) (random : Random) : LayeredM LGraphId := do
  if let some g := (← getNode node).nestedGraph then return g
  let nested ← newGraph random
  modifyGraph nested fun x => { x with parentNode := some node }
  modifyNode node fun x => { x with nestedGraph := some nested }
  return nested

/-- `add_external_port_dummy_node_to_layer(layer, port)`. -/
def addExternalPortDummy (layer : LayerId) (port : LPortId) : LayeredM LNodeId := do
  let g := (← getLayer layer).owner
  let node ← addNode cfg g layer
  let side := (← getPort port).side
  modifyNode node fun x => { x with
    type := .externalPort, internal := { x.internal with origin := some (.lPort port), extPortSide := side } }
  modifyPort port fun x => { x with internal := { x.internal with portDummy := some node, insideConnections := true } }
  modifyGraph g fun x => { x with internal := { x.internal with
    graphProperties := x.internal.graphProperties.insert .externalPorts } }
  return node

/-- `add_external_port_dummies_to_layer(layer, ports)`: east ports in order, others reversed. -/
def addExternalPortDummies (layer : LayerId) (ports : Array LPortId) : LayeredM (Array LNodeId) := do
  let some first := ports[0]? | return #[]
  let side := (← getPort first).side
  let mut nodes := #[]
  for i in [0:ports.size] do
    let portIndex := if side == .east then i else ports.size - 1 - i
    nodes := nodes.push (← addExternalPortDummy layer ports[portIndex]!)
  return nodes

/-- `set_up_ids(graph)`: per graph (stack order) layer, node and port ids. -/
def setUpIds (graph : LGraphId) : LayeredM Unit := do
  let mut graphs := #[graph]
  while !graphs.isEmpty do
    let current := graphs.back!
    graphs := graphs.pop
    let mut portId : Int := 0
    let layers := (← getGraph current).layers
    for h : layerId in [0:layers.size] do
      let layer := layers[layerId]
      modifyLayer layer fun x => { x with id := layerId }
      let nodes := (← getLayer layer).nodes
      for h2 : nodeId in [0:nodes.size] do
        let node := nodes[nodeId]
        modifyNode node fun x => { x with id := nodeId }
        if let some nested := (← getNode node).nestedGraph then graphs := graphs.push nested
        for port in (← getNode node).ports do
          let id := portId
          modifyPort port fun x => { x with id := id }
          portId := portId + 1

/-- Runs the minimiser of a type on a graph. -/
def runMinimizer (graph : LGraphId) (crossMinType : CrossMinType) : LayeredM Unit := do
  let monitor ← ProgressMonitor.basic
  LayerSweepCrossingMinimizer.process crossMinType graph monitor

/-- `run_crossmin(graph, type)`: ids, `THOROUGHNESS = 1` for the barycenter type, then the minimiser. -/
def runCrossmin (graph : LGraphId) (crossMinType : CrossMinType) : LayeredM Unit := do
  setUpIds graph
  if crossMinType == .barycenter then setGraphProp graph LayeredOptions.THOROUGHNESS (1 : Int)
  runMinimizer graph crossMinType

/-- `clone_layer_nodes(layer)`. -/
def layerNodes (layer : LayerId) : LayeredM (Array LNodeId) := do return (← getLayer layer).nodes

/-- The ports of a node. -/
def portsOf (n : LNodeId) : LayeredM (Array LPortId) := do return (← getNode n).ports

/-- `node_index(nodes, needle)` (as `Int`). -/
def idx {α : Type} [BEq α] (xs : Array α) (x : α) : Int := ((xs.findIdx? (· == x)).getD 999 : Nat)

/-- `signum(a - b)`. -/
def sgn (a b : Int) : Int := if a > b then 1 else if a < b then -1 else 0

/-- `count_all_crossings(graph)`: a fresh `AllCrossingsCounter` on the graph's node order (not
initialised, as in Rust). -/
def countAllCrossings (graph : LGraphId) : LayeredM Int := do
  let order ← nodeArray graph
  let counter ← AllCrossingsCounter.new graph order
  counter.countAllCrossings order

/-- `set_hierarchical_sweepiness_on_all_graphs(graph, value)` / `set_on_all_graphs`. -/
partial def setSweepinessOnAllGraphs (graph : LGraphId) (value : Float) : LayeredM Unit := do
  setGraphProp graph LayeredOptions.CROSSING_MINIMIZATION_HIERARCHICAL_SWEEPINESS value
  for layer in (← getGraph graph).layers do
    for node in (← getLayer layer).nodes do
      if let some nested := (← getNode node).nestedGraph then setSweepinessOnAllGraphs nested value

/-- `make_nested_two_node_graph_with_eastern_ports(left_outer_node, left_outer_ports)`. -/
def makeNestedTwoNodeGraphWithEasternPorts (leftOuterNode : LNodeId) (leftOuterPorts : Array LPortId) :
    LayeredM LGraphId := do
  let inner ← nestedGraphShared leftOuterNode
  let nodesLayer ← makeLayer inner
  let dummyLayer ← makeLayer inner
  let n0 ← addNode cfg inner nodesLayer
  let n1 ← addNode cfg inner nodesLayer
  let dummies ← addExternalPortDummies dummyLayer leftOuterPorts
  eastWestEdgeFromTo cfg n0 dummies[0]!
  eastWestEdgeFromTo cfg n1 dummies[1]!
  return inner

/-- `make_nested_two_node_graph_with_western_ports(right_outer_node, right_outer_ports)`. -/
def makeNestedTwoNodeGraphWithWesternPorts (rightOuterNode : LNodeId) (rightOuterPorts : Array LPortId) :
    LayeredM LGraphId := do
  let inner ← nestedGraphShared rightOuterNode
  let dummyLayer ← makeLayer inner
  let nodesLayer ← makeLayer inner
  let dummies ← addExternalPortDummies dummyLayer rightOuterPorts
  let n0 ← addNode cfg inner nodesLayer
  let n1 ← addNode cfg inner nodesLayer
  eastWestEdgeFromTo cfg dummies[0]! n0
  eastWestEdgeFromTo cfg dummies[1]! n1
  return inner

/-! ## `layer_sweep_crossing_minimizer_test.rs` -/

/-- `given_no_node_shouldnt_crash_*`. -/
def tNoNode (t : CrossMinType) : LayeredM Bool := do
  let g ← newGraph
  runCrossmin g t
  return true

/-- `given_one_node_shouldnt_crash_*`. -/
def tOneNode (t : CrossMinType) : LayeredM Bool := do
  let g ← newGraph
  let l ← makeLayer g
  let _ ← addNode cfg g l
  runCrossmin g t
  return true

/-- The simple cross graph `n1→n4, n2→n3`. -/
def simpleCross : LayeredM (LGraphId × Array LNodeId) := do
  let g ← newGraph
  let left ← makeLayer g
  let right ← makeLayer g
  let n1 ← addNode cfg g left
  let n2 ← addNode cfg g left
  let n3 ← addNode cfg g right
  let n4 ← addNode cfg g right
  eastWestEdgeFromTo cfg n1 n4
  eastWestEdgeFromTo cfg n2 n3
  return (g, #[n1, n2, n3, n4])

/-- `simple_cross_graph_runs_and_keeps_layer_structure`. -/
def tSimpleCrossBarycenter : LayeredM Bool := do
  let (g, n) ← simpleCross
  runCrossmin g .barycenter
  let gr ← getGraph g
  let left ← layerNodes gr.layers[0]!
  let right ← layerNodes gr.layers[1]!
  return gr.layers.size == 2 && left.size == 2 && right == #[n[3]!, n[2]!]

/-- `simple_cross_graph_one_sided_switch_reorders_right_layer`. -/
def tSimpleCrossOneSided : LayeredM Bool := do
  let (g, n) ← simpleCross
  runCrossmin g .oneSidedGreedySwitch
  let gr ← getGraph g
  let left ← layerNodes gr.layers[0]!
  let right ← layerNodes gr.layers[1]!
  return sgn (idx left n[0]!) (idx left n[1]!) == sgn (idx right n[3]!) (idx right n[2]!)

/-- `assert_single_hierarchical_cross_removed(type)`. -/
def tSingleHierarchicalCross (t : CrossMinType) : LayeredM Bool := do
  let g ← newGraph
  let outerLayer ← makeLayer g
  let outer ← addNode cfg g outerLayer
  let inner ← nestedGraphShared outer
  let left ← makeLayer inner
  let right ← makeLayer inner
  let l0 ← addNode cfg inner left
  let l1 ← addNode cfg inner left
  let r0 ← addNode cfg inner right
  let r1 ← addNode cfg inner right
  eastWestEdgeFromTo cfg l0 r1
  eastWestEdgeFromTo cfg l1 r0
  runCrossmin g t
  let leftNodes ← layerNodes left
  let rightNodes ← layerNodes right
  return sgn (idx leftNodes l0) (idx leftNodes l1) == sgn (idx rightNodes r1) (idx rightNodes r0)

/-- Two outer nodes with two east and two west ports connected in parallel. -/
def twoOuterNodes (random : Random := mockRandom true) :
    LayeredM (LGraphId × LNodeId × LNodeId × Array LPortId × Array LPortId) := do
  let g ← newGraph random
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let leftOuter ← addNode cfg g leftLayer
  let rightOuter ← addNode cfg g rightLayer
  let leftPorts ← addPorts cfg leftOuter 2 .east
  let rightPorts ← addPorts cfg rightOuter 2 .west
  connect leftPorts[0]! rightPorts[0]!
  connect leftPorts[1]! rightPorts[1]!
  return (g, leftOuter, rightOuter, leftPorts, rightPorts)

/-- `assert_simple_hierarchical_cross_results_in_no_crossing(type)`. -/
def tSimpleHierarchicalCross (t : CrossMinType) : LayeredM Bool := do
  let (g, leftOuter, rightOuter, leftPorts, rightPorts) ← twoOuterNodes
  let _ ← makeNestedTwoNodeGraphWithEasternPorts leftOuter leftPorts
  let rightInner ← makeNestedTwoNodeGraphWithWesternPorts rightOuter rightPorts
  let innerLayers := (← getGraph rightInner).layers
  let dummies ← layerNodes innerLayers[0]!
  let normals ← layerNodes innerLayers[1]!
  setSweepinessOnAllGraphs g 0.1
  runCrossmin g t
  let actualDummies ← layerNodes innerLayers[0]!
  let actualNormals ← layerNodes innerLayers[1]!
  let actualPorts ← portsOf rightOuter
  if t == .barycenter then
    return actualDummies == #[dummies[1]!, dummies[0]!] && actualNormals == #[normals[1]!, normals[0]!]
      && actualPorts == #[rightPorts[1]!, rightPorts[0]!]
  else
    return sgn (idx actualDummies dummies[0]!) (idx actualDummies dummies[1]!)
      == sgn (idx actualNormals normals[0]!) (idx actualNormals normals[1]!)

/-- `assert_simple_hierarchical_cross_sweeping_right_to_left_results_in_no_crossing(type)`. -/
def tSimpleHierarchicalCrossRightToLeft (t : CrossMinType) : LayeredM Bool := do
  let (g, leftOuter, rightOuter, leftPorts, rightPorts) ← twoOuterNodes (mockRandom false)
  let leftInner ← makeNestedTwoNodeGraphWithEasternPorts leftOuter leftPorts
  let _ ← makeNestedTwoNodeGraphWithWesternPorts rightOuter rightPorts
  let layer0 := (← getGraph leftInner).layers[0]!
  let innerNodes ← layerNodes layer0
  runCrossmin g t
  let actualPorts ← portsOf leftOuter
  let actualInner ← layerNodes layer0
  if t == .oneSidedGreedySwitch then
    return actualPorts == #[leftPorts[1]!, leftPorts[0]!] && actualInner == #[innerNodes[1]!, innerNodes[0]!]
  else
    return actualPorts.size == 2 && actualInner.size == 2

/-- `assert_backward_sweep_not_taken_still_corrects_port_order(type, left_edges_per_middle)`. -/
def tBackwardSweepNotTaken (t : CrossMinType) (leftEdgesPerMiddle : Nat) : LayeredM Bool := do
  let g ← newGraph
  let layers ← makeLayers g 3
  let leftNode ← addNode cfg g layers[0]!
  let middle ← addNodes cfg g layers[1]! 3
  let right ← addNodes cfg g layers[2]! 2
  eastWestEdgeFromTo cfg middle[0]! right[0]!
  eastWestEdgeFromTo cfg middle[1]! right[0]!
  eastWestEdgeFromTo cfg middle[2]! right[1]!
  eastWestEdgeFromTo cfg middle[2]! right[1]!
  for _ in [0:leftEdgesPerMiddle] do
    eastWestEdgeFromTo cfg leftNode middle[0]!
    eastWestEdgeFromTo cfg leftNode middle[1]!
  setFixedOrderConstraint cfg right[1]!
  setFixedOrderConstraint cfg right[0]!
  setFixedOrderConstraint cfg leftNode
  let bottomPorts ← portsOf middle[2]!
  runCrossmin g t
  return (← portsOf middle[2]!) == #[bottomPorts[1]!, bottomPorts[0]!]

/-- `assert_resolves_in_layer_port_order_crossings_after_switch(type)`. -/
def tInLayerPortOrderAfterSwitch (t : CrossMinType) : LayeredM Bool := do
  let g ← newGraph
  let leftLayer ← makeLayer g
  let middleLayer ← makeLayer g
  let left ← addNodes cfg g leftLayer 2
  let middle ← addNodes cfg g middleLayer 2
  eastWestEdgeFromTo cfg left[0]! middle[1]!
  addInLayerEdge cfg middle[1]! middle[0]! .west
  eastWestEdgeFromTo cfg left[1]! middle[0]!
  let topPorts ← portsOf middle[0]!
  runCrossmin g t
  if t == .barycenter then
    return (← layerNodes middleLayer) == #[middle[1]!, middle[0]!] && (← portsOf middle[0]!) == #[topPorts[1]!, topPorts[0]!]
  return true

/-- `assert_compound_graph_forward_sweep_case_removes_crossing(type)`. -/
def tCompoundForwardSweep (t : CrossMinType) : LayeredM Bool := do
  let g ← newGraph
  let outerLayer ← makeLayer g
  let outer ← addNode cfg g outerLayer
  let inner ← nestedGraphShared outer
  let leftLayer ← makeLayer inner
  let rightLayer ← makeLayer inner
  let leftInner ← addNode cfg inner leftLayer
  setFixedOrderConstraint cfg leftInner
  let r0 ← addNode cfg inner rightLayer
  let r1 ← addNode cfg inner rightLayer
  eastWestEdgeFromTo cfg leftInner r1
  eastWestEdgeFromTo cfg leftInner r0
  let expectedPorts ← portsOf leftInner
  runCrossmin g t
  return (← portsOf leftInner) == expectedPorts && (← layerNodes rightLayer) == #[r1, r0]

/-- `assert_graph_without_nesting_improves_on_backward_sweep(type)`. -/
def tImprovesOnBackwardSweep (t : CrossMinType) : LayeredM Bool := do
  let g ← newGraph (mockRandom false)
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let leftTop ← addNode cfg g leftLayer
  let leftBottom ← addNode cfg g leftLayer
  let right ← addNode cfg g rightLayer
  setFixedOrderConstraint cfg right
  eastWestEdgeFromTo cfg leftTop right
  eastWestEdgeFromTo cfg leftBottom right
  runCrossmin g t
  return (← layerNodes leftLayer) == #[leftBottom, leftTop]

/-- `assert_simple_graph_not_reordered_randomly_on_backward_sweep(type)`. -/
def tNotReorderedRandomly (t : CrossMinType) : LayeredM Bool := do
  let g ← newGraph
  let layers ← makeLayers g 2
  let l0 ← addNode cfg g layers[0]!
  let l1 ← addNode cfg g layers[0]!
  let r0 ← addNode cfg g layers[1]!
  let r1 ← addNode cfg g layers[1]!
  let r2 ← addNode cfg g layers[1]!
  eastWestEdgeFromTo cfg l0 r0
  eastWestEdgeFromTo cfg l0 r2
  eastWestEdgeFromTo cfg l1 r1
  runCrossmin g t
  let actualRight ← layerNodes layers[1]!
  let rightOk := if t == .oneSidedGreedySwitch then actualRight == #[r0, r2, r1]
    else idx actualRight r2 < idx actualRight r1
  return rightOk && (← layerNodes layers[0]!) == #[l0, l1]

/-- `assert_graph_which_worsens_on_backward_takes_forward_result(type)`. -/
def tWorsensOnBackward (t : CrossMinType) : LayeredM Bool := do
  let g ← newGraph
  let layers ← makeLayers g 3
  let left ← addNode cfg g layers[0]!
  setFixedOrderConstraint cfg left
  let m0 ← addNode cfg g layers[1]!
  let m1 ← addNode cfg g layers[1]!
  let right ← addNode cfg g layers[2]!
  setFixedOrderConstraint cfg right
  eastWestEdgeFromTo cfg left m1
  eastWestEdgeFromTo cfg left m1
  eastWestEdgeFromTo cfg left m0
  eastWestEdgeFromTo cfg left m0
  eastWestEdgeFromTo cfg m1 right
  eastWestEdgeFromTo cfg m0 right
  runCrossmin g t
  return (← layerNodes layers[1]!) == #[m1, m0]

/-- `assert_cross_between_compound_and_non_compound_nodes_removed(type)`. -/
def tCrossCompoundNonCompound (t : CrossMinType) : LayeredM Bool := do
  let g ← newGraph
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let leftOuter ← addNode cfg g leftLayer
  let right ← addNodes cfg g rightLayer 2
  let leftPorts ← addPorts cfg leftOuter 2 .east
  eastWestEdgeFromPort cfg leftPorts[0]! right[1]!
  eastWestEdgeFromPort cfg leftPorts[1]! right[0]!
  let _ ← makeNestedTwoNodeGraphWithEasternPorts leftOuter leftPorts
  runCrossmin g t
  let rightOrder ← layerNodes rightLayer
  if t == .barycenter then
    return rightOrder == #[right[1]!, right[0]!]
  let ports ← portsOf leftOuter
  return sgn (idx ports leftPorts[0]!) (idx ports leftPorts[1]!) == sgn (idx rightOrder right[1]!) (idx rightOrder right[0]!)

/-- `assert_cross_in_first_level_compound_node_removed(type)`. -/
def tCrossInFirstLevelCompound (t : CrossMinType) : LayeredM Bool := do
  let g ← newGraph
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let leftOuter ← addNode cfg g leftLayer
  let right ← addNodes cfg g rightLayer 2
  let leftPorts ← addPorts cfg leftOuter 2 .east
  eastWestEdgeFromPort cfg leftPorts[0]! right[0]!
  eastWestEdgeFromPort cfg leftPorts[1]! right[1]!
  let inner ← nestedGraphShared leftOuter
  let innerLeft ← makeLayer inner
  let innerRight ← makeLayer inner
  let innerDummy ← makeLayer inner
  let il ← addNodes cfg inner innerLeft 2
  let ir ← addNodes cfg inner innerRight 2
  let dummies ← addExternalPortDummies innerDummy leftPorts
  eastWestEdgeFromTo cfg ir[0]! dummies[0]!
  eastWestEdgeFromTo cfg ir[1]! dummies[1]!
  eastWestEdgeFromTo cfg il[0]! ir[1]!
  eastWestEdgeFromTo cfg il[1]! ir[0]!
  runCrossmin g t
  let rightOrder ← layerNodes rightLayer
  if t == .barycenter then
    return rightOrder == #[right[1]!, right[0]!]
  let ports ← portsOf leftOuter
  return sgn (idx ports leftPorts[0]!) (idx ports leftPorts[1]!) == sgn (idx rightOrder right[0]!) (idx rightOrder right[1]!)

/-- `assert_graph_with_normal_and_hierarchical_cross_removed(type, with_unused_port)`. -/
def tNormalAndHierarchicalCross (t : CrossMinType) (withUnusedPort : Bool) : LayeredM Bool := do
  let g ← newGraph
  let layers ← makeLayers g 2
  let leftOuter ← addNode cfg g layers[0]!
  let rightTop ← addNode cfg g layers[1]!
  let rightBottom ← addNode cfg g layers[1]!
  let outerNormalPort ← addPort cfg leftOuter .east
  let rightBottomPort ← addPort cfg rightBottom .west
  connect outerNormalPort rightBottomPort
  let inner ← nestedGraphShared leftOuter
  let innerLayers ← makeLayers inner 2
  let innerNormal ← addNode cfg inner innerLayers[0]!
  let hierarchPort ← addPort cfg leftOuter .east
  let innerDummy ← addExternalPortDummy innerLayers[1]! hierarchPort
  eastWestEdgeFromTo cfg innerNormal innerDummy
  if withUnusedPort then
    let _ ← addPort cfg leftOuter .east
  let rightTopPort ← addPort cfg rightTop .west
  connect hierarchPort rightTopPort
  runCrossmin g t
  let ports ← portsOf leftOuter
  let rightOrder ← layerNodes layers[1]!
  return sgn (idx ports outerNormalPort) (idx ports hierarchPort) == sgn (idx rightOrder rightBottom) (idx rightOrder rightTop)

/-- `assert_cross_with_no_external_port_dummies_on_one_nested_graph_removed(type)`. -/
def tNoExternalPortDummiesOnOneNested (t : CrossMinType) : LayeredM Bool := do
  let (g, leftOuter, rightOuter, leftPorts, _) ← twoOuterNodes
  let before ← countAllCrossings g
  let _ ← makeNestedTwoNodeGraphWithEasternPorts leftOuter leftPorts
  let rightInner ← nestedGraphShared rightOuter
  let rightInnerLayer ← makeLayer rightInner
  let _ ← addNodes cfg rightInner rightInnerLayer 2
  runCrossmin g t
  let after ← countAllCrossings g
  return after == 0 && after <= before

/-- `assert_nested_graph_with_wrongly_sorted_dummy_nodes_sorted_and_resolves(type)`. -/
def tWronglySortedDummies (t : CrossMinType) : LayeredM Bool := do
  let (g, leftOuter, rightOuter, leftPorts, rightPorts) ← twoOuterNodes
  let _ ← makeNestedTwoNodeGraphWithEasternPorts leftOuter leftPorts
  let rightInner ← nestedGraphShared rightOuter
  let dummyLayer ← makeLayer rightInner
  let dummies ← addExternalPortDummies dummyLayer #[rightPorts[1]!, rightPorts[0]!]
  let normalLayer ← makeLayer rightInner
  let normals ← addNodes cfg rightInner normalLayer 2
  eastWestEdgeFromTo cfg dummies[1]! normals[0]!
  eastWestEdgeFromTo cfg dummies[0]! normals[1]!
  let before ← countAllCrossings g
  runCrossmin g t
  let actualDummies ← layerNodes dummyLayer
  let actualPorts ← portsOf rightOuter
  let actualNormals ← layerNodes normalLayer
  if t == .barycenter then
    return actualDummies == dummies && actualPorts == #[rightPorts[1]!, rightPorts[0]!]
      && actualNormals == #[normals[1]!, normals[0]!]
  let after ← countAllCrossings g
  return after == 0 && after <= before
    && sgn (idx actualDummies dummies[1]!) (idx actualDummies dummies[0]!)
      == sgn (idx actualNormals normals[0]!) (idx actualNormals normals[1]!)

/-- Runs a check for both types (`_barycenter`, `_one_sided`). -/
def bothTypes (name : String) (t : CrossMinType → LayeredM Bool) : TestM Unit := do
  check s!"{name}_barycenter" (← runL (t .barycenter))
  check s!"{name}_one_sided" (← runL (t .oneSidedGreedySwitch))

def layerSweepTests : Suite := suite "layered.p3order.layer_sweep_crossing_minimizer" do
  bothTypes "given_no_node_shouldnt_crash" tNoNode
  bothTypes "given_one_node_shouldnt_crash" tOneNode
  check "simple_cross_graph_runs_and_keeps_layer_structure" (← runL tSimpleCrossBarycenter)
  check "simple_cross_graph_one_sided_switch_reorders_right_layer" (← runL tSimpleCrossOneSided)
  bothTypes "given_single_hierarchical_node_with_cross_removes_crossing" tSingleHierarchicalCross
  bothTypes "given_simple_hierarchical_cross_should_result_in_no_crossing" tSimpleHierarchicalCross
  bothTypes "given_simple_hierarchical_cross_sweeping_from_right_to_left_should_result_in_no_crossing"
    tSimpleHierarchicalCrossRightToLeft
  bothTypes "although_backward_sweep_not_taken_still_corrects_port_order" (tBackwardSweepNotTaken · 2)
  bothTypes "does_not_count_removable_port_crossing" (tBackwardSweepNotTaken · 1)
  bothTypes "resolves_in_layer_port_order_crossings_after_switch" tInLayerPortOrderAfterSwitch
  bothTypes "given_compound_graph_where_order_is_only_corrected_on_forward_sweep_removes_crossing"
    tCompoundForwardSweep
  bothTypes "given_graph_without_nesting_should_improve_on_backward_sweep" tImprovesOnBackwardSweep
  bothTypes "given_simple_graph_should_not_be_reordered_randomly_on_backward_sweep" tNotReorderedRandomly
  check "given_graph_which_worsens_on_backward_sweep_should_take_result_of_forward_sweep_one_sided"
    (← runL (tWorsensOnBackward .oneSidedGreedySwitch))
  bothTypes "given_cross_between_compound_and_non_compound_nodes_should_remove_crossing" tCrossCompoundNonCompound
  bothTypes "given_cross_in_first_level_compound_node_should_remove_crossing" tCrossInFirstLevelCompound
  bothTypes "given_graph_with_normal_edge_and_hierarchical_edge_crossing_should_remove_crossing"
    (tNormalAndHierarchicalCross · false)
  bothTypes "given_graph_with_port_without_edge_should_remove_crossing" (tNormalAndHierarchicalCross · true)
  bothTypes "given_cross_with_no_external_port_dummies_on_one_nested_graph_should_remove_crossing"
    tNoExternalPortDummiesOnOneNested
  bothTypes "given_nested_graph_with_wrongly_sorted_dummy_nodes_should_sort_and_resolve_crossing"
    tWronglySortedDummies

/-! ## `layer_sweep_type_decider_test.rs` -/

/-- Builders of the type decider test: an own `Random(0)` per graph and the full north/south edges. -/
def dCfg : Cfg := { selfUnit := true, fixSide := true, graphProps := true, full := true }

/-- `GraphInfoHolder::new(nested, BARYCENTER).dont_sweep_into()`. -/
def dontSweepIntoOf (graph : LGraphId) : LayeredM Bool := do
  let random ← IO.mkRef ((← graphRandom? graph).getD (Random.ofInt 0))
  return (← GraphInfoHolder.new graph .barycenter random).dontSweepInto

/-- Graph ids `0` (root) and `1` (nested). -/
def setGraphIds (root nested : LGraphId) : LayeredM Unit := do
  modifyGraph root fun x => { x with id := 0 }
  modifyGraph nested fun x => { x with id := 1 }

/-- `north_south_ports_change_decision`. -/
def tNorthSouthPortsChangeDecision : LayeredM Bool := do
  let g ← newGraph (Random.ofInt 0)
  let layers ← makeLayers g 3
  let leftOuter ← addNode dCfg g layers[0]!
  let middleOuter ← addNode dCfg g layers[1]!
  let rightOuter ← addNode dCfg g layers[2]!
  let leftPortMiddle ← addPort dCfg middleOuter .west
  let rightPortMiddle ← addPort dCfg middleOuter .east
  eastWestEdgeFromTo dCfg middleOuter rightOuter
  eastWestEdgeFromPort dCfg rightPortMiddle rightOuter
  eastWestEdgeFromNode dCfg leftOuter leftPortMiddle
  eastWestEdgeFromTo dCfg leftOuter middleOuter
  let nested ← nestedGraphOwn middleOuter (Random.ofInt 0)
  let inner ← makeLayers nested 5
  let leftDummy ← addExternalPortDummy inner[0]! leftPortMiddle
  let first ← addNodes dCfg nested inner[1]! 3
  let second ← addNodes dCfg nested inner[2]! 3
  let third ← addNodes dCfg nested inner[3]! 2
  let rightDummy ← addExternalPortDummy inner[4]! rightPortMiddle
  eastWestEdgeFromTo dCfg leftDummy first[2]!
  eastWestEdgeFromTo dCfg first[2]! second[2]!
  eastWestEdgeFromTo dCfg second[2]! third[1]!
  eastWestEdgeFromTo dCfg third[1]! rightDummy
  addNorthSouthEdge dCfg .north first[1]! first[0]! second[0]! false
  addNorthSouthEdge dCfg .south second[0]! second[1]! third[0]! false
  setGraphIds g nested
  setSweepinessOnAllGraphs g 0.1
  dontSweepIntoOf nested

/-- `all_hierarchical_but_minus_one_still_returns_bottom_up`. -/
def tAllHierarchicalButMinusOne : LayeredM Bool := do
  let g ← newGraph (Random.ofInt 0)
  let leftNode ← addNode dCfg g (← makeLayer g)
  let middleNode ← addNode dCfg g (← makeLayer g)
  let rightNode ← addNode dCfg g (← makeLayer g)
  let middleRight ← addPorts dCfg middleNode 2 .east
  let middleLeft ← addPorts dCfg middleNode 2 .west
  eastWestEdgeFromNode dCfg leftNode middleLeft[1]!
  eastWestEdgeFromNode dCfg leftNode middleLeft[0]!
  eastWestEdgeFromPort dCfg middleRight[0]! rightNode
  eastWestEdgeFromPort dCfg middleRight[1]! rightNode
  let inner ← nestedGraphOwn middleNode (Random.ofInt 0)
  let innerLayers ← makeLayers inner 3
  let leftInnerDummies ← addExternalPortDummies innerLayers[2]! middleRight
  let innerNode ← addNode dCfg inner innerLayers[1]!
  let rightInnerDummies ← addExternalPortDummies innerLayers[0]! middleLeft
  eastWestEdgeFromTo dCfg leftInnerDummies[0]! innerNode
  eastWestEdgeFromTo dCfg leftInnerDummies[1]! innerNode
  eastWestEdgeFromTo dCfg innerNode rightInnerDummies[0]!
  eastWestEdgeFromTo dCfg innerNode rightInnerDummies[1]!
  setGraphIds g inner
  setSweepinessOnAllGraphs g (-1.0)
  dontSweepIntoOf inner

/-- `port_with_no_edges_does_not_count`. -/
def tPortWithNoEdges : LayeredM Bool := do
  let g ← newGraph (Random.ofInt 0)
  let middleNode ← addNode dCfg g (← makeLayer g)
  let rightNode ← addNode dCfg g (← makeLayer g)
  let middleRight ← addPorts dCfg middleNode 2 .east
  eastWestEdgeFromPort dCfg middleRight[0]! rightNode
  eastWestEdgeFromPort dCfg middleRight[1]! rightNode
  let inner ← nestedGraphOwn middleNode (Random.ofInt 0)
  let innerLayers ← makeLayers inner 2
  let innerNode ← addNode dCfg inner innerLayers[0]!
  let rightInnerDummies ← addExternalPortDummies innerLayers[1]! middleRight
  eastWestEdgeFromTo dCfg innerNode rightInnerDummies[0]!
  eastWestEdgeFromTo dCfg innerNode rightInnerDummies[1]!
  let _ ← addPort dCfg innerNode .west
  setGraphIds g inner
  setSweepinessOnAllGraphs g (-0.1)
  dontSweepIntoOf inner

def typeDeciderTests : Suite := suite "layered.p3order.layer_sweep_type_decider" do
  check "north_south_ports_change_decision" (← runL tNorthSouthPortsChangeDecision)
  check "all_hierarchical_but_minus_one_still_returns_bottom_up" (← runL tAllHierarchicalButMinusOne)
  check "port_with_no_edges_does_not_count" (← runL tPortWithNoEdges)

/-! ## `basic_crossing_minimization_test.rs` -/

/-- `ensure_layer_assignment_unchanged_for(type)`: the layers keep their node sets. -/
def tLayerAssignmentUnchanged (t : CrossMinType) : LayeredM Bool := do
  let g ← newGraph (Random.ofInt 42)
  let left ← makeLayer g
  let middle ← makeLayer g
  let right ← makeLayer g
  let n1 ← addNode cfg g left
  let n2 ← addNode cfg g left
  let n3 ← addNode cfg g middle
  let n4 ← addNode cfg g middle
  let n5 ← addNode cfg g middle
  let n6 ← addNode cfg g right
  let n7 ← addNode cfg g right
  eastWestEdgeFromTo cfg n1 n4
  eastWestEdgeFromTo cfg n2 n3
  eastWestEdgeFromTo cfg n1 n5
  eastWestEdgeFromTo cfg n3 n7
  eastWestEdgeFromTo cfg n4 n6
  eastWestEdgeFromTo cfg n5 n7
  setUpIds g
  let before ← nodeArray g
  runMinimizer g t
  let after ← nodeArray g
  let sameSet (a b : Array LNodeId) : Bool := a.size == b.size && a.all b.contains
  return before.size == after.size && (before.zip after).all fun (a, b) => sameSet a b

def basicTests : Suite := suite "layered.p3order.basic_crossing_minimization" do
  check "ensure_layer_assignment_unchanged" (← runL (tLayerAssignmentUnchanged .barycenter))
  check "ensure_layer_assignment_unchanged_greedy_switch" (← runL (tLayerAssignmentUnchanged .twoSidedGreedySwitch))

/-! ## `greedy_switch_processor_test.rs` -/

/-- `set_in_layer_order_constraint(this_node, before_node)`. -/
def setInLayerOrderConstraint (thisNode beforeNode : LNodeId) : LayeredM Unit :=
  modifyNode thisNode fun x => { x with internal := { x.internal with inLayerSuccessorConstraints := #[beforeNode] } }

/-- `add_north_south_edge` of the greedy switch test (the dummy is appended to the associates). -/
def addNorthSouthEdgeAppend (side : PortSide) (nsNode dummy ewNode : LNodeId) (ewIsOrigin : Bool) : LayeredM Unit := do
  addNorthSouthEdge cfg side nsNode dummy ewNode ewIsOrigin
  modifyNode nsNode fun x => { x with internal := { x.internal with barycenterAssociates := x.internal.barycenterAssociates.push dummy } }
  if side == .north then
    modifyNode dummy fun x => { x with internal := { x.internal with
      inLayerSuccessorConstraints := x.internal.inLayerSuccessorConstraints.push nsNode } }
  else
    modifyNode nsNode fun x => { x with internal := { x.internal with
      inLayerSuccessorConstraints := x.internal.inLayerSuccessorConstraints.push dummy } }

/-- The nodes of layer `i`. -/
def layerAt (g : LGraphId) (i : Nat) : LayeredM (Array LNodeId) := do
  return (← nodeArray g)[i]?.getD #[]

/-- `copy_of_switch_order_of_nodes_in_layer(graph, upper, lower, layer)`. -/
def switched (g : LGraphId) (upper lower i : Nat) : LayeredM (Array LNodeId) := do
  return (← layerAt g i).swapIfInBounds upper lower

/-- `graph_cross_formed()`. -/
def graphCrossFormed : LayeredM LGraphId := do
  let (g, _) ← simpleCross
  setUpIds g
  return g

/-- `graph_cross_formed_with_constraints_in_second_layer()`. -/
def graphCrossFormedConstrained : LayeredM LGraphId := do
  let g ← graphCrossFormed
  let nodes ← layerAt g 1
  setInLayerOrderConstraint nodes[0]! nodes[1]!
  setUpIds g
  return g

/-- `graph_cross_formed_constraints_prevent_any_switch()`. -/
def graphCrossFormedNoSwitch : LayeredM LGraphId := do
  let (g, n) ← simpleCross
  setInLayerOrderConstraint n[2]! n[3]!
  setInLayerOrderConstraint n[0]! n[1]!
  setUpIds g
  return g

/-- `graph_in_layer_edges()`. -/
def graphInLayerEdges : LayeredM LGraphId := do
  let g ← newGraph
  let leftLayer ← makeLayer g
  let middleLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let left ← addNode cfg g leftLayer
  let middle ← addNodes cfg g middleLayer 3
  let right ← addNode cfg g rightLayer
  eastWestEdgeFromTo cfg middle[1]! right
  eastWestEdgeFromTo cfg left middle[1]!
  addInLayerEdge cfg middle[0]! middle[2]! .west
  setUpIds g
  return g

/-- `graph_multiple_edges_between_same_nodes()`. -/
def graphMultipleEdges : LayeredM LGraphId := do
  let g ← newGraph
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let tl ← addNode cfg g leftLayer
  let bl ← addNode cfg g leftLayer
  let tr ← addNode cfg g rightLayer
  let br ← addNode cfg g rightLayer
  eastWestEdgeFromTo cfg tl br
  eastWestEdgeFromTo cfg tl br
  eastWestEdgeFromTo cfg bl tr
  eastWestEdgeFromTo cfg bl tr
  setUpIds g
  return g

/-- `graph_more_complex_three_layer()`. -/
def graphMoreComplex : LayeredM LGraphId := do
  let g ← newGraph
  let leftLayer ← makeLayer g
  let middleLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let left ← addNodes cfg g leftLayer 3
  let middle ← addNodes cfg g middleLayer 2
  let right ← addNodes cfg g rightLayer 3
  let leftMiddlePort ← addPort cfg left[1]! .east
  let middleLowerEast ← addPort cfg middle[1]! .east
  let middleUpperEast ← addPort cfg middle[0]! .east
  let rightUpperPort ← addPort cfg right[0]! .west
  let rightMiddlePort ← addPort cfg right[1]! .west
  setUpIds g
  connect middleUpperEast rightUpperPort
  connect middleUpperEast rightMiddlePort
  connect middleUpperEast rightMiddlePort
  eastWestEdgeFromPort cfg middleLowerEast right[2]!
  eastWestEdgeFromPort cfg leftMiddlePort middle[0]!
  eastWestEdgeFromNode cfg middle[1]! rightUpperPort
  eastWestEdgeFromPort cfg leftMiddlePort middle[1]!
  eastWestEdgeFromTo cfg left[2]! middle[0]!
  eastWestEdgeFromTo cfg left[0]! middle[0]!
  setUpIds g
  return g

/-- `graph_switch_only_one_sided()`. -/
def graphSwitchOnlyOneSided : LayeredM LGraphId := do
  let g ← newGraph
  let layers ← makeLayers g 3
  let left ← addNodes cfg g layers[0]! 2
  let middle ← addNodes cfg g layers[1]! 2
  let right ← addNodes cfg g layers[2]! 2
  eastWestEdgeFromTo cfg middle[0]! right[0]!
  eastWestEdgeFromTo cfg middle[1]! right[1]!
  eastWestEdgeFromTo cfg left[0]! middle[1]!
  eastWestEdgeFromTo cfg left[1]! middle[0]!
  setUpIds g
  return g

/-- `graph_which_could_be_worsened_by_switch()`. -/
def graphCouldBeWorsened : LayeredM LGraphId := do
  let g ← newGraph
  let layers ← makeLayers g 3
  let left ← addNodes cfg g layers[0]! 2
  let middle ← addNodes cfg g layers[1]! 2
  let right ← addNodes cfg g layers[2]! 2
  setInLayerOrderConstraint left[0]! left[1]!
  setInLayerOrderConstraint right[0]! right[1]!
  eastWestEdgeFromTo cfg middle[0]! right[1]!
  eastWestEdgeFromTo cfg middle[1]! right[0]!
  eastWestEdgeFromTo cfg left[0]! middle[0]!
  eastWestEdgeFromTo cfg left[0]! middle[0]!
  eastWestEdgeFromTo cfg left[1]! middle[1]!
  eastWestEdgeFromTo cfg left[1]! middle[1]!
  setUpIds g
  return g

/-- `graph_nodes_in_different_layout_units_prevent_switch()`. -/
def graphDifferentLayoutUnits : LayeredM LGraphId := do
  let g ← newGraph
  let layers ← makeLayers g 2
  let left ← addNodes cfg g layers[0]! 2
  let right ← addNodes cfg g layers[1]! 3
  eastWestEdgeFromTo cfg left[1]! right[0]!
  addNorthSouthEdgeAppend .east right[2]! right[1]! left[0]! true
  modifyNode right[1]! fun x => { x with internal := { x.internal with inLayerLayoutUnit := some right[2]! } }
  modifyNode right[2]! fun x => { x with internal := { x.internal with inLayerLayoutUnit := some right[2]! } }
  setUpIds g
  return g

/-- `graph_north_south_downward_crossing()`. -/
def graphNorthSouthDownwardCrossing : LayeredM LGraphId := do
  let g ← newGraph
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let left ← addNodes cfg g leftLayer 3
  let right ← addNodes cfg g rightLayer 2
  addNorthSouthEdgeAppend .south left[0]! left[2]! right[1]! false
  addNorthSouthEdgeAppend .south left[0]! left[1]! right[0]! false
  setFixedOrderConstraint cfg left[0]!
  setUpIds g
  return g

/-- `should_switch_cross` / `multiple_edges_between_same_nodes`: one-sided switches the second
layer, two-sided the first. -/
def tSwitchesCross (graph : LayeredM LGraphId) (t : CrossMinType) : LayeredM Bool := do
  let g ← graph
  let (e1, e2) ← if t == .oneSidedGreedySwitch then do pure (← layerAt g 0, ← switched g 0 1 1)
    else do pure (← switched g 0 1 0, ← layerAt g 1)
  runMinimizer g t
  return (← layerAt g 0) == e1 && (← layerAt g 1) == e2

/-- `constraints_prevent_switch_in_second_layer`. -/
def tConstraintsPreventSecondLayer (t : CrossMinType) : LayeredM Bool := do
  let g ← graphCrossFormedConstrained
  let e1 ← switched g 0 1 0
  let e2 ← layerAt g 1
  runMinimizer g t
  return (← layerAt g 0) == e1 && (← layerAt g 1) == e2

/-- An unchanged order of the given layers after the run. -/
def tUnchanged (graph : LayeredM LGraphId) (layers : Array Nat) (t : CrossMinType) : LayeredM Bool := do
  let g ← graph
  let expected ← layers.mapM (layerAt g)
  runMinimizer g t
  return (← layers.mapM (layerAt g)) == expected

/-- `in_layer_switchable`. -/
def tInLayerSwitchable (t : CrossMinType) : LayeredM Bool := do
  let g ← graphInLayerEdges
  let expected ← switched g 0 1 1
  runMinimizer g t
  return (← layerAt g 1) == expected

/-- `self_loops`. -/
def tSelfLoops (t : CrossMinType) : LayeredM Bool := do
  let g ← newGraph
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let tl ← addNode cfg g leftLayer
  let bl ← addNode cfg g leftLayer
  let tr ← addNode cfg g rightLayer
  let br ← addNode cfg g rightLayer
  let tlPort ← addPort cfg tl .east
  let blPort ← addPort cfg bl .east
  setUpIds g
  for layer in (← getGraph g).layers do
    for node in (← getLayer layer).nodes do
      for _ in [0:3] do selfLoopOn cfg node .east
      for _ in [0:3] do selfLoopOn cfg node .west
  let trPort ← addPort cfg tr .west
  let brPort ← addPort cfg br .west
  connect tlPort brPort
  connect blPort trPort
  let (e1, e2) ← if t == .oneSidedGreedySwitch then do pure (← layerAt g 0, ← switched g 0 1 1)
    else do pure (← switched g 0 1 0, ← layerAt g 1)
  runMinimizer g t
  return (← layerAt g 0) == e1 && (← layerAt g 1) == e2

/-- `north_south_port_crossing`. -/
def tNorthSouthPortCrossing (t : CrossMinType) : LayeredM Bool := do
  let g ← graphNorthSouthDownwardCrossing
  let twoSided ← layerAt g 0
  let oneSided ← switched g 1 2 0
  runMinimizer g t
  return (← layerAt g 0) == (if t == .oneSidedGreedySwitch then oneSided else twoSided)

/-- `more_complex`. -/
def tMoreComplex (t : CrossMinType) : LayeredM Bool := do
  let g ← graphMoreComplex
  let e2 ← layerAt g 1
  let e3 ← switched g 0 1 2
  runMinimizer g t
  return (← layerAt g 1) == e2 && (← layerAt g 2) == e3

/-- `switch_only_for_one_sided`. -/
def tSwitchOnlyOneSided (t : CrossMinType) : LayeredM Bool := do
  let g ← graphSwitchOnlyOneSided
  let oneSided ← switched g 0 1 1
  let twoSided ← layerAt g 1
  runMinimizer g t
  return (← layerAt g 1) == (if t == .oneSidedGreedySwitch then oneSided else twoSided)

/-- `switch_more_than_once`. -/
def tSwitchMoreThanOnce (t : CrossMinType) : LayeredM Bool := do
  let g ← newGraph
  let left ← addNodes cfg g (← makeLayer g) 2
  let right ← addNodes cfg g (← makeLayer g) 4
  let leftTop ← addPort cfg left[0]! .east
  let leftLower ← addPort cfg left[1]! .east
  let rightTop ← addPort cfg right[0]! .west
  connect leftLower rightTop
  eastWestEdgeFromPort cfg leftLower right[2]!
  connect leftTop rightTop
  eastWestEdgeFromPort cfg leftTop right[1]!
  eastWestEdgeFromPort cfg leftTop right[3]!
  setUpIds g
  let oneFirstLayer ← layerAt g 0
  let oneThird := ((← switched g 0 1 1).swapIfInBounds 2 3).swapIfInBounds 1 2
  let twoFirstLayer ← switched g 0 1 0
  let twoSecond := (← switched g 1 2 1).swapIfInBounds 0 1
  runMinimizer g t
  if t == .oneSidedGreedySwitch then
    return (← layerAt g 0) == oneFirstLayer && (← layerAt g 1) == oneThird
  return (← layerAt g 0) == twoFirstLayer && (← layerAt g 1) == twoSecond

/-- Runs a check for both greedy types (`for_each_greedy_type`). -/
def bothGreedy (name : String) (t : CrossMinType → LayeredM Bool) : TestM Unit := do
  check s!"{name} (one-sided)" (← runL (t .oneSidedGreedySwitch))
  check s!"{name} (two-sided)" (← runL (t .twoSidedGreedySwitch))

def greedySwitchProcessorTests : Suite := suite "layered.intermediate.greedyswitch.greedy_switch_processor" do
  bothGreedy "should_switch_cross" (tSwitchesCross graphCrossFormed)
  bothGreedy "constraints_prevent_switch_in_second_layer" tConstraintsPreventSecondLayer
  bothGreedy "constraints_prevent_any_switch" (tUnchanged graphCrossFormedNoSwitch #[0, 1])
  bothGreedy "layout_unit_constraint_prevents_switch" (tUnchanged graphDifferentLayoutUnits #[1])
  bothGreedy "in_layer_switchable" tInLayerSwitchable
  bothGreedy "multiple_edges_between_same_nodes" (tSwitchesCross graphMultipleEdges)
  bothGreedy "self_loops" tSelfLoops
  bothGreedy "north_south_port_crossing" tNorthSouthPortCrossing
  bothGreedy "more_complex" tMoreComplex
  bothGreedy "switch_only_for_one_sided" tSwitchOnlyOneSided
  bothGreedy "does_not_worsen_cross_amount" (tUnchanged graphCouldBeWorsened #[0, 1])
  bothGreedy "switch_more_than_once" tSwitchMoreThanOnce

/-! ## `layer_sweep_hierarchical_two_sided_greedy_switch_test.rs` -/

/-- `new_graph()` of the file: `Random(99)`. -/
def hGraph : LayeredM LGraphId := newGraph (Random.ofInt 99)

/-- A graph with its own `Random(99)` as the nested graph of `node` without a parent link
(`outer.set_nested_graph(nested)` only). -/
def unlinkedNested (node : LNodeId) : LayeredM LGraphId := do
  let nested ← hGraph
  modifyNode node fun x => { x with nestedGraph := some nested }
  return nested

/-- `two_sided_greedy_switch_runs_on_simple_cross_graph`. -/
def tTwoSidedRunsSimple : LayeredM Bool := do
  let g ← hGraph
  let left ← makeLayer g
  let right ← makeLayer g
  let n ← addNodes cfg g left 2
  let m ← addNodes cfg g right 2
  eastWestEdgeFromTo cfg n[0]! m[1]!
  eastWestEdgeFromTo cfg n[1]! m[0]!
  runMinimizer g .twoSidedGreedySwitch
  return true

/-- `two_sided_greedy_switch_runs_with_nested_graph`. -/
def tTwoSidedRunsNested : LayeredM Bool := do
  let g ← hGraph
  let left ← makeLayer g
  let right ← makeLayer g
  let outer ← addNode cfg g left
  let rightTop ← addNode cfg g right
  let rightBottom ← addNode cfg g right
  eastWestEdgeFromTo cfg outer rightTop
  eastWestEdgeFromTo cfg outer rightBottom
  let nested ← hGraph
  let nl ← makeLayer nested
  let nr ← makeLayer nested
  let i ← addNodes cfg nested nl 2
  let j ← addNodes cfg nested nr 2
  eastWestEdgeFromTo cfg i[0]! j[1]!
  eastWestEdgeFromTo cfg i[1]! j[0]!
  modifyNode outer fun x => { x with nestedGraph := some nested }
  runMinimizer g .twoSidedGreedySwitch
  return (← getGraph g).layers.size == 2

/-- `two_sided_greedy_switch_removes_cross_in_single_nested_graph`. -/
def tTwoSidedRemovesNestedCross : LayeredM Bool := do
  let g ← hGraph
  let outer ← addNode cfg g (← makeLayer g)
  let nested ← unlinkedNested outer
  let left ← makeLayer nested
  let right ← makeLayer nested
  let l0 ← addNode cfg nested left
  let l1 ← addNode cfg nested left
  let r0 ← addNode cfg nested right
  let r1 ← addNode cfg nested right
  eastWestEdgeFromTo cfg l0 r1
  eastWestEdgeFromTo cfg l1 r0
  runMinimizer g .twoSidedGreedySwitch
  let leftNodes ← layerNodes left
  let rightNodes ← layerNodes right
  return sgn (idx leftNodes l0) (idx leftNodes l1) == sgn (idx rightNodes r1) (idx rightNodes r0)

/-- `two_sided_greedy_switch_forward_sweep_case_reorders_inner_layer`. -/
def tTwoSidedForwardSweepInner : LayeredM Bool := do
  let g ← hGraph
  let outer ← addNode cfg g (← makeLayer g)
  let nested ← unlinkedNested outer
  let leftLayer ← makeLayer nested
  let rightLayer ← makeLayer nested
  let left ← addNode cfg nested leftLayer
  setFixedOrderConstraint cfg left
  let r0 ← addNode cfg nested rightLayer
  let r1 ← addNode cfg nested rightLayer
  eastWestEdgeFromTo cfg left r1
  eastWestEdgeFromTo cfg left r0
  let before ← layerNodes rightLayer
  runMinimizer g .twoSidedGreedySwitch
  let after ← layerNodes rightLayer
  return after.size == 2 && after == #[before[1]!, before[0]!]

/-- `given_cross_in_first_level_compound_node_using_two_sided_greedy_switch_leaves_crossing`. -/
def tTwoSidedFirstLevelLeavesCrossing : LayeredM Bool := do
  let g ← hGraph
  let leftLayer ← makeLayer g
  let rightLayer ← makeLayer g
  let leftOuter ← addNode cfg g leftLayer
  let right ← addNodes cfg g rightLayer 2
  let leftPorts ← addPorts cfg leftOuter 2 .east
  eastWestEdgeFromPort cfg leftPorts[0]! right[0]!
  eastWestEdgeFromPort cfg leftPorts[1]! right[1]!
  let inner ← nestedGraphOwn leftOuter (Random.ofInt 99)
  let innerLeft ← makeLayer inner
  let innerRight ← makeLayer inner
  let innerDummy ← makeLayer inner
  let il ← addNodes cfg inner innerLeft 2
  let ir ← addNodes cfg inner innerRight 2
  let dummies ← addExternalPortDummies innerDummy leftPorts
  eastWestEdgeFromTo cfg ir[0]! dummies[0]!
  eastWestEdgeFromTo cfg ir[1]! dummies[1]!
  eastWestEdgeFromTo cfg il[0]! ir[1]!
  eastWestEdgeFromTo cfg il[1]! ir[0]!
  setGraphProp g LayeredOptions.CROSSING_MINIMIZATION_HIERARCHICAL_SWEEPINESS (-1.0)
  let expected ← layerNodes rightLayer
  runMinimizer g .twoSidedGreedySwitch
  return (← layerNodes rightLayer) == expected

/-- A left node whose two east ports lead to a fixed-order right node, with a nested graph whose
inner node is connected to the two port dummies (`connectSwapped` swaps the inner edges and the
order of the outer edges). -/
def tTwoSidedDummyOrder (swapped : Bool) : LayeredM Bool := do
  let g ← hGraph
  let leftNode ← addNode cfg g (← makeLayer g)
  let rightNode ← addNode cfg g (← makeLayer g)
  let leftPorts ← addPorts cfg leftNode 2 .east
  if swapped then
    eastWestEdgeFromPort cfg leftPorts[1]! rightNode
    eastWestEdgeFromPort cfg leftPorts[0]! rightNode
  else
    eastWestEdgeFromPort cfg leftPorts[0]! rightNode
    eastWestEdgeFromPort cfg leftPorts[1]! rightNode
  setFixedOrderConstraint cfg rightNode
  let inner ← nestedGraphOwn leftNode (Random.ofInt 99)
  let innerLayers ← makeLayers inner 2
  let innerLeft ← addNode cfg inner innerLayers[0]!
  setFixedOrderConstraint cfg innerLeft
  let dummies ← addExternalPortDummies innerLayers[1]! leftPorts
  if swapped then
    eastWestEdgeFromTo cfg innerLeft dummies[1]!
    eastWestEdgeFromTo cfg innerLeft dummies[0]!
  else
    eastWestEdgeFromTo cfg innerLeft dummies[0]!
    eastWestEdgeFromTo cfg innerLeft dummies[1]!
  let expected ← layerNodes innerLayers[1]!
  runMinimizer g .twoSidedGreedySwitch
  return (← layerNodes innerLayers[1]!) == expected

/-- `crossing_before_first_layer_causes_crossing_outside_two_sided_prevents`. -/
def tTwoSidedCrossingBeforeFirstLayer : LayeredM Bool := do
  let random := ((Random.ofInt 0).setMockNextBoolean false).setMockDoubleSequence 0.0 0.0001
  let g ← newGraph random
  let leftNode ← addNode cfg g (← makeLayer g)
  let rightNode ← addNode cfg g (← makeLayer g)
  let rightPorts ← addPorts cfg rightNode 2 .west
  eastWestEdgeFromNode cfg leftNode rightPorts[1]!
  eastWestEdgeFromNode cfg leftNode rightPorts[0]!
  setFixedOrderConstraint cfg leftNode
  let inner ← nestedGraphOwn rightNode (Random.ofInt 99)
  let innerLayers ← makeLayers inner 2
  let innerRight ← addNode cfg inner innerLayers[1]!
  setFixedOrderConstraint cfg innerRight
  let dummies ← addExternalPortDummies innerLayers[0]! rightPorts
  eastWestEdgeFromTo cfg dummies[0]! innerRight
  eastWestEdgeFromTo cfg dummies[1]! innerRight
  let expected ← layerNodes innerLayers[0]!
  runMinimizer g .twoSidedGreedySwitch
  return (← layerNodes innerLayers[0]!) == expected

def hierarchicalTwoSidedTests : Suite := suite "layered.intermediate.greedyswitch.layer_sweep_hierarchical_two_sided" do
  check "two_sided_greedy_switch_runs_on_simple_cross_graph" (← runL tTwoSidedRunsSimple)
  check "two_sided_greedy_switch_runs_with_nested_graph" (← runL tTwoSidedRunsNested)
  check "two_sided_greedy_switch_removes_cross_in_single_nested_graph" (← runL tTwoSidedRemovesNestedCross)
  check "two_sided_greedy_switch_forward_sweep_case_reorders_inner_layer" (← runL tTwoSidedForwardSweepInner)
  check "given_cross_in_first_level_compound_node_using_two_sided_greedy_switch_leaves_crossing"
    (← runL tTwoSidedFirstLevelLeavesCrossing)
  check "only_two_sided_greedy_switch_returns_no_change" (← runL (tTwoSidedDummyOrder false))
  check "crossing_before_last_layer_causes_crossing_outside_two_sided_prevents" (← runL (tTwoSidedDummyOrder true))
  check "crossing_before_first_layer_causes_crossing_outside_two_sided_prevents" (← runL tTwoSidedCrossingBeforeFirstLayer)

def suites : Array Suite := #[layerSweepTests, typeDeciderTests, basicTests, greedySwitchProcessorTests,
  hierarchicalTwoSidedTests]

end Tests.Layered.P3LayerSweep
