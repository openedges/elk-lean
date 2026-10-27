import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Components
/-! Tests of `org.eclipse.elk.alg.layered.components`: component groups (port of elk-rs
`tests/components/component_group_test.rs`), `ComponentsProcessor.split`/`combine`, the graph
placers, the Rust unit tests of `components_processor.rs` and the components compactor
(`tests/compaction/compaction_test.rs` adapted, see `compactionCases`). -/
namespace Tests.Layered.Components

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open Elk.Alg.Layered.Components PortSide

/-- Rust `generate_graph(connections)`: a graph with the given `EXT_PORT_CONNECTIONS`. -/
def generateGraph (connections : EnumSet PortSide) : LayeredM LGraphId :=
  LayeredM.createGraph { internal := { extPortConnections := connections } }

/-- Runs `(connections, expected add result)` steps on a fresh `ComponentGroup`; returns the
indices of the steps whose result differs. -/
def runGroup (steps : Array (EnumSet PortSide × Bool)) : LayeredM (Array Nat) := do
  let mut g := ComponentGroup.new
  let mut wrong : Array Nat := #[]
  for i in [0:steps.size] do
    let (sides, expected) := steps[i]!
    let (ok, g') ← g.add (← generateGraph sides)
    g := g'
    if ok != expected then wrong := wrong.push i
  return wrong

/-- `runGroup` for `ModelOrderComponentGroup`. -/
def runGroupMO (steps : Array (EnumSet PortSide × Bool)) : LayeredM (Array Nat) := do
  let mut g := ModelOrderComponentGroup.new
  let mut wrong : Array Nat := #[]
  for i in [0:steps.size] do
    let (sides, expected) := steps[i]!
    let (ok, g') ← g.add (← generateGraph sides)
    g := g'
    if ok != expected then wrong := wrong.push i
  return wrong

def componentGroupTests : Suite := suite "layered.components.componentGroup" do
  -- test_valid_constraints
  let ((v1, v2, v3, v4), _) ← LayeredM.run (do
    let v1 ← runGroup #[(SIDES_NORTH, true), (SIDES_NORTH, true), (SIDES_SOUTH, true), (SIDES_SOUTH, true),
      (SIDES_WEST, true), (SIDES_WEST, true), (SIDES_EAST, true), (SIDES_EAST, true), (SIDES_NONE, true),
      (SIDES_NONE, true)]
    let v2 ← runGroup #[(SIDES_EAST_WEST, true), (SIDES_EAST_WEST, true), (SIDES_WEST, true), (SIDES_WEST, true),
      (SIDES_EAST, true), (SIDES_EAST, true), (SIDES_NONE, true), (SIDES_NONE, true)]
    let v3 ← runGroup #[(SIDES_NORTH_SOUTH, true), (SIDES_NORTH_SOUTH, true), (SIDES_NORTH, true), (SIDES_NORTH, true),
      (SIDES_SOUTH, true), (SIDES_SOUTH, true), (SIDES_NONE, true), (SIDES_NONE, true)]
    let v4 ← runGroup #[(SIDES_NORTH_EAST_SOUTH_WEST, true), (SIDES_NORTH_WEST, true), (SIDES_NORTH_EAST, true),
      (SIDES_SOUTH_WEST, true), (SIDES_EAST_SOUTH, true)]
    return (v1, v2, v3, v4))
  checkEq "test_valid_constraints: single sides" v1 #[]
  checkEq "test_valid_constraints: east-west with sides" v2 #[]
  checkEq "test_valid_constraints: north-south with sides" v3 #[]
  checkEq "test_valid_constraints: all sides and corners" v4 #[]
  -- test_invalid_constraints
  let ((i1, i2, i3, i4), _) ← LayeredM.run (do
    let i1 ← runGroup #[(SIDES_EAST_WEST, true), (SIDES_NORTH_SOUTH, false), (SIDES_NORTH_SOUTH_WEST, false),
      (SIDES_NORTH_EAST_SOUTH, false)]
    let i2 ← runGroup #[(SIDES_NORTH_SOUTH, true), (SIDES_EAST_WEST, false), (SIDES_NORTH_EAST_WEST, false),
      (SIDES_EAST_SOUTH_WEST, false)]
    let i3 ← runGroup #[(SIDES_NORTH_WEST, true), (SIDES_NORTH_EAST, true), (SIDES_SOUTH_WEST, true),
      (SIDES_EAST_SOUTH, true), (SIDES_NORTH_EAST_SOUTH, false), (SIDES_NORTH_EAST_WEST, false),
      (SIDES_EAST_SOUTH_WEST, false), (SIDES_NORTH_SOUTH_WEST, false)]
    let i4 ← runGroup #[(SIDES_NORTH_EAST_SOUTH_WEST, true), (SIDES_NONE, false), (SIDES_NORTH_SOUTH, false),
      (SIDES_EAST_WEST, false), (SIDES_NORTH_EAST_SOUTH, false), (SIDES_NORTH_EAST_WEST, false),
      (SIDES_EAST_SOUTH_WEST, false), (SIDES_NORTH_SOUTH_WEST, false), (SIDES_NORTH_EAST_SOUTH_WEST, false)]
    return (i1, i2, i3, i4))
  checkEq "test_invalid_constraints: east-west blocks north-south" i1 #[]
  checkEq "test_invalid_constraints: north-south blocks east-west" i2 #[]
  checkEq "test_invalid_constraints: corners block three sides" i3 #[]
  checkEq "test_invalid_constraints: all sides block everything" i4 #[]
  -- test_model_order_constraints
  let ((m1, m2), _) ← LayeredM.run (do
    let m1 ← runGroupMO #[(SIDES_NONE, true), (SIDES_NORTH, false)]
    let m2 ← runGroupMO #[(SIDES_EAST, true), (SIDES_EAST_WEST, false)]
    return (m1, m2))
  checkEq "test_model_order_constraints: none blocks north" m1 #[]
  checkEq "test_model_order_constraints: east blocks east-west" m2 #[]
  -- grouping and order queries (hand: entries by mask in insertion order of the masks)
  let ((sides, comps, forWest, moSides, moComps), _) ← LayeredM.run (do
    let a ← generateGraph SIDES_WEST
    let b ← generateGraph SIDES_NONE
    let c ← generateGraph SIDES_WEST
    let mut g := ComponentGroup.new
    for x in #[a, b, c] do g := (← g.add x).2
    let mut mo := ModelOrderComponentGroup.new
    for x in #[a, c] do mo := (← mo.add x).2
    let d ← generateGraph SIDES_WEST
    mo := (← mo.add d).2
    return (g.portSides.map (·.toArray), g.components, g.componentsFor SIDES_WEST,
      mo.portSides.map (·.toArray), mo.components))
  checkEq "group port sides grouped by mask" sides.toList [#[PortSide.west], #[.west], #[]]
  checkEq "group components grouped by mask (a, c, b)" (comps.map (·.idx)) #[0, 2, 1]
  checkEq "group components for WEST" (forWest.map (·.idx)) #[0, 2]
  checkEq "model order group port sides in insertion order" moSides.toList [#[PortSide.west], #[.west], #[.west]]
  checkEq "model order group components in insertion order" (moComps.map (·.idx)) #[0, 2, 3]
  checkEq "connections to mask NESW" (ComponentGroup.connectionsToMask SIDES_NORTH_EAST_SOUTH_WEST) 15
  checkEq "connections to mask ignores UNDEFINED" (ComponentGroup.connectionsToMask (EnumSet.of #[.undefined, .west])) 8
  checkEq "mask to connections (5 = north + south)" (ComponentGroup.maskToConnections 5).toArray #[.north, .south]
  -- hand: the pairs with candidate NORTH_SOUTH in list order: EAST, SOUTH, EAST_SOUTH, SOUTH_WEST,
  -- EAST_SOUTH_WEST, NORTH_EAST_SOUTH, NONE, NORTH (the second SOUTH is a duplicate)
  checkEq "model order constraints of NORTH_SOUTH"
    (ModelOrderComponentGroup.modelOrderConstraintMasks ComponentGroup.MASK_NORTH_SOUTH) #[2, 4, 6, 12, 14, 7, 0, 1]

/-! ## `split` -/

/-- The sample graph of the split/combine tests: layerless `[n0, n1, n2, n3, n4, n5]` (10 x 10
at `(i, 0)`), edges `e0: n0 → n2` (bend point, junction point, label), `e1: n3 → n0`,
`e2: n1 → n4`, `n5` isolated. `n0` has the ports `p0a` (target of `e1`) and `p0b` (source of
`e0`). -/
structure Sample where
  graph : LGraphId
  nodes : Array LNodeId
  edges : Array LEdgeId
  labels : Array LLabelId

def mkPort (n : LNodeId) : LayeredM LPortId := do
  let p ← LayeredM.createPort
  LayeredM.setPortNode p (some n)
  return p

def buildSample (configure : LGraph → LGraph := id) : LayeredM Sample := do
  let g ← LayeredM.createGraph (configure {
    props := (({} : PropertyMap).set CoreOptions.SPACING_NODE_NODE 33.0).set CoreOptions.NODE_SIZE_MINIMUM ⟨5.0, 5.0⟩,
    padding := ⟨1.0, 2.0, 3.0, 4.0⟩,
    internal := { graphProperties := EnumSet.of #[.selfLoops] } })
  let mut nodes : Array LNodeId := #[]
  for i in [0:6] do
    nodes := nodes.push (← LayeredM.createNode g { size := ⟨10.0, 10.0⟩, position := ⟨i.toFloat, 0.0⟩ })
  let all := nodes
  LayeredM.modifyGraph g fun x => { x with layerlessNodes := all }
  let p0a ← mkPort nodes[0]!
  let p0b ← mkPort nodes[0]!
  let p2 ← mkPort nodes[2]!
  let p3 ← mkPort nodes[3]!
  let p1 ← mkPort nodes[1]!
  let p4 ← mkPort nodes[4]!
  let e0 ← LayeredM.createEdge { bendPoints := #[⟨10.0, 10.0⟩] }
  LayeredM.setEdgeSource e0 (some p0b)
  LayeredM.setEdgeTarget e0 (some p2)
  LayeredM.setEdgeProp e0 CoreOptions.JUNCTION_POINTS #[⟨1.0, 1.0⟩]
  let l0 ← LayeredM.createLabel "e0" { position := ⟨2.0, 2.0⟩ }
  LayeredM.modifyEdge e0 fun e => { e with labels := #[l0] }
  let e1 ← LayeredM.createEdge
  LayeredM.setEdgeSource e1 (some p3)
  LayeredM.setEdgeTarget e1 (some p0a)
  let e2 ← LayeredM.createEdge
  LayeredM.setEdgeSource e2 (some p1)
  LayeredM.setEdgeTarget e2 (some p4)
  return { graph := g, nodes, edges := #[e0, e1, e2], labels := #[l0] }

def splitTests : Suite := suite "layered.components.split" do
  let ((s, comps), a) ← LayeredM.run (do
    let s ← buildSample
    let comps ← ComponentsProcessor.split s.graph
    return (s, comps))
  let n := s.nodes
  -- hand: DFS from n0: adjacency(n0) = [n3 (incoming e1 at p0a), n2 (outgoing e0 at p0b)]
  checkEq "three components (2 connected + 1 isolated)" comps.size 3
  checkEq "component 0 in DFS order [n0, n3, n2]" (a.graph comps[0]!).layerlessNodes #[n[0]!, n[3]!, n[2]!]
  checkEq "component 1 [n1, n4]" (a.graph comps[1]!).layerlessNodes #[n[1]!, n[4]!]
  checkEq "component 2 [n5]" (a.graph comps[2]!).layerlessNodes #[n[5]!]
  checkEq "nodes point to their component graph" (a.nodeGraph n[3]!) (some comps[0]!)
  checkEq "isolated node points to its component" (a.nodeGraph n[5]!) (some comps[2]!)
  checkEq "original graph keeps its layerless list" (a.graph s.graph).layerlessNodes n
  checkFloat "options copied (SPACING_NODE_NODE)" ((a.graph comps[1]!).props.getD CoreOptions.SPACING_NODE_NODE 0.0) 33.0
  check "NODE_SIZE_MINIMUM removed" (!(a.graph comps[1]!).props.has CoreOptions.NODE_SIZE_MINIMUM)
  check "original keeps NODE_SIZE_MINIMUM" ((a.graph s.graph).props.has CoreOptions.NODE_SIZE_MINIMUM)
  checkEqR "padding copied" (a.graph comps[2]!).padding ⟨1.0, 2.0, 3.0, 4.0⟩
  check "internals copied (GRAPH_PROPERTIES)" ((a.graph comps[0]!).internal.graphProperties.contains .selfLoops)
  check "no external port connections" (a.graph comps[0]!).internal.extPortConnections.isEmpty
  -- SEPARATE_CONNECTED_COMPONENTS = false
  let ((s2, comps2), _) ← LayeredM.run (do
    let s ← buildSample fun g => { g with props := g.props.set CoreOptions.SEPARATE_CONNECTED_COMPONENTS false }
    return (s, ← ComponentsProcessor.split s.graph))
  checkEq "split disabled: the graph itself" comps2 #[s2.graph]
  -- model order: comp of n1 (min 2) < comp of n0 (min 5) < comp of n5 (none = Integer.MAX_VALUE)
  let ((s3, comps3), a3) ← LayeredM.run (do
    let s ← buildSample fun g => { g with props := (g.props.set LayeredOptions.CONSIDER_MODEL_ORDER_COMPONENTS
      ComponentOrderingStrategy.modelOrder) }
    for (i, o) in #[((0 : Nat), (5 : Int)), (3, 7), (1, 2), (4, 9)] do
      LayeredM.modifyNode s.nodes[i]! fun x => { x with internal := { x.internal with modelOrder := some o } }
    return (s, ← ComponentsProcessor.split s.graph))
  checkEq "model order sort: [n1 n4], [n0 n3 n2], [n5]"
    (comps3.map fun c => (a3.graph c).layerlessNodes) #[#[s3.nodes[1]!, s3.nodes[4]!],
      #[s3.nodes[0]!, s3.nodes[3]!, s3.nodes[2]!], #[s3.nodes[5]!]]

/-- A graph with external ports: `x → d` (`d` an external port dummy on the EAST side, at
`(100, 5)`) and an isolated node `y`; `x` at `(1, 1)`, `y` at `(2, 3)`. -/
def buildExternal (constraints : PortConstraints) : LayeredM (LGraphId × LNodeId × LNodeId × LNodeId) := do
  let g ← LayeredM.createGraph {
    props := ({} : PropertyMap).set CoreOptions.PORT_CONSTRAINTS constraints,
    internal := { graphProperties := EnumSet.of #[.externalPorts] } }
  let x ← LayeredM.createNode g { size := ⟨10.0, 10.0⟩, position := ⟨1.0, 1.0⟩ }
  let d ← LayeredM.createNode g { type := .externalPort, position := ⟨100.0, 5.0⟩ }
  LayeredM.modifyNode d fun nd => { nd with internal := { nd.internal with extPortSide := .east } }
  let y ← LayeredM.createNode g { size := ⟨10.0, 10.0⟩, position := ⟨2.0, 3.0⟩ }
  LayeredM.modifyGraph g fun gr => { gr with layerlessNodes := #[x, d, y] }
  let px ← mkPort x
  let pd ← mkPort d
  let e ← LayeredM.createEdge
  LayeredM.setEdgeSource e (some px)
  LayeredM.setEdgeTarget e (some pd)
  return (g, x, d, y)

def externalSplitTests : Suite := suite "layered.components.split.externalPorts" do
  let (((_, x, d, y), comps), a) ← LayeredM.run (do
    let r ← buildExternal .free
    return (r, ← ComponentsProcessor.split r.1))
  checkEq "free external ports: two components" comps.size 2
  checkEq "component with the external port dummy" (a.graph comps[0]!).layerlessNodes #[x, d]
  checkEq "external port connections {EAST}" (a.graph comps[0]!).internal.extPortConnections.toArray #[.east]
  checkEq "isolated component without connections" (a.graph comps[1]!).internal.extPortConnections.toArray #[]
  checkEq "isolated component [y]" (a.graph comps[1]!).layerlessNodes #[y]
  let (((g2, _, _, _), comps2), _) ← LayeredM.run (do
    let r ← buildExternal .fixedOrder
    return (r, ← ComponentsProcessor.split r.1))
  checkEq "order-fixed external ports block the split" comps2 #[g2]
  let (((g3, _, _, _), comps3), _) ← LayeredM.run (do
    let r ← buildExternal .fixedPos
    return (r, ← ComponentsProcessor.split r.1))
  checkEq "FIXED_POS external ports block the split" comps3 #[g3]

/-! ## `combine` -/

def combineSimpleRowTests : Suite := suite "layered.components.combine.simpleRow" do
  let ((s, comps), a) ← LayeredM.run (do
    let s ← buildSample
    let comps ← ComponentsProcessor.split s.graph
    -- hand-set "layout" results
    for (n, pos) in #[(s.nodes[5]!, (⟨1.0, 2.0⟩ : KVector)), (s.nodes[1]!, ⟨3.0, 4.0⟩), (s.nodes[0]!, ⟨5.0, 6.0⟩)] do
      LayeredM.modifyNode n fun x => { x with position := pos }
    LayeredM.modifyGraph comps[0]! fun g => { g with size := ⟨100.0, 50.0⟩ }
    LayeredM.modifyGraph comps[1]! fun g => { g with size := ⟨60.0, 40.0⟩, offset := ⟨5.0, 5.0⟩ }
    LayeredM.modifyGraph comps[2]! fun g => { g with size := ⟨30.0, 30.0⟩ }
    ComponentsProcessor.combine comps s.graph
    return (s, comps))
  let n := s.nodes
  -- hand: order by area [comp2 (900), comp1 (2400), comp0 (5000)];
  -- max row width = max(100, sqrt(8300) * 1.6 = 145.77); comp2 at (0,0), comp1 at (50,0) (+ own
  -- offset (5,5)), comp0 does not fit (130 + 100 > 145.77): new row at (0, 40 + 20 = 60)
  checkEq "target layerless order [n5, n1, n4, n0, n3, n2]" (a.graph s.graph).layerlessNodes
    #[n[5]!, n[1]!, n[4]!, n[0]!, n[3]!, n[2]!]
  checkEqR "n5 stays at (1,2)" (a.node n[5]!).position ⟨1.0, 2.0⟩
  checkEqR "n1 moved by (50 + 5, 0 + 5)" (a.node n[1]!).position ⟨58.0, 9.0⟩
  checkEqR "n0 moved to the second row (0, 60)" (a.node n[0]!).position ⟨5.0, 66.0⟩
  checkEqR "bend point of e0 moved" (a.edge s.edges[0]!).bendPoints #[⟨10.0, 70.0⟩]
  checkEqR "junction point of e0 moved" ((a.edge s.edges[0]!).props.getD CoreOptions.JUNCTION_POINTS #[]) #[⟨1.0, 61.0⟩]
  checkEqR "edge label moved" (a.label s.labels[0]!).position ⟨2.0, 62.0⟩
  -- hand: broadest row max(20, 30, 110, 100) = 110, height 60 + 50
  checkEqR "target size (110, 110)" (a.graph s.graph).size ⟨110.0, 110.0⟩
  checkEqR "component offsets reset" (a.graph comps[1]!).offset ⟨0.0, 0.0⟩
  checkEq "nodes moved back to the target graph" (a.nodeGraph n[3]!) (some s.graph)
  -- single component: moved without placement (hand: n1 at (1, 0) + component offset (1, 1))
  let ((s1, target), a1) ← LayeredM.run (do
    let s ← buildSample
    let comps ← ComponentsProcessor.split s.graph
    let target ← LayeredM.createGraph
    LayeredM.modifyGraph comps[1]! fun g => { g with size := ⟨7.0, 8.0⟩, offset := ⟨1.0, 1.0⟩ }
    ComponentsProcessor.combine #[comps[1]!] target
    return (s, target))
  checkEq "single component: nodes moved into the target" (a1.graph target).layerlessNodes #[s1.nodes[1]!, s1.nodes[4]!]
  checkEqR "single component: graph offset applied" (a1.node s1.nodes[1]!).position ⟨2.0, 1.0⟩
  checkEqR "single component: size copied" (a1.graph target).size ⟨7.0, 8.0⟩
  checkEqR "single component: padding copied" (a1.graph target).padding ⟨1.0, 2.0, 3.0, 4.0⟩
  checkFloat "single component: options copied" ((a1.graph target).props.getD CoreOptions.SPACING_NODE_NODE 0.0) 33.0

def combineGroupTests : Suite := suite "layered.components.combine.componentGroup" do
  let ((g, x, d, y), a) ← LayeredM.run (do
    let r ← buildExternal .free
    let comps ← ComponentsProcessor.split r.1
    LayeredM.modifyGraph comps[0]! fun gr => { gr with size := ⟨50.0, 30.0⟩ }
    LayeredM.modifyGraph comps[1]! fun gr => { gr with size := ⟨40.0, 20.0⟩ }
    ComponentsProcessor.combine comps r.1
    return r)
  -- hand: one group {EAST: [A = x d], NONE: [B = y]}; sector c: B row-placed at (0,0), size (60, 40);
  -- sector e: A vertically, size (70, 50); columns mid 60 / right 70, row mid 50; A offset by (60, 0);
  -- group size (130, 50); target size (130 - 20, 50 - 20)
  checkEq "nodes moved in group order [x, d, y]" (a.graph g).layerlessNodes #[x, d, y]
  checkEqR "EAST component moved right of the centre sector" (a.node x).position ⟨61.0, 1.0⟩
  checkEqR "external port dummy moved with its component" (a.node d).position ⟨160.0, 5.0⟩
  checkEqR "centre component stays" (a.node y).position ⟨2.0, 3.0⟩
  checkEqR "target size (110, 30)" (a.graph g).size ⟨110.0, 30.0⟩
  -- model order row placer (CONSIDER_MODEL_ORDER_COMPONENTS = MODEL_ORDER)
  let ((g2, x2, _, y2), a2) ← LayeredM.run (do
    let r ← buildExternal .free
    LayeredM.setGraphProp r.1 LayeredOptions.CONSIDER_MODEL_ORDER_COMPONENTS ComponentOrderingStrategy.modelOrder
    let comps ← ComponentsProcessor.split r.1
    LayeredM.modifyGraph comps[0]! fun gr => { gr with size := ⟨50.0, 30.0⟩ }
    LayeredM.modifyGraph comps[1]! fun gr => { gr with size := ⟨40.0, 20.0⟩ }
    ComponentsProcessor.combine comps r.1
    return r)
  -- hand: no model orders (keys all MAX) keep the split order; max row width
  -- max(50, sqrt(2300) * 1.6 = 76.7); A {EAST} at (0,0); B follows an EAST component: new row at
  -- (0, 30 + 20); size (max(20, 50, 40), 50 + 20)
  checkEqR "model order row: first component stays" (a2.node x2).position ⟨1.0, 1.0⟩
  checkEqR "model order row: component after EAST starts a new row" (a2.node y2).position ⟨2.0, 53.0⟩
  checkEqR "model order row: target size (50, 70)" (a2.graph g2).size ⟨50.0, 70.0⟩

/-- Ports of the Rust unit tests of `components_processor.rs`. -/
def processorUnitTests : Suite := suite "layered.components.processor.rustUnit" do
  -- sort_components_by_priority_keeps_input_order_for_ties
  let ((first, second, sorted), _) ← LayeredM.run (do
    let target ← LayeredM.createGraph
    let first ← LayeredM.createGraph { size := ⟨10.0, 10.0⟩ }
    let second ← LayeredM.createGraph { size := ⟨10.0, 10.0⟩ }
    let n1 ← LayeredM.createNode first
    let n2 ← LayeredM.createNode second
    LayeredM.modifyGraph first fun g => { g with layerlessNodes := #[n1] }
    LayeredM.modifyGraph second fun g => { g with layerlessNodes := #[n2] }
    let sorted ← SimpleRowGraphPlacer.sortComponentsByPriority #[first, second] target
    return (first, second, sorted))
  checkEq "sort_components_by_priority_keeps_input_order_for_ties" sorted #[first, second]
  -- single_external_component_uses_group_placement
  let (target, a) ← LayeredM.run (do
    let mk (ext : EnumSet PortSide) : LayeredM LGraphId := LayeredM.createGraph {
      props := ({} : PropertyMap).set LayeredOptions.SPACING_COMPONENT_COMPONENT 20.0,
      internal := { graphProperties := EnumSet.of #[.externalPorts], extPortConnections := ext } }
    let source ← mk SIDES_EAST_WEST
    let target ← mk SIDES_NONE
    -- A zero-width passthrough still needs the group's spacing subtraction.
    ComponentsProcessor.combine #[source] target
    return target)
  checkEqR "single_external_component_uses_group_placement" (a.graph target).size ⟨-20.0, 0.0⟩

/-- Builds two single-node components (A with `PRIORITY` 1 and component size 60 x 10, B with
10 x 10), placed in one row (`ASPECT_RATIO` 100), optionally compacted. -/
def runCompactionCase (compact : Bool) : IO ((LGraphId × LNodeId × LNodeId) × LGraphArena) := LayeredM.run (do
  let g ← LayeredM.createGraph {
    props := (({} : PropertyMap).set CoreOptions.ASPECT_RATIO 100.0).set
      LayeredOptions.COMPACTION_CONNECTED_COMPONENTS compact }
  let na ← LayeredM.createNode g { size := ⟨10.0, 10.0⟩ }
  let nb ← LayeredM.createNode g { size := ⟨10.0, 10.0⟩ }
  LayeredM.setNodeProp na CoreOptions.PRIORITY 1
  LayeredM.modifyGraph g fun x => { x with layerlessNodes := #[nb, na] }
  let comps ← ComponentsProcessor.split g
  for c in comps do
    let isA := (← LayeredM.getGraph c).layerlessNodes == #[na]
    LayeredM.modifyGraph c fun x => { x with size := if isA then ⟨60.0, 10.0⟩ else ⟨10.0, 10.0⟩ }
  ComponentsProcessor.combine comps g
  return (g, na, nb))

def compactionTests : Suite := suite "layered.components.compaction" do
  -- hand: priority order [A, B]; A at x = 0, B at x = 60 + 20; broadest row 90
  let ((g0, a0, b0), ar0) ← runCompactionCase false
  checkEqR "without compaction: B placed after A's component box" (ar0.node b0).position ⟨80.0, 0.0⟩
  checkEqR "without compaction: A at the origin" (ar0.node a0).position ⟨0.0, 0.0⟩
  checkEqR "without compaction: target size (90, 10)" (ar0.graph g0).size ⟨90.0, 10.0⟩
  -- hand: the hulls are the 10 x 10 nodes; LEFT compaction moves B to 10 + 20; size (40, 10)
  let ((g1, a1, b1), ar1) ← runCompactionCase true
  checkEqR "compaction moves B next to A" (ar1.node b1).position ⟨30.0, 0.0⟩
  checkEqR "compaction keeps A" (ar1.node a1).position ⟨0.0, 0.0⟩
  checkEqR "compacted target size (40, 10)" (ar1.graph g1).size ⟨40.0, 10.0⟩
  checkEq "target layerless order [A, B]" (ar1.graph g1).layerlessNodes #[a1, b1]

/-- elk-rs `tests/compaction/compaction_test.rs` runs a full layered layout of five 40 x 30 nodes
(`n1, n2 → n3 → n4, n5`) for ten option combinations and checks finite coordinates and positive
sizes. The layered pipeline is not ported yet (TODO: switch to the real layout once
`ElkLayered` exists); this adaptation runs the components part of that pipeline (`split` +
`combine`) on the same graph with hand-set node positions and the same options. -/
def compactionCases : Suite := suite "layered.components.compactionTestRs" do
  let cases : Array (String × GraphCompactionStrategy × ConstraintCalculationStrategy × EdgeRouting × Bool) := #[
    ("compaction_none_orthogonal_scanline", .none, .scanline, .orthogonal, false),
    ("compaction_left_orthogonal_scanline", .left, .scanline, .orthogonal, false),
    ("compaction_right_orthogonal_scanline", .right, .scanline, .orthogonal, false),
    ("compaction_left_right_constraint_locking_orthogonal_quadratic", .leftRightConstraintLocking, .quadratic,
      .orthogonal, false),
    ("compaction_left_right_connection_locking_orthogonal_scanline", .leftRightConnectionLocking, .scanline,
      .orthogonal, false),
    ("compaction_edge_length_orthogonal_scanline", .edgeLength, .scanline, .orthogonal, false),
    ("compaction_left_splines_quadratic", .left, .quadratic, .splines, false),
    ("compaction_right_splines_scanline", .right, .scanline, .splines, false),
    ("compaction_polyline_left_does_not_fail", .left, .scanline, .polyline, false),
    ("compaction_connected_components_enabled", .leftRightConstraintLocking, .quadratic, .orthogonal, true)]
  for (name, strategy, constraints, routing, connected) in cases do
    let (nodes, a) ← LayeredM.run (do
      let g ← LayeredM.createGraph {
        props := ((((({} : PropertyMap).set LayeredOptions.COMPACTION_POST_COMPACTION_STRATEGY strategy).set
          LayeredOptions.COMPACTION_POST_COMPACTION_CONSTRAINTS constraints).set LayeredOptions.EDGE_ROUTING routing).set
          LayeredOptions.COMPACTION_CONNECTED_COMPONENTS connected) }
      let positions : Array KVector := #[⟨0.0, 0.0⟩, ⟨0.0, 50.0⟩, ⟨100.0, 25.0⟩, ⟨200.0, 0.0⟩, ⟨200.0, 50.0⟩]
      let mut nodes : Array LNodeId := #[]
      for p in positions do
        nodes := nodes.push (← LayeredM.createNode g { size := ⟨40.0, 30.0⟩, position := p })
      let all := nodes
      LayeredM.modifyGraph g fun x => { x with layerlessNodes := all }
      for (s, t) in #[((0 : Nat), (2 : Nat)), (1, 2), (2, 3), (2, 4)] do
        let ps ← mkPort nodes[s]!
        let pt ← mkPort nodes[t]!
        let e ← LayeredM.createEdge
        LayeredM.setEdgeSource e (some ps)
        LayeredM.setEdgeTarget e (some pt)
      let comps ← ComponentsProcessor.split g
      for c in comps do LayeredM.modifyGraph c fun x => { x with size := ⟨240.0, 80.0⟩ }
      ComponentsProcessor.combine comps g
      return nodes)
    let ok := nodes.all fun n =>
      let nd := a.node n
      nd.position.x.isFinite && nd.position.y.isFinite && nd.size.x > 0.0 && nd.size.y > 0.0
    check name ok

def suites : Array Suite :=
  #[componentGroupTests, splitTests, externalSplitTests, combineSimpleRowTests, combineGroupTests,
    processorUnitTests, compactionTests, compactionCases]

end Tests.Layered.Components
