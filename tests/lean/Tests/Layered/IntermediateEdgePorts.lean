import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Intermediate.EdgePortProcessors
/-!
Tests of the layered intermediate processors of task I6 (long edges, hyperedges, north/south ports,
port sides and order, reversed edges). The elk-rs tests (`tests/intermediate/*_test.rs`) build small
layered graphs by hand; they are ported with their assertions (Rust test names in the check names)
and extended with hand-derived expectations ("hand: …").
-/
namespace Tests.Layered.IntermediateEdgePorts

open Tests Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM
open Elk (ElkEnum)

/-! ## Graph builders -/

/-- A graph with `n` empty layers. -/
def mkGraph (n : Nat) : LayeredM (LGraphId × Array LayerId) := do
  let g ← createGraph
  let mut layers : Array LayerId := #[]
  for _ in [0:n] do
    layers := layers.push (← createLayer g)
  let ls := layers
  modifyGraph g fun x => { x with layers := ls }
  return (g, layers)

/-- `add_node`: a node of `g` appended to `layer`. -/
def addNode (g : LGraphId) (layer : LayerId) (n : LNode := {}) : LayeredM LNodeId := do
  let node ← createNode g n
  setNodeLayer node (some layer)
  return node

/-- `add_port`: a port on `side` at `pos` (side set before the position, as in the Rust tests). -/
def addPort (node : LNodeId) (side : PortSide) (pos : KVector := {}) : LayeredM LPortId := do
  let p ← LayeredM.createPort
  modifyPort p fun pt => { (pt.setSide side) with position := pos }
  setPortNode p (some node)
  return p

/-- `connect`: a new edge from `s` to `t`. -/
def connect (s t : LPortId) : LayeredM LEdgeId := do
  let e ← createEdge
  setEdgeSource e (some s)
  setEdgeTarget e (some t)
  return e

/-- Runs a processor with a null monitor. -/
def runP (p : LayeredProcessor) (g : LGraphId) : LayeredM Unit := p.process g ProgressMonitor.null

/-- The nodes of the `i`-th layer. -/
def layerNodes (a : LGraphArena) (g : LGraphId) (i : Nat) : Array LNodeId :=
  (a.layer (a.graph g).layers[i]!).nodes

/-- The owner node of an edge's source / target port. -/
def sourceNode (a : LGraphArena) (e : LEdgeId) : Option LNodeId := (a.edge e).source.bind fun p => (a.port p).owner
def targetNode (a : LGraphArena) (e : LEdgeId) : Option LNodeId := (a.edge e).target.bind fun p => (a.port p).owner

/-! ## Registration -/

def registrationTests : Suite := suite "layered.intermediate.edgePorts.registration" do
  for (s, name) in #[(IntermediateProcessorStrategy.longEdgeSplitter, "LongEdgeSplitter"),
      (.longEdgeJoiner, "LongEdgeJoiner"), (.hyperedgeDummyMerger, "HyperedgeDummyMerger"),
      (.hypernodeProcessor, "HypernodeProcessor"), (.northSouthPortPreprocessor, "NorthSouthPortPreprocessor"),
      (.northSouthPortPostprocessor, "NorthSouthPortPostprocessor"), (.invertedPortProcessor, "InvertedPortProcessor"),
      (.portSideProcessor, "PortSideProcessor"), (.portListSorter, "PortListSorter"),
      (.reversedEdgeRestorer, "ReversedEdgeRestorer")] do
    check s!"{ElkEnum.javaName s} registered" (← IntermediateProcessorStrategy.isAvailable s)
    checkEq s!"{ElkEnum.javaName s} name" (← IntermediateProcessorStrategy.create s).name name

/-! ## LongEdgeSplitter / LongEdgeJoiner -/

/-- Four layers; one edge from layer 0 to layer 3 with a thickness, junction points, a center and a
head label and `MODEL_ORDER = 5`. Returns graph, layers, ports `[source, target]`, the edge and the
labels `[center, head]`. -/
def splitFixture (thickness : Float := 3.0) :
    LayeredM (LGraphId × Array LayerId × Array LPortId × LEdgeId × Array LLabelId) := do
  let (g, layers) ← mkGraph 4
  let source ← addNode g layers[0]!
  let target ← addNode g layers[3]!
  let sp ← addPort source .east
  let tp ← addPort target .west
  let e ← connect sp tp
  let cl ← createLabel "center"
  let hl ← createLabel "head"
  setLabelProp hl CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.head
  modifyEdge e fun ed => { ed with
    labels := #[cl, hl],
    props := (ed.props.set CoreOptions.EDGE_THICKNESS thickness).set CoreOptions.JUNCTION_POINTS #[⟨1, 1⟩],
    internal := { ed.internal with modelOrder := some 5 } }
  return (g, layers, #[sp, tp], e, #[cl, hl])

/-- The edge leaving the eastern (second) port of a long edge dummy. -/
def dummyOutEdge (a : LGraphArena) (dummy : LNodeId) : LEdgeId := (a.port (a.node dummy).ports[1]!).outgoingEdges[0]!

def splitterTests : Suite := suite "layered.intermediate.LongEdgeSplitter" do
  let ((g, _, ports, e, labels), a) ← LayeredM.run (do
      let r ← splitFixture
      runP LongEdgeSplitter.processor r.1
      return r)
  let sp := ports[0]!; let tp := ports[1]!
  -- long_edge_splitter_makes_edges_connect_adjacent_layers
  let mut adjacent := true
  for i in [0:4] do
    for n in layerNodes a g i do
      for out in a.nodeOutgoingEdges n do
        let some t := targetNode a out | adjacent := false
        if (a.node t).layer != (a.graph g).layers[i + 1]? then adjacent := false
  check "long_edge_splitter_makes_edges_connect_adjacent_layers" adjacent
  -- long_edge_splitter_inserts_long_edge_dummy_nodes
  check "long_edge_splitter_inserts_long_edge_dummy_nodes"
    ((layerNodes a g 1).any fun n => (a.node n).type == .longEdge)
  checkEq "hand: one dummy in layer 1" (layerNodes a g 1).size 1
  checkEq "hand: one dummy in layer 2" (layerNodes a g 2).size 1
  let d1 := (layerNodes a g 1)[0]!
  let d2 := (layerNodes a g 2)[0]!
  checkEq "dummy 2 type" (a.node d2).type NodeType.longEdge
  checkEq "dummy 1 LONG_EDGE_SOURCE" (a.node d1).internal.longEdgeSource (some sp)
  checkEq "dummy 1 LONG_EDGE_TARGET" (a.node d1).internal.longEdgeTarget (some tp)
  checkEq "hand: dummy 2 copies LONG_EDGE_SOURCE from dummy 1" (a.node d2).internal.longEdgeSource (some sp)
  checkEq "hand: dummy 2 copies LONG_EDGE_TARGET from dummy 1" (a.node d2).internal.longEdgeTarget (some tp)
  checkEqR "dummy 1 ORIGIN = original edge" (a.node d1).internal.origin (some (Origin.lEdge e))
  checkEq "dummy PORT_CONSTRAINTS FIXED_POS"
    ((a.node d1).props.getD CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined) PortConstraints.fixedPos
  checkFloat "hand: dummy height = edge thickness 3" (a.node d1).size.y 3.0
  checkEq "dummy port sides [WEST, EAST]" ((a.node d1).ports.map fun p => (a.port p).side) #[PortSide.west, .east]
  checkFloat "hand: dummy port y = floor(3 / 2) = 1" (a.port (a.node d1).ports[0]!).position.y 1.0
  checkEq "original edge keeps its source" (a.edge e).source (some sp)
  checkEq "original edge ends at dummy 1" (a.edge e).target (a.node d1).ports[0]?
  let de1 := dummyOutEdge a d1
  let de2 := dummyOutEdge a d2
  checkEq "dummy edge 1 ends at dummy 2" (a.edge de1).target (a.node d2).ports[0]?
  checkEq "dummy edge 2 ends at the original target" (a.edge de2).target (some tp)
  checkEq "target port incoming = [dummy edge 2]" (a.port tp).incomingEdges #[de2]
  checkEqR "dummy 2 ORIGIN = dummy edge 1" (a.node d2).internal.origin (some (Origin.lEdge de1))
  check "original edge keeps JUNCTION_POINTS" ((a.edge e).props.has CoreOptions.JUNCTION_POINTS)
  check "dummy edges drop JUNCTION_POINTS"
    (!(a.edge de1).props.has CoreOptions.JUNCTION_POINTS && !(a.edge de2).props.has CoreOptions.JUNCTION_POINTS)
  checkFloat "dummy edge copies EDGE_THICKNESS" ((a.edge de2).props.getD CoreOptions.EDGE_THICKNESS 0.0) 3.0
  checkEq "dummy edge copies internal MODEL_ORDER" (a.edge de1).internal.modelOrder (some 5)
  checkEq "hand: center label stays on the original edge" (a.edge e).labels #[labels[0]!]
  checkEq "hand: head label moved to the last dummy edge" (a.edge de2).labels #[labels[1]!]
  checkEq "hand: head label END_LABEL_EDGE = original edge (kept on the second move)"
    (a.label labels[1]!).internal.endLabelEdge (some e)
  checkEq "hand: 3 edges in total" a.edges.size 3
  -- negative thickness is clamped to 0 and written back
  let ((g2, _, _, e2, _), a2) ← LayeredM.run (do
      let r ← splitFixture (-2.0)
      runP LongEdgeSplitter.processor r.1
      return r)
  let d := (layerNodes a2 g2 1)[0]!
  checkFloat "hand: negative thickness written back as 0" ((a2.edge e2).props.getD CoreOptions.EDGE_THICKNESS 1.0) 0.0
  checkFloat "hand: dummy height 0 for negative thickness" (a2.node d).size.y 0.0
  -- at most two layers: nothing is split (even edges spanning backwards)
  let (g3, a3) ← LayeredM.run (do
      let (g, layers) ← mkGraph 2
      let s ← addNode g layers[1]!
      let t ← addNode g layers[0]!
      let _ ← connect (← addPort s .east) (← addPort t .west)
      runP LongEdgeSplitter.processor g
      return g)
  checkEq "hand: at most two layers: nothing is split" ((layerNodes a3 g3 0).size + (layerNodes a3 g3 1).size) 2

/-- Splits the fixture, emulates routing (bend points, dummy positions, a junction point on the last
dummy edge) and joins. Returns graph, ports, the original edge, the dummies, the dummy edges and
the labels. -/
def joinFixture (unnecessaryBendpoints : Bool) :
    LayeredM (LGraphId × Array LPortId × LEdgeId × Array LNodeId × Array LEdgeId × Array LLabelId) := do
  let (g, _, ports, e, labels) ← splitFixture
  runP LongEdgeSplitter.processor g
  let d1 := (← getLayer (← getGraph g).layers[1]!).nodes[0]!
  let d2 := (← getLayer (← getGraph g).layers[2]!).nodes[0]!
  let de1 ← withArena (dummyOutEdge · d1)
  let de2 ← withArena (dummyOutEdge · d2)
  modifyEdge e fun x => { x with bendPoints := #[⟨10, 0⟩] }
  modifyEdge de1 fun x => { x with bendPoints := #[⟨20, 0⟩] }
  modifyEdge de2 fun x => { x with bendPoints := #[⟨30, 0⟩], props := x.props.set CoreOptions.JUNCTION_POINTS #[⟨2, 2⟩] }
  modifyNode d1 fun x => { x with position := ⟨15, 5⟩ }
  modifyNode d2 fun x => { x with position := ⟨25, 5⟩ }
  if unnecessaryBendpoints then setGraphProp g LayeredOptions.UNNECESSARY_BENDPOINTS true
  runP LongEdgeJoiner.processor g
  return (g, ports, e, #[d1, d2], #[de1, de2], labels)

def joinerTests : Suite := suite "layered.intermediate.LongEdgeJoiner" do
  let ((g, ports, e, dummies, dummyEdges, labels), a) ← LayeredM.run (joinFixture false)
  -- long_edge_joiner_removes_long_edge_dummy_nodes
  let mut noDummies := true
  for i in [0:4] do
    for n in layerNodes a g i do
      if (a.node n).type == .longEdge then noDummies := false
  check "long_edge_joiner_removes_long_edge_dummy_nodes" noDummies
  checkEq "joined dummies have no layer" (dummies.map fun d => (a.node d).layer) #[none, none]
  checkEq "original edge restored: source" (a.edge e).source (some ports[0]!)
  checkEq "original edge restored: target" (a.edge e).target (some ports[1]!)
  checkEq "target port incoming = [original edge]" (a.port ports[1]!).incomingEdges #[e]
  checkEq "hand: bend points joined in chain order" (a.edge e).bendPoints #[⟨10, 0⟩, ⟨20, 0⟩, ⟨30, 0⟩]
  checkEq "dropped edges disconnected"
    (dummyEdges.map fun x => ((a.edge x).source, (a.edge x).target)) #[(none, none), (none, none)]
  checkEq "hand: labels collected (center, then head from the last edge)" (a.edge e).labels labels
  checkEq "hand: junction points appended" ((a.edge e).props.get CoreOptions.JUNCTION_POINTS) (some #[⟨1, 1⟩, ⟨2, 2⟩])
  -- with UNNECESSARY_BENDPOINTS the dummies' first port anchors (15 + 0, 5 + 1) / (25, 6) are added
  let ((_, _, e', _, _, _), a') ← LayeredM.run (joinFixture true)
  checkEq "hand: UNNECESSARY_BENDPOINTS adds the dummy positions as bend points" (a'.edge e').bendPoints
    #[⟨10, 0⟩, ⟨15, 6⟩, ⟨20, 0⟩, ⟨25, 6⟩, ⟨30, 0⟩]

/-! ## HyperedgeDummyMerger -/

/-- Three layers; edges `s → t1` and `s2 → t2` (`s2 = s` when `shared`), split by the splitter. -/
def hyperFixture (shared : Bool) : LayeredM (LGraphId × Array LPortId × Array LEdgeId) := do
  let (g, layers) ← mkGraph 3
  let s ← addNode g layers[0]!
  let ps ← addPort s .east
  let ps2 ← if shared then pure ps else do
    let s2 ← addNode g layers[0]!
    addPort s2 .east
  let pt1 ← addPort (← addNode g layers[2]!) .west
  let pt2 ← addPort (← addNode g layers[2]!) .west
  let e1 ← connect ps pt1
  let e2 ← connect ps2 pt2
  runP LongEdgeSplitter.processor g
  return (g, #[ps, pt1, pt2], #[e1, e2])

def mergerTests : Suite := suite "layered.intermediate.HyperedgeDummyMerger" do
  let ((g, ports, edges, dummies), a) ← LayeredM.run (do
      let (g, ports, edges) ← hyperFixture true
      let dummies := (← getLayer (← getGraph g).layers[1]!).nodes
      runP HyperedgeDummyMerger.processor g
      return (g, ports, edges, dummies))
  checkEq "hand: splitter created two dummies in layer 1" dummies.size 2
  let d1 := dummies[0]!; let d2 := dummies[1]!
  checkEq "hand: same hyperedge, same source: merged into the first dummy" (layerNodes a g 1) #[d1]
  checkEq "merged node removed (layer none)" (a.node d2).layer none
  checkEq "merge target input collects both edges" (a.port (a.node d1).ports[0]!).incomingEdges edges
  checkEq "merge target output has two edges" (a.port (a.node d1).ports[1]!).outgoingEdges.size 2
  check "merged node has no edges left" ((a.node d2).ports.all fun p => (a.port p).degree == 0)
  checkEq "shared LONG_EDGE_SOURCE kept" (a.node d1).internal.longEdgeSource (some ports[0]!)
  checkEq "different LONG_EDGE_TARGET cleared" (a.node d1).internal.longEdgeTarget none
  -- joining afterwards restores both edges (pairs by index)
  let ((), a2) ← LayeredM.run (runP LongEdgeJoiner.processor g) a
  checkEq "hand: joined edge 1 ends at t1" (a2.edge edges[0]!).target (some ports[1]!)
  checkEq "hand: joined edge 2 ends at t2" (a2.edge edges[1]!).target (some ports[2]!)
  -- different sources: different hyperedges, no merge
  let ((g3, _, _), a3) ← LayeredM.run (do
      let r ← hyperFixture false
      runP HyperedgeDummyMerger.processor r.1
      return r)
  checkEq "hand: different hyperedges are not merged" (layerNodes a3 g3 1).size 2
  -- label dummies: merging on the same source requires both dummies before their label dummies
  -- hand: layer [port owner, d1, d2]; merged → 2 nodes, not merged → 3
  for (beforeOther, expected) in #[(true, 2), (false, 3)] do
    let ((g4, _), a4) ← LayeredM.run (do
        let (g, layers) ← mkGraph 1
        let p ← addPort (← addNode g layers[0]!) .east
        let mut ds : Array LNodeId := #[]
        for before in #[true, beforeOther] do
          let d ← addNode g layers[0]! { type := .longEdge }
          let _ ← addPort d .west
          let _ ← addPort d .east
          modifyNode d fun x => { x with internal := { x.internal with
            longEdgeSource := some p, longEdgeHasLabelDummies := true, longEdgeBeforeLabelDummy := before } }
          ds := ds.push d
        runP HyperedgeDummyMerger.processor g
        return (g, ds))
    checkEq s!"hand: label dummies, second before label dummy = {beforeOther}: layer size" (layerNodes a4 g4 0).size expected

/-! ## HypernodeProcessor -/

def hypernodeTests : Suite := suite "layered.intermediate.HypernodeProcessor" do
  -- moves_hypernode_to_first_join_point_and_rewrites_source_port
  let ((hypernode, sourcePort, edge), a) ← LayeredM.run (do
      let (g, layers) ← mkGraph 1
      modifyGraph g fun x => { x with size := { x.size with x := 220 } }
      let hypernode ← addNode g layers[0]! { position := ⟨10, 20⟩, size := ⟨20, 20⟩ }
      setNodeProp hypernode CoreOptions.HYPERNODE true
      let sourcePort ← addPort hypernode .east ⟨20, 10⟩
      let target ← addNode g layers[0]! { position := ⟨160, 80⟩, size := ⟨20, 20⟩ }
      let targetPort ← addPort target .west ⟨0, 10⟩
      let edge ← connect sourcePort targetPort
      modifyEdge edge fun x => { x with
        bendPoints := #[⟨100, 100⟩, ⟨130, 140⟩],
        props := x.props.set CoreOptions.JUNCTION_POINTS #[⟨100, 100⟩, ⟨170, 140⟩] }
      runP HypernodeProcessor.processor g
      return (hypernode, sourcePort, edge))
  checkFloat "moves_hypernode: x = 100 - 20 / 2" (a.node hypernode).position.x 90.0
  checkEq "moves_hypernode: two ports added" (a.node hypernode).ports.size 3
  let some newSource := (a.edge edge).source | check "edge source exists" false
  check "moves_hypernode: source port rewritten" (newSource != sourcePort)
  checkEq "hand: next point (130, 140) below (100, 100): south port" (a.port newSource).side PortSide.south
  checkEq "hand: south port at (width / 2, height)" (a.port newSource).position ⟨10, 20⟩
  checkEq "moves_hypernode: first bend point removed" (a.edge edge).bendPoints #[⟨130, 140⟩]
  checkEq "moves_hypernode: junction point removed" ((a.edge edge).props.get CoreOptions.JUNCTION_POINTS)
    (some #[⟨170, 140⟩])
  -- left branch: Java starts bendX at Integer.MAX_VALUE, so no incoming edge qualifies
  let ((hn, _), a2) ← LayeredM.run (do
      let (g, layers) ← mkGraph 1
      let hn ← addNode g layers[0]! { position := ⟨10, 20⟩, size := ⟨20, 20⟩ }
      setNodeProp hn CoreOptions.HYPERNODE true
      let wp ← addPort hn .west ⟨0, 10⟩
      let src ← addPort (← addNode g layers[0]!) .east
      let e ← connect src wp
      modifyEdge e fun x => { x with bendPoints := #[⟨50, 30⟩, ⟨70, 100⟩] }
      runP HypernodeProcessor.processor g
      return (hn, e))
  checkEq "hand: left-moving hypernode stays (bendX starts at Integer.MAX_VALUE)" (a2.node hn).position ⟨10, 20⟩

/-! ## NorthSouthPortPreprocessor / NorthSouthPortPostprocessor -/

/-- Rust `build_north_south_fixture` (intermediate_processors_test.rs): `owner` (FIXED_SIDE) with a
north port fed by `other`'s east port and a south port feeding `other`'s west port, one layer.
Returns graph, nodes `[owner, other]`, ports `[north, south, otherEast, otherWest]`, edges
`[incoming, outgoing]`. -/
def nsFixture : LayeredM (LGraphId × Array LNodeId × Array LPortId × Array LEdgeId) := do
  let (g, layers) ← mkGraph 1
  let owner ← addNode g layers[0]! { position := ⟨20, 40⟩ }
  setNodeProp owner CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
  let north ← addPort owner .north ⟨5, -2⟩
  let south ← addPort owner .south ⟨7, 12⟩
  let other ← addNode g layers[0]! { position := ⟨100, 40⟩ }
  let otherEast ← addPort other .east ⟨0, 3⟩
  let otherWest ← addPort other .west ⟨0, 9⟩
  let incoming ← connect otherEast north
  let outgoing ← connect south otherWest
  return (g, #[owner, other], #[north, south, otherEast, otherWest], #[incoming, outgoing])

def nsPreTests : Suite := suite "layered.intermediate.NorthSouthPortPreprocessor" do
  let ((g, nodes, ports, edges), a) ← LayeredM.run (do
      let r ← nsFixture
      runP NorthSouthPortPreprocessor.processor r.1
      return r)
  let owner := nodes[0]!; let other := nodes[1]!
  let north := ports[0]!; let south := ports[1]!
  let layer := layerNodes a g 0
  -- north_south_preprocessor_creates_dummy_nodes_for_connected_ports
  checkEq "creates_dummy_nodes_for_connected_ports: 2 + 2 nodes" layer.size 4
  checkEq "creates_dummy_nodes: 2 north/south dummies"
    (layer.filter fun n => (a.node n).type == .northSouthPort).size 2
  let nd := layer[0]!; let sd := layer[2]!
  checkEq "hand: layer order [north dummy, owner, south dummy, other]" layer #[nd, owner, sd, other]
  -- north_south_preprocessor_isolates_north_south_ports
  check "isolates_north_south_ports" ((a.port north).degree == 0 && (a.port south).degree == 0)
  checkEq "incoming edge now ends at the north dummy" (targetNode a edges[0]!) (some nd)
  checkEq "outgoing edge now starts at the south dummy" (sourceNode a edges[1]!) (some sd)
  let ndPort := (a.node nd).ports[0]!
  checkEq "north dummy input port on WEST" (a.port ndPort).side PortSide.west
  checkEqR "north dummy port ORIGIN = north port" (a.port ndPort).internal.origin (some (Origin.lPort north))
  checkEq "south dummy output port on EAST" (a.port (a.node sd).ports[0]!).side PortSide.east
  checkEq "PORT_DUMMY of the north port" (a.port north).internal.portDummy (some nd)
  checkEq "PORT_DUMMY of the south port" (a.port south).internal.portDummy (some sd)
  checkEqR "dummy ORIGIN = owner node" (a.node nd).internal.origin (some (Origin.lNode owner))
  -- north_south_preprocessor_sets_layout_unit_and_barycenter_associates
  checkEq "sets_layout_unit_and_barycenter_associates: associates" (a.node owner).internal.barycenterAssociates #[nd, sd]
  checkEq "sets_layout_unit: dummies' unit is the owner"
    #[(a.node nd).internal.inLayerLayoutUnit, (a.node sd).internal.inLayerLayoutUnit] #[some owner, some owner]
  checkEq "hand: owner is its own layout unit" (a.node owner).internal.inLayerLayoutUnit (some owner)
  checkEq "hand: north dummy must precede the owner" (a.node nd).internal.inLayerSuccessorConstraints #[owner]
  checkEq "hand: owner must precede the south dummy" (a.node owner).internal.inLayerSuccessorConstraints #[sd]
  checkEq "hand: other node (free ports) gets no layout unit" (a.node other).internal.inLayerLayoutUnit none
  check "owner port sides cached by sort_port_list" (a.node owner).portSidesCached
  -- north_south_preprocessor_skips_unconnected_ports
  let ((g2, _), a2) ← LayeredM.run (do
      let (g, layers) ← mkGraph 1
      let owner ← addNode g layers[0]!
      setNodeProp owner CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
      let _ ← addPort owner .north
      let _ ← addPort owner .south
      runP NorthSouthPortPreprocessor.processor g
      return (g, owner))
  checkEq "skips_unconnected_ports" (layerNodes a2 g2 0).size 1
  -- north_south_preprocessor_sets_layout_unit_for_fixed_side_node_without_north_south_ports
  let (owner3, a3) ← LayeredM.run (do
      let (g, layers) ← mkGraph 1
      let owner ← addNode g layers[0]!
      setNodeProp owner CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
      let _ ← addPort owner .east
      let _ ← addPort owner .west
      runP NorthSouthPortPreprocessor.processor g
      return owner)
  checkEq "sets_layout_unit_for_fixed_side_node_without_north_south_ports"
    (a3.node owner3).internal.inLayerLayoutUnit (some owner3)

/-- One north port with an incoming and an outgoing edge (one in/out dummy); `allowSwitch` sets
`ALLOW_NON_FLOW_PORTS_TO_SWITCH_SIDES` on the port. Returns graph, `[owner]`, `[port]`, edges. -/
def inOutFixture (allowSwitch : Bool) : LayeredM (LGraphId × LNodeId × LPortId × Array LEdgeId) := do
  let (g, layers) ← mkGraph 1
  let owner ← addNode g layers[0]!
  setNodeProp owner CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
  let pn ← addPort owner .north ⟨10, 0⟩
  if allowSwitch then setPortProp pn LayeredOptions.ALLOW_NON_FLOW_PORTS_TO_SWITCH_SIDES true
  let e1 ← connect (← addPort (← addNode g layers[0]!) .east) pn
  let e2 ← connect pn (← addPort (← addNode g layers[0]!) .west)
  runP NorthSouthPortPreprocessor.processor g
  return (g, owner, pn, #[e1, e2])

def nsSpecialTests : Suite := suite "layered.intermediate.NorthSouthPortPreprocessor.special" do
  -- in/out port: one dummy with a western and an eastern port of the same origin
  let ((g, owner, pn, _), a) ← LayeredM.run (inOutFixture false)
  let d := (layerNodes a g 0)[0]!
  checkEq "hand: in/out dummy first in the layer" (a.node d).type NodeType.northSouthPort
  checkEq "hand: in/out dummy port sides" ((a.node d).ports.map fun p => (a.port p).side) #[PortSide.west, .east]
  checkEq "hand: single-port owner keeps its (uncached) port list" ((a.node owner).ports, (a.node owner).portSidesCached) (#[pn], false)
  checkEq "hand: successor constraint without ALLOW_NON_FLOW_PORTS_TO_SWITCH_SIDES" (a.node d).internal.inLayerSuccessorConstraints #[owner]
  let ((g', _, _, _), a') ← LayeredM.run (inOutFixture true)
  checkEq "hand: no successor constraint when the origin port may switch sides"
    (a'.node (layerNodes a' g' 0)[0]!).internal.inLayerSuccessorConstraints #[]
  -- same-side self loop: sort_port_list puts the input-only north port first
  let ((g2, owner2, ps2, loop2), a2) ← LayeredM.run (do
      let (g, layers) ← mkGraph 1
      let owner ← addNode g layers[0]!
      setNodeProp owner CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
      let pA ← addPort owner .north
      let pB ← addPort owner .north
      let loop ← connect pA pB
      runP NorthSouthPortPreprocessor.processor g
      return (g, owner, #[pA, pB], loop))
  checkEq "hand: north ports sorted input-only (id 0) before output-only (id 4)" (a2.node owner2).ports #[ps2[1]!, ps2[0]!]
  let sd := (layerNodes a2 g2 0)[0]!
  checkEqR "hand: same-side self loop dummy ORIGIN = loop" (a2.node sd).internal.origin (some (Origin.lEdge loop2))
  checkEq "hand: same-side self loop disconnected" ((a2.edge loop2).source, (a2.edge loop2).target) (none, none)
  checkEq "hand: both loop ports know the dummy"
    (ps2.map fun p => (a2.port p).internal.portDummy) #[some sd, some sd]
  checkEq "hand: self loop dummies are no barycenter associates" (a2.node owner2).internal.barycenterAssociates #[]
  -- north→south self loop: dummies on both sides, the loop rerouted between them (EAST ports)
  let ((g3, owner3, loop3), a3) ← LayeredM.run (do
      let (g, layers) ← mkGraph 1
      let owner ← addNode g layers[0]!
      setNodeProp owner CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
      let pN ← addPort owner .north ⟨4, 0⟩
      let pS ← addPort owner .south ⟨6, 10⟩
      let loop ← connect pN pS
      runP NorthSouthPortPreprocessor.processor g
      return (g, owner, loop))
  let l3 := layerNodes a3 g3 0
  checkEq "hand: north/south self loop: [north dummy, owner, south dummy]" l3.size 3
  checkEq "hand: owner in the middle" l3[1]? (some owner3)
  checkEq "hand: loop starts at the north dummy" (sourceNode a3 loop3) l3[0]?
  checkEq "hand: loop ends at the south dummy" (targetNode a3 loop3) l3[2]?
  checkEq "hand: loop dummy ports on EAST"
    ((a3.edge loop3).source.map fun p => (a3.port p).side, (a3.edge loop3).target.map fun p => (a3.port p).side)
    (some PortSide.east, some PortSide.east)
  -- postprocessor restores the self loop with one bend point per dummy
  let ((), a4) ← LayeredM.run (do
      modifyNode l3[0]! fun x => { x with position := { x.position with y := -10 } }
      modifyNode l3[2]! fun x => { x with position := { x.position with y := 30 } }
      runP NorthSouthPortPostprocessor.processor g3) a3
  checkEq "hand: north/south self loop restored" (sourceNode a4 loop3, targetNode a4 loop3) (some owner3, some owner3)
  checkEq "hand: self loop bend points (north x 4, y -10) then (south x 6, y 30)" (a4.edge loop3).bendPoints
    #[⟨4, -10⟩, ⟨6, 30⟩]

def nsPostTests : Suite := suite "layered.intermediate.NorthSouthPortPostprocessor" do
  let ((g, nodes, ports, edges), a) ← LayeredM.run (do
      let r ← nsFixture
      runP NorthSouthPortPreprocessor.processor r.1
      let layer := (← getLayer (← getGraph r.1).layers[0]!).nodes
      modifyNode layer[0]! fun x => { x with position := { x.position with y := 10 } }
      modifyNode layer[2]! fun x => { x with position := { x.position with y := 70 } }
      runP NorthSouthPortPostprocessor.processor r.1
      return r)
  -- north_south_postprocessor_removes_all_north_south_dummy_nodes / removes_dummy_nodes_from_layers
  checkEq "removes_dummy_nodes_from_layers" (layerNodes a g 0) nodes
  -- north_south_postprocessor_restores_incoming_edge_to_origin_port
  checkEq "restores_incoming_edge_to_origin_port" (a.edge edges[0]!).target (some ports[0]!)
  checkEq "hand: incoming bend point (owner 20 + port 5, dummy y 10)" (a.edge edges[0]!).bendPoints #[⟨25, 10⟩]
  -- north_south_postprocessor_restores_outgoing_edge_to_origin_port
  checkEq "restores_outgoing_edge_to_origin_port" (a.edge edges[1]!).source (some ports[1]!)
  checkEq "hand: outgoing bend point (owner 20 + port 7, dummy y 70)" (a.edge edges[1]!).bendPoints #[⟨27, 70⟩]
  check "hand: single-port dummies add no junction points"
    (!(a.edge edges[0]!).props.has CoreOptions.JUNCTION_POINTS && !(a.edge edges[1]!).props.has CoreOptions.JUNCTION_POINTS)
  -- in/out dummy: same origin on both ports → junction points
  let ((_, _, pn, es), a2) ← LayeredM.run (do
      let r ← inOutFixture false
      let d := (← getLayer (← getGraph r.1).layers[0]!).nodes[0]!
      modifyNode d fun x => { x with position := { x.position with y := 5 } }
      runP NorthSouthPortPostprocessor.processor r.1
      return r)
  checkEq "hand: in/out edges reconnected to the origin port" ((a2.edge es[0]!).target, (a2.edge es[1]!).source) (some pn, some pn)
  checkEq "hand: same origin: junction point on the incoming edge" ((a2.edge es[0]!).props.get CoreOptions.JUNCTION_POINTS)
    (some #[⟨10, 5⟩])
  checkEq "hand: same origin: junction point on the outgoing edge" ((a2.edge es[1]!).props.get CoreOptions.JUNCTION_POINTS)
    (some #[⟨10, 5⟩])
  -- spline routing: reconnect only and record the dummy y on the origin port
  let ((g3, _, ports3, edges3), a3) ← LayeredM.run (do
      let r ← nsFixture
      setGraphProp r.1 CoreOptions.EDGE_ROUTING EdgeRouting.splines
      runP NorthSouthPortPreprocessor.processor r.1
      let layer := (← getLayer (← getGraph r.1).layers[0]!).nodes
      modifyNode layer[0]! fun x => { x with position := { x.position with y := 10 } }
      runP NorthSouthPortPostprocessor.processor r.1
      return r)
  checkEq "splines: dummies removed" (layerNodes a3 g3 0).size 2
  checkEq "splines: edge reconnected without bend points" ((a3.edge edges3[0]!).target, (a3.edge edges3[0]!).bendPoints)
    (some ports3[0]!, #[])
  checkEq "splines: SPLINE_NS_PORT_Y_COORD on the origin port"
    ((a3.port ports3[0]!).props.get NorthSouthPortPostprocessor.SPLINE_NS_PORT_Y_COORD) (some 10.0)

/-! ## InvertedPortProcessor -/

def invertedTests : Suite := suite "layered.intermediate.InvertedPortProcessor" do
  -- inverted_port_processor_inserts_dummy_for_inverted_ports
  let ((g, layers, ports, edges, headLabel), a) ← LayeredM.run (do
      let (g, layers) ← mkGraph 2
      let wsn ← addNode g layers[0]!
      setNodeProp wsn CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
      let westSource ← addPort wsn .west
      let wtn ← addNode g layers[1]!
      setNodeProp wtn CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
      let westTarget ← addPort wtn .west
      let e1 ← connect westSource westTarget
      let esn ← addNode g layers[0]!
      setNodeProp esn CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
      let eastSource ← addPort esn .east
      let etn ← addNode g layers[1]!
      setNodeProp etn CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
      let eastTarget ← addPort etn .east
      let e2 ← connect eastSource eastTarget
      let hl ← createLabel "head"
      setLabelProp hl CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.head
      modifyEdge e1 fun x => { x with labels := #[hl] }
      runP InvertedPortProcessor.processor g
      return (g, layers, #[westSource, westTarget, eastSource, eastTarget], #[e1, e2], hl))
  let westDummy := targetNode a (a.port ports[0]!).outgoingEdges[0]!
  checkEq "inserts_dummy: west dummy type" (westDummy.map fun d => (a.node d).type) (some NodeType.longEdge)
  checkEq "inserts_dummy: west dummy in the left layer" (westDummy.bind fun d => (a.node d).layer) (some layers[0]!)
  let eastIn := (a.port ports[3]!).incomingEdges[0]!
  let eastDummy := sourceNode a eastIn
  checkEq "inserts_dummy: east dummy type" (eastDummy.map fun d => (a.node d).type) (some NodeType.longEdge)
  checkEq "inserts_dummy: east dummy in the right layer" (eastDummy.bind fun d => (a.node d).layer) (some layers[1]!)
  checkEq "hand: dummies appended to their layers" ((layerNodes a g 0)[2]?, (layerNodes a g 1)[2]?) (westDummy, eastDummy)
  checkEq "hand: original west edge cut at the dummy" (a.edge edges[0]!).target (westDummy.bind fun d => (a.node d).ports[0]?)
  checkEq "hand: new edge from the dummy to the original target" (a.port ports[1]!).incomingEdges.size 1
  checkEq "hand: original east edge cut at the dummy" (targetNode a edges[1]!) eastDummy
  check "hand: head label moved to the new edge"
    ((a.edge edges[0]!).labels.isEmpty && (a.edge (a.port ports[1]!).incomingEdges[0]!).labels == #[headLabel])
  checkEq "hand: Rust sets no END_LABEL_EDGE" (a.label headLabel).internal.endLabelEdge none
  checkEq "hand: Rust sets no LONG_EDGE_SOURCE" (westDummy.bind fun d => (a.node d).internal.longEdgeSource) none
  -- inverted_port_processor_ignores_self_loop
  let ((g2, n2), a2) ← LayeredM.run (do
      let (g, layers) ← mkGraph 1
      let n ← addNode g layers[0]!
      setNodeProp n CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
      let w ← addPort n .west
      let e ← addPort n .east
      let _ ← connect w e
      runP InvertedPortProcessor.processor g
      return (g, n))
  checkEq "ignores_self_loop" (layerNodes a2 g2 0) #[n2]
  checkEq "ignores_self_loop: node stays NORMAL" (a2.node n2).type NodeType.normal

/-! ## PortSideProcessor -/

def portSideTests : Suite := suite "layered.intermediate.PortSideProcessor" do
  -- port_side_processor_assigns_sides_and_fixes_constraints
  let ((node, outPort, inPort), a) ← LayeredM.run (do
      let (g, layers) ← mkGraph 1
      let node ← addNode g layers[0]!
      let other ← addNode g layers[0]!
      setNodeProp node CoreOptions.PORT_CONSTRAINTS PortConstraints.free
      let outPort ← addPort node .undefined
      let inPort ← addPort node .undefined
      let otherWest ← addPort other .west
      let otherEast ← addPort other .east
      let _ ← connect outPort otherWest
      let _ ← connect otherEast inPort
      runP PortSideProcessor.processor g
      return (node, outPort, inPort))
  checkEq "assigns_sides_and_fixes_constraints: FIXED_SIDE"
    ((a.node node).props.getD CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined) PortConstraints.fixedSide
  checkEq "assigns_sides: output port EAST" (a.port outPort).side PortSide.east
  checkEq "assigns_sides: input port WEST" (a.port inPort).side PortSide.west
  -- port_side_processor_only_fills_undefined_ports_when_side_fixed
  let ((fixed, undefinedPort), a2) ← LayeredM.run (do
      let (g, layers) ← mkGraph 1
      let node ← addNode g layers[0]!
      setNodeProp node CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
      let fixed ← addPort node .north
      let undefinedPort ← addPort node .undefined
      runP PortSideProcessor.processor g
      return (fixed, undefinedPort))
  checkEq "only_fills_undefined_ports_when_side_fixed: kept" (a2.port fixed).side PortSide.north
  checkEq "hand: unconnected undefined port gets WEST (net flow 0)" (a2.port undefinedPort).side PortSide.west
  -- port_side_processor_prefers_port_dummy_external_side (+ layerless nodes are processed)
  let (port, a3) ← LayeredM.run (do
      let (g, layers) ← mkGraph 1
      let node ← addNode g layers[0]!
      setNodeProp node CoreOptions.PORT_CONSTRAINTS PortConstraints.free
      let dummy ← addNode g layers[0]!
      modifyNode dummy fun x => { x with internal := { x.internal with extPortSide := .south } }
      let port ← addPort node .undefined
      modifyPort port fun x => { x with internal := { x.internal with portDummy := some dummy } }
      runP PortSideProcessor.processor g
      return port)
  checkEq "prefers_port_dummy_external_side" (a3.port port).side PortSide.south
  let (lp, a4) ← LayeredM.run (do
      let g ← createGraph
      let n ← createNode g
      modifyGraph g fun x => { x with layerlessNodes := #[n] }
      let p ← addPort n .undefined
      let q ← addPort (← createNode g) .west
      let _ ← connect p q
      runP PortSideProcessor.processor g
      return p)
  checkEq "hand: layerless node processed (net flow -1: EAST)" (a4.port lp).side PortSide.east

/-! ## PortListSorter -/

/-- `graph_with_one_node` + `add_port(node, side, index, x, y)` for each spec; returns the node and
its ports in creation order. -/
def sorterFixture (constraints : PortConstraints) (specs : Array (PortSide × Option Int × Float × Float))
    (strategy : Option PortSortingStrategy := none) : LayeredM (LGraphId × LNodeId × Array LPortId) := do
  let (g, layers) ← mkGraph 1
  if let some s := strategy then setGraphProp g LayeredOptions.PORT_SORTING_STRATEGY s
  let node ← addNode g layers[0]!
  setNodeProp node CoreOptions.PORT_CONSTRAINTS constraints
  let mut ports : Array LPortId := #[]
  for (side, index, x, y) in specs do
    let p ← addPort node side ⟨x, y⟩
    if let some i := index then setPortProp p CoreOptions.PORT_INDEX i
    ports := ports.push p
  return (g, node, ports)

def portListSorterTests : Suite := suite "layered.intermediate.PortListSorter" do
  -- port_list_sorter_orders_by_side_and_index_for_fixed_order (via the strategy factory)
  let ((node, ps), a) ← LayeredM.run (do
      let (g, node, ps) ← sorterFixture .fixedOrder #[(.north, some 2, 50, 0), (.west, some 1, 0, 10),
        (.east, some 1, 0, 20), (.south, some 2, 80, 0), (.north, some 1, 10, 0), (.east, some 2, 0, 30),
        (.south, some 1, 20, 0), (.west, some 2, 0, 40)]
      runP (← IntermediateProcessorStrategy.create .portListSorter) g
      return (node, ps))
  -- created: n2 w1 e1 s2 n1 e2 s1 w2 → expected n1 n2 e1 e2 s1 s2 w1 w2
  checkEq "orders_by_side_and_index_for_fixed_order" (a.node node).ports
    #[ps[4]!, ps[0]!, ps[2]!, ps[5]!, ps[6]!, ps[3]!, ps[1]!, ps[7]!]
  check "port sides cached" (a.node node).portSidesCached
  -- port_list_sorter_orders_fixed_pos_ports_clockwise_by_position
  let ((node2, ps2), a2) ← LayeredM.run (do
      let (g, node, ps) ← sorterFixture .fixedPos #[(.north, none, 30, 0), (.south, none, 10, 0),
        (.west, none, 0, 30), (.east, none, 0, 10), (.north, none, 10, 0), (.west, none, 0, 10),
        (.south, none, 30, 0), (.east, none, 0, 30)]
      runP PortListSorter.processor g
      return (node, ps))
  -- created: nHi sLeft wHi eLo nLo wLo sRight eHi → nLo nHi eLo eHi sRight sLeft wHi wLo
  checkEq "orders_fixed_pos_ports_clockwise_by_position" (a2.node node2).ports
    #[ps2[4]!, ps2[0]!, ps2[3]!, ps2[7]!, ps2[6]!, ps2[1]!, ps2[2]!, ps2[5]!]
  -- port_list_sorter_skips_nodes_with_free_constraints
  let ((node3, ps3), a3) ← LayeredM.run (do
      let (g, node, ps) ← sorterFixture .free #[(.west, some 2, 0, 10), (.north, some 1, 5, 0)]
      runP PortListSorter.processor g
      return (node, ps))
  checkEq "skips_nodes_with_free_constraints" (a3.node node3).ports ps3
  -- FIXED_SIDE: side sort; the south/west range reversals cancel when both sides are present
  -- (hand: south range [3, 7) reversed, then the west range [3, 7) reversed back)
  let ((node4, ps4), a4) ← LayeredM.run (do
      let (g, node, ps) ← sorterFixture .fixedSide #[(.west, none, 0, 0), (.south, none, 0, 0),
        (.north, none, 0, 0), (.east, none, 0, 0), (.south, none, 0, 0), (.west, none, 0, 0),
        (.south, none, 0, 0), (.east, none, 0, 0)]
      runP PortListSorter.processor g
      return (node, ps))
  -- created: w1 s1 n1 e1 s2 w2 s3 e2
  checkEq "hand: FIXED_SIDE with south and west ports: n1 e1 e2 s1 s2 s3 w1 w2" (a4.node node4).ports
    #[ps4[2]!, ps4[3]!, ps4[7]!, ps4[1]!, ps4[4]!, ps4[6]!, ps4[0]!, ps4[5]!]
  -- FIXED_SIDE without west ports: the Java findPortSideRange bug reverses [1, 4) only
  let ((node5, ps5), a5) ← LayeredM.run (do
      let (g, node, ps) ← sorterFixture .fixedSide #[(.south, none, 0, 0), (.north, none, 0, 0),
        (.south, none, 0, 0), (.south, none, 0, 0), (.south, none, 0, 0)]
      runP PortListSorter.processor g
      return (node, ps))
  -- created: s1 n1 s2 s3 s4 → side sort n1 s1 s2 s3 s4 → reversed range [1, 4): n1 s3 s2 s1 s4
  checkEq "hand: FIXED_SIDE without west ports: n1 s3 s2 s1 s4 (Java range bug)" (a5.node node5).ports
    #[ps5[1]!, ps5[3]!, ps5[2]!, ps5[0]!, ps5[4]!]
  -- PORT_DEGREE: east by decreasing non-reversed outgoing degree, west by increasing incoming degree
  let ((node6, ps6), a6) ← LayeredM.run (do
      let (g, node, ps) ← sorterFixture .fixedSide #[(.east, none, 0, 0), (.west, none, 0, 0),
        (.east, none, 0, 0), (.west, none, 0, 0), (.east, none, 0, 0)] (some .portDegree)
      let other ← addNode g (← getGraph g).layers[0]!
      let sink ← addPort other .west
      let src ← addPort other .east
      -- eA: 1 out; eB: 2 out; eC: 2 out (one reversed); wA: 2 in; wB: 0 in
      let _ ← connect ps[0]! sink
      let _ ← connect ps[2]! sink
      let _ ← connect ps[2]! sink
      let _ ← connect ps[4]! sink
      let r ← connect ps[4]! sink
      modifyEdge r fun x => { x with internal := { x.internal with reversed := true } }
      let _ ← connect src ps[1]!
      let _ ← connect src ps[1]!
      runP PortListSorter.processor g
      return (node, ps))
  -- created: eA wA eB wB eC → side sort eA eB eC wA wB → degree sort eB eA eC wB wA
  checkEq "hand: PORT_DEGREE sorting" (a6.node node6).ports #[ps6[2]!, ps6[0]!, ps6[4]!, ps6[3]!, ps6[1]!]

/-! ## ReversedEdgeRestorer -/

def restorerTests : Suite := suite "layered.intermediate.ReversedEdgeRestorer" do
  -- reversed_edge_restorer_reverses_marked_edge_direction
  let ((sp, tp, edge, plain, label), a) ← LayeredM.run (do
      let (g, layers) ← mkGraph 1
      let sourceNode ← addNode g layers[0]!
      let targetNode ← addNode g layers[0]!
      let sp ← addPort sourceNode .east
      let tp ← addPort targetNode .west
      let edge ← connect sp tp
      let hl ← createLabel "head"
      setLabelProp hl CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.head
      modifyEdge edge fun x => { x with
        bendPoints := #[⟨1, 1⟩, ⟨2, 2⟩], labels := #[hl],
        internal := { x.internal with reversed := true } }
      let plain ← connect sp tp
      runP ReversedEdgeRestorer.processor g
      return (sp, tp, edge, plain, hl))
  checkEq "reverses_marked_edge_direction: source" (a.edge edge).source (some tp)
  checkEq "reverses_marked_edge_direction: target" (a.edge edge).target (some sp)
  check "reverses_marked_edge_direction: REVERSED cleared" (!(a.edge edge).internal.reversed)
  checkEq "hand: bend points reversed" (a.edge edge).bendPoints #[⟨2, 2⟩, ⟨1, 1⟩]
  checkEq "hand: HEAD label becomes TAIL"
    ((a.label label).props.getD CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.center) EdgeLabelPlacement.tail
  checkEq "hand: unmarked edge untouched" ((a.edge plain).source, (a.edge plain).target) (some sp, some tp)

def suites : Array Suite :=
  #[registrationTests, splitterTests, joinerTests, mergerTests, hypernodeTests, nsPreTests, nsSpecialTests,
    nsPostTests, invertedTests, portSideTests, portListSorterTests, restorerTests]

end Tests.Layered.IntermediateEdgePorts
