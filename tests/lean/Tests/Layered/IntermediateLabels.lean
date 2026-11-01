import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Intermediate.LabelProcessors
/-!
# Tests of the label intermediate processors (task I1)

`LabelDummyInserter`, `LabelDummySwitcher`, `LabelDummyRemover`, `LabelSideSelector`,
`LabelManagementProcessor`, `EndLabelSorter`, `EndLabelPostprocessor` and
`LayerSizeAndGraphHeightCalculator` on hand-built layered graphs. The elk-rs tests
(`tests/intermediate/*_test.rs`) are ported with their names in the check names; further expected
values are derived by hand from the Rust code ("hand: …").
-/
namespace Tests.Layered.IntermediateLabels

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate

def checkVec (name : String) (actual expected : KVector) : TestM Unit := do
  checkFloat s!"{name} x" actual.x expected.x
  checkFloat s!"{name} y" actual.y expected.y

/-- Runs a processor with a null monitor. -/
def runProc (p : LayeredProcessor) (g : LGraphId) : LayeredM Unit := p.process g ProgressMonitor.null

/-- A graph with `n` layers. -/
def mkGraph (n : Nat) (props : PropertyMap := {}) : LayeredM (LGraphId × Array LayerId) := do
  let g ← LayeredM.createGraph { props := props }
  let mut layers : Array LayerId := #[]
  for _ in [0:n] do
    layers := layers.push (← LayeredM.createLayer g)
  let ls := layers
  LayeredM.modifyGraph g fun x => { x with layers := ls }
  return (g, layers)

/-- A node of the given type in a layer (Rust test helper `add_node`). -/
def addNode (g : LGraphId) (layer : LayerId) (type : NodeType) (n : LNode := {}) : LayeredM LNodeId := do
  let node ← LayeredM.createNode g { n with type := type }
  LayeredM.setNodeLayer node (some layer)
  return node

/-- A port on the given side (Rust test helper `add_port`). -/
def addPort (node : LNodeId) (side : PortSide) : LayeredM LPortId := do
  let p ← LayeredM.createPort
  LayeredM.modifyPort p (·.setSide side)
  LayeredM.setPortNode p (some node)
  return p

/-- An edge between two ports (Rust test helper `connect`). -/
def connect (s t : LPortId) (e : LEdge := {}) : LayeredM LEdgeId := do
  let edge ← LayeredM.createEdge e
  LayeredM.setEdgeSource edge (some s)
  LayeredM.setEdgeTarget edge (some t)
  return edge

/-- A label with text, size and properties. -/
def mkLabel (text : String) (w h : Float) (props : PropertyMap := {}) : LayeredM LLabelId :=
  LayeredM.createLabel text { size := ⟨w, h⟩, props := props }

def addEdgeLabel (e : LEdgeId) (l : LLabelId) : LayeredM Unit :=
  LayeredM.modifyEdge e fun x => { x with labels := x.labels.push l }

def setRepresented (n : LNodeId) (ls : Array LLabelId) : LayeredM Unit :=
  LayeredM.modifyNode n fun x => { x with internal := { x.internal with representedLabels := ls } }

def centerProps : PropertyMap := ({} : PropertyMap).set LayeredOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.center

-- ===============================================================================================
-- LabelDummyInserter

/-- Rust `inserts_label_dummy_and_moves_center_labels` (+ hand checks of the split edge). -/
def inserterTests : Suite := suite "layered.intermediate.labelDummyInserter" do
  let ((g, src, tgt, sp, tp, e, lbl), a) ← LayeredM.run (do
    let props := ({} : PropertyMap).set LayeredOptions.DIRECTION Direction.right
      |>.set LayeredOptions.SPACING_EDGE_LABEL 2.0 |>.set LayeredOptions.SPACING_LABEL_LABEL 1.0
    let g ← LayeredM.createGraph { props := props }
    let src ← LayeredM.createNode g
    let tgt ← LayeredM.createNode g
    LayeredM.modifyGraph g fun x => { x with layerlessNodes := #[src, tgt] }
    let sp ← addPort src .east
    let tp ← addPort tgt .west
    let e ← connect sp tp { props := ({} : PropertyMap).set CoreOptions.EDGE_THICKNESS 2.0 }
    let lbl ← mkLabel "center" 10.0 5.0 centerProps
    addEdgeLabel e lbl
    runProc LabelDummyInserter.processor g
    return (g, src, tgt, sp, tp, e, lbl))
  let layerless := (a.graph g).layerlessNodes
  checkEq "inserts_label_dummy_and_moves_center_labels: label dummy should be added" layerless.size 3
  let dummy := layerless[2]!
  let d := a.node dummy
  checkEq "inserts_label_dummy_and_moves_center_labels: dummy type" d.type NodeType.label
  checkEq "inserts_label_dummy_and_moves_center_labels: center label must move to dummy" d.internal.representedLabels #[lbl]
  checkFloat "inserts_label_dummy_and_moves_center_labels: dummy width" d.size.x 10.0
  checkFloat "inserts_label_dummy_and_moves_center_labels: dummy height" d.size.y 11.0
  checkEq "inserts_label_dummy_and_moves_center_labels: center label must be removed from edge" (a.edge e).labels #[]
  checkEq "hand: dummies appended after the original layerless nodes" (layerless.extract 0 2) #[src, tgt]
  checkEq "hand: dummy graph" d.graph (some g)
  check "hand: ORIGIN is the split edge" (d.internal.origin == some (.lEdge e))
  checkEq "hand: PORT_CONSTRAINTS = FIXED_POS" (d.props.get LayeredOptions.PORT_CONSTRAINTS) (some PortConstraints.fixedPos)
  checkEq "hand: dummy has two ports" d.ports.size 2
  let pin := d.ports[0]!
  let pout := d.ports[1]!
  checkEq "hand: input port side WEST" (a.port pin).side PortSide.west
  checkEq "hand: output port side EAST" (a.port pout).side PortSide.east
  checkFloat "hand: port position floor(thickness / 2)" (a.port pin).position.y 1.0
  checkEq "hand: edge rerouted into the dummy" (a.edge e).target (some pin)
  let newEdge := (a.port pout).outgoingEdges[0]!
  checkEq "hand: new edge from the dummy to the old target" (a.edge newEdge).target (some tp)
  checkEq "hand: old target's incoming edges" (a.port tp).incomingEdges #[newEdge]
  checkEq "hand: new edge copies EDGE_THICKNESS" ((a.edge newEdge).props.get? CoreOptions.EDGE_THICKNESS) (some 2.0)
  checkEq "hand: LONG_EDGE_SOURCE = edge source" d.internal.longEdgeSource (some sp)
  checkEq "hand: LONG_EDGE_TARGET = old target" d.internal.longEdgeTarget (some tp)
  check "hand: no label dummies next to it" (!d.internal.longEdgeHasLabelDummies)
  checkEq "hand: source node keeps its outgoing edge" (a.nodeOutgoingEdges src) #[e]
  checkEq "hand: target node unchanged" (a.node tgt).ports #[tp]

/-- Vertical stacking, head/tail labels, self loops, negative thickness and a long edge source. -/
def inserterTests2 : Suite := suite "layered.intermediate.labelDummyInserter.cases" do
  let ((g, e, c1, c2, head, tail, loopE, negE, leE), a) ← LayeredM.run (do
    let props := ({} : PropertyMap).set LayeredOptions.DIRECTION Direction.down
      |>.set LayeredOptions.SPACING_EDGE_LABEL 2.0 |>.set LayeredOptions.SPACING_LABEL_LABEL 1.0
    let g ← LayeredM.createGraph { props := props }
    let n1 ← LayeredM.createNode g
    let n2 ← LayeredM.createNode g
    let n3 ← LayeredM.createNode g
    let le ← LayeredM.createNode g { type := .longEdge }
    LayeredM.modifyGraph g fun x => { x with layerlessNodes := #[n1, n2, n3, le] }
    let p1 ← addPort n1 .east
    let p2 ← addPort n2 .west
    let e ← connect p1 p2
    let c1 ← mkLabel "c1" 10.0 5.0
    let head ← mkLabel "h" 7.0 3.0 (({} : PropertyMap).set LayeredOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.head)
    let c2 ← mkLabel "c2" 20.0 4.0 centerProps
    let tail ← mkLabel "t" 6.0 3.0 (({} : PropertyMap).set LayeredOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.tail)
    for l in #[c1, head, c2, tail] do addEdgeLabel e l
    -- a self loop with a center label is not processed
    let q1 ← addPort n3 .east
    let q2 ← addPort n3 .west
    let loopE ← connect q1 q2
    addEdgeLabel loopE (← mkLabel "loop" 5.0 5.0)
    -- negative thickness is clamped to 0
    let r1 ← addPort n1 .east
    let r2 ← addPort n3 .west
    let negE ← connect r1 r2 { props := ({} : PropertyMap).set CoreOptions.EDGE_THICKNESS (-3.0) }
    addEdgeLabel negE (← mkLabel "neg" 4.0 4.0)
    -- an edge leaving a long edge dummy that already has label dummies
    LayeredM.modifyNode le fun x => { x with internal := { x.internal with
      longEdgeSource := some p1, longEdgeTarget := some p2, longEdgeHasLabelDummies := true } }
    let s1 ← addPort le .east
    let s2 ← addPort n2 .west
    let leE ← connect s1 s2
    addEdgeLabel leE (← mkLabel "le" 4.0 4.0)
    runProc LabelDummyInserter.processor g
    return (g, e, c1, c2, head, tail, loopE, negE, leE))
  let layerless := (a.graph g).layerlessNodes
  checkEq "hand: one dummy per labelled non-loop edge" layerless.size 7
  let dE := layerless[4]!
  checkEq "hand: both center labels represented (order kept)" (a.node dE).internal.representedLabels #[c1, c2]
  -- vertical: x = (0 + (10 + 1)) + (20 + 1) - 1 = 31, y = max(1, 5, 4) + (2 + 1) = 8
  checkFloat "hand: vertical dummy width" (a.node dE).size.x 31.0
  checkFloat "hand: vertical dummy height" (a.node dE).size.y 8.0
  checkEq "hand: tail label stays on the original edge" (a.edge e).labels #[tail]
  let pout := (a.node dE).ports[1]!
  let newEdge := (a.port pout).outgoingEdges[0]!
  checkEq "hand: head label moves to the new edge" (a.edge newEdge).labels #[head]
  checkEq "hand: head label END_LABEL_EDGE = original edge" (a.label head).internal.endLabelEdge (some e)
  checkEq "hand: self loop keeps its label" (a.edge loopE).labels.size 1
  checkEq "hand: negative thickness stored as 0" ((a.edge negE).props.get? CoreOptions.EDGE_THICKNESS) (some 0.0)
  let dNeg := layerless[5]!
  checkFloat "hand: vertical dummy of a zero-thickness edge: height max(0, 4) + (2 + 0)" (a.node dNeg).size.y 6.0
  checkFloat "hand: zero thickness ports at 0" (a.port (a.node dNeg).ports[0]!).position.y 0.0
  let dLe := layerless[6]!
  check "hand: LONG_EDGE_HAS_LABEL_DUMMIES copied from the long edge source" (a.node dLe).internal.longEdgeHasLabelDummies
  checkEq "hand: LONG_EDGE_SOURCE copied from the long edge source" (a.node dLe).internal.longEdgeSource
    ((a.node (layerless[3]!)).internal.longEdgeSource)
  checkEq "hand: dummy of the long edge's edge represents its label" (a.node dLe).internal.representedLabels.size 1
  let _ := leE

-- ===============================================================================================
-- LabelDummySwitcher

/-- Rust `moves_label_dummy_to_median_layer` (+ hand checks of the swapped edges and
`LONG_EDGE_BEFORE_LABEL_DUMMY`). -/
def switcherTests : Suite := suite "layered.intermediate.labelDummySwitcher" do
  let ((layers, nodes, ports, lbl), a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 3
    let source ← addNode g layers[0]! .normal
    let labelDummy ← addNode g layers[0]! .label
    let longEdge1 ← addNode g layers[1]! .longEdge
    let longEdge2 ← addNode g layers[2]! .longEdge
    let target ← addNode g layers[2]! .normal
    let sourceOut ← addPort source .east
    let labelIn ← addPort labelDummy .west
    let labelOut ← addPort labelDummy .east
    let long1In ← addPort longEdge1 .west
    let long1Out ← addPort longEdge1 .east
    let long2In ← addPort longEdge2 .west
    let long2Out ← addPort longEdge2 .east
    let targetIn ← addPort target .west
    let _ ← connect sourceOut labelIn
    let _ ← connect labelOut long1In
    let _ ← connect long1Out long2In
    let _ ← connect long2Out targetIn
    let lbl ← mkLabel "l" 5.0 5.0
    setRepresented labelDummy #[lbl]
    runProc LabelDummySwitcher.processor g
    return (layers, #[source, labelDummy, longEdge1, longEdge2, target],
      #[sourceOut, labelIn, labelOut, long1In, long1Out, long2In, long2Out, targetIn], lbl))
  let labelDummy := nodes[1]!; let longEdge1 := nodes[2]!; let longEdge2 := nodes[3]!
  check "moves_label_dummy_to_median_layer: long edge dummy should swap into leftmost layer"
    ((a.layer layers[0]!).nodes.contains longEdge1)
  check "moves_label_dummy_to_median_layer: label dummy should move to median layer"
    ((a.layer layers[1]!).nodes.contains labelDummy)
  checkEq "hand: swapped dummy keeps the label dummy's position in layer 0" (a.layer layers[0]!).nodes #[nodes[0]!, longEdge1]
  checkEq "hand: layer ids assigned" ((a.graph (a.layer layers[2]!).owner).layers.map fun l => (a.layer l).id) #[0, 1, 2]
  -- source → long1 → label → long2 → target
  checkEq "hand: source edge now enters long1" (a.portSuccessorPorts ports[0]!) #[ports[3]!]
  checkEq "hand: long1 now enters the label dummy" (a.portSuccessorPorts ports[4]!) #[ports[1]!]
  checkEq "hand: label dummy now enters long2" (a.portSuccessorPorts ports[2]!) #[ports[5]!]
  checkEq "hand: long2 still enters the target" (a.portSuccessorPorts ports[6]!) #[ports[7]!]
  check "hand: preceding long edge dummy LONG_EDGE_BEFORE_LABEL_DUMMY" (a.node longEdge1).internal.longEdgeBeforeLabelDummy
  check "hand: following long edge dummy not marked" (!(a.node longEdge2).internal.longEdgeBeforeLabelDummy)
  checkEq "hand: INCLUDE_LABEL set on the represented label" ((a.label lbl).props.get? LabelDummySwitcher.INCLUDE_LABEL) (some true)

/-- A label dummy in layer 0 of a chain over `widths.size` layers; layer `i` also holds a `NORMAL`
node of width `widths[i]`. Returns the layers, the label dummy and the long edge dummies. -/
def buildChain (widths : Array Float) (strategy : Option CenterEdgeLabelPlacementStrategy)
    (reversed : Bool := false) (layerWidths : Array Float := #[]) (dummyWidth : Float := 30.0) :
    LayeredM (LGraphId × Array LayerId × LNodeId × Array LNodeId) := do
  let props := ({} : PropertyMap).set LayeredOptions.DIRECTION Direction.right
  let props := match strategy with
    | some s => props.set LayeredOptions.EDGE_LABELS_CENTER_LABEL_PLACEMENT_STRATEGY s
    | none => props
  let (g, layers) ← mkGraph widths.size props
  for h : i in [0:layers.size] do
    if let some w := layerWidths[i]? then
      LayeredM.modifyLayer layers[i] fun l => { l with size := ⟨w, 0.0⟩ }
  let source ← addNode g layers[0]! .normal { size := ⟨widths[0]!, 10.0⟩ }
  let labelDummy ← addNode g layers[0]! .label { size := ⟨dummyWidth, 10.0⟩ }
  let mut prevOut ← addPort source .east
  let dIn ← addPort labelDummy .west
  let dOut ← addPort labelDummy .east
  let _ ← connect prevOut dIn { internal := { reversed := reversed } }
  prevOut := dOut
  let mut longs : Array LNodeId := #[]
  for i in [1:widths.size] do
    let _ ← addNode g layers[i]! .normal { size := ⟨widths[i]!, 10.0⟩ }
    let le ← addNode g layers[i]! .longEdge
    let lin ← addPort le .west
    let lout ← addPort le .east
    let _ ← connect prevOut lin { internal := { reversed := reversed } }
    prevOut := lout
    longs := longs.push le
  let target ← addNode g layers[widths.size - 1]! .normal
  let tin ← addPort target .west
  let _ ← connect prevOut tin { internal := { reversed := reversed } }
  let lbl ← mkLabel "l" dummyWidth 5.0
  setRepresented labelDummy #[lbl]
  return (g, layers, labelDummy, longs)

/-- Layer index of a node in the final arena. -/
def layerOf (a : LGraphArena) (layers : Array LayerId) (n : LNodeId) : Option Nat :=
  (a.node n).layer.bind fun l => layers.findIdx? (· == l)

/-- Runs the switcher on a chain and returns the label dummy's final layer index. -/
def switchChain (widths : Array Float) (strategy : Option CenterEdgeLabelPlacementStrategy) (reversed : Bool := false)
    (layerWidths : Array Float := #[]) (dummyWidth : Float := 30.0) : IO (Option Nat × Option Alignment) := do
  let ((layers, d), a) ← LayeredM.run (do
    let (g, layers, d, _) ← buildChain widths strategy reversed layerWidths dummyWidth
    runProc LabelDummySwitcher.processor g
    return (layers, d))
  return (layerOf a layers d, (a.node d).props.get? LayeredOptions.ALIGNMENT)

/-- Target layers per strategy on a 5-layer chain with widths `[60, 10, 10, 10, 10]` (minimum layer
space `max(2 · 10, 20) = 20`). -/
def switcherStrategyTests : Suite := suite "layered.intermediate.labelDummySwitcher.strategies" do
  let widths : Array Float := #[60.0, 10.0, 10.0, 10.0, 10.0]
  -- median: range 0..4, lower median (5 - 1) / 2 = 2
  checkEq "hand: MEDIAN_LAYER (default) → layer 2" (← switchChain widths none).1 (some 2)
  -- widest: layer widths 60, 30 (dummy width does not count before), 10, 10, 10 → layer 0
  checkEq "hand: WIDEST_LAYER → layer 0" (← switchChain widths (some .widestLayer)).1 (some 0)
  -- center: sums -20 + 80 = 60, 90, 120, 150, 180; threshold 90 → index 1
  checkEq "hand: CENTER_LAYER → layer 1" (← switchChain widths (some .centerLayer)).1 (some 1)
  let (head, headAlign) ← switchChain widths (some .headLayer)
  checkEq "hand: HEAD_LAYER → rightmost layer 4" head (some 4)
  checkEq "hand: HEAD_LAYER alignment RIGHT" headAlign (some Alignment.right)
  let (tail, tailAlign) ← switchChain widths (some .tailLayer)
  checkEq "hand: TAIL_LAYER → leftmost layer 0" tail (some 0)
  checkEq "hand: TAIL_LAYER alignment LEFT" tailAlign (some Alignment.left)
  let (headRev, headRevAlign) ← switchChain widths (some .headLayer) (reversed := true)
  checkEq "hand: HEAD_LAYER of a reversed edge → leftmost layer 0" headRev (some 0)
  checkEq "hand: HEAD_LAYER of a reversed edge alignment LEFT" headRevAlign (some Alignment.left)
  -- widest: a wide node in layer 3
  checkEq "hand: WIDEST_LAYER picks the widest normal node's layer" (← switchChain #[10.0, 10.0, 10.0, 90.0, 10.0] (some .widestLayer)).1 (some 3)
  -- space efficient: layer 2 already has size.x = 40 ≥ dummy width 30 → assign_to_wider_layer
  checkEq "hand: SPACE_EFFICIENT_LAYER uses the first layer whose size.x fits" (← switchChain widths (some .spaceEfficientLayer) (layerWidths := #[0.0, 0.0, 40.0, 50.0, 0.0])).1 (some 2)
  -- space efficient without a wide enough layer: potentially widest = first layer whose width ≥ 30 (layer 0: 60)
  checkEq "hand: SPACE_EFFICIENT_LAYER falls back to the potentially widest layer" (← switchChain widths (some .spaceEfficientLayer)).1 (some 0)
  -- widths 10, 20, 20 and a dummy of width 100: layer 1 is the first of the two widest layers
  checkEq "hand: SPACE_EFFICIENT_LAYER wide dummy → widest potential (leftmost on ties)" (← switchChain #[10.0, 20.0, 20.0] (some .spaceEfficientLayer) (dummyWidth := 100.0)).1 (some 1)
  -- a label override wins over the graph strategy
  let ((layers, d), a) ← LayeredM.run (do
    let (g, layers, d, _) ← buildChain widths (some .medianLayer)
    let lbl := (← LayeredM.getNode d).internal.representedLabels[0]!
    LayeredM.setLabelProp lbl LayeredOptions.EDGE_LABELS_CENTER_LABEL_PLACEMENT_STRATEGY CenterEdgeLabelPlacementStrategy.tailLayer
    runProc LabelDummySwitcher.processor g
    return (layers, d))
  checkEq "hand: label's own strategy (TAIL_LAYER) overrides the graph's" (layerOf a layers d) (some 0)

-- ===============================================================================================
-- LabelDummyRemover

/-- Single layer source → label dummy → target (Rust `graph_with_single_layer` + helpers). -/
def removerGraph (props : PropertyMap) (dummyPos dummySize : KVector) (labels : Array (String × Float × Float × PropertyMap))
    (side : LabelSide) (sourceX : Float := 0.0) (targetX : Float := 0.0) :
    LayeredM (LGraphId × LayerId × Array LNodeId × Array LPortId × Array LEdgeId × Array LLabelId) := do
  let (g, layers) ← mkGraph 1 props
  let layer := layers[0]!
  let source ← addNode g layer .normal { position := ⟨sourceX, 0.0⟩, size := ⟨30.0, 10.0⟩ }
  let dummy ← addNode g layer .label { position := dummyPos, size := dummySize }
  let target ← addNode g layer .normal { position := ⟨targetX, 0.0⟩ }
  let sourcePort ← addPort source .east
  let dummyWest ← addPort dummy .west
  let dummyEast ← addPort dummy .east
  let targetPort ← addPort target .west
  let surviving ← connect sourcePort dummyWest
  let dropped ← connect dummyEast targetPort { bendPoints := #[⟨1.0, 2.0⟩] }
  let mut ls : Array LLabelId := #[]
  for (t, w, h, p) in labels do
    ls := ls.push (← mkLabel t w h p)
  let labelIds := ls
  LayeredM.modifyNode dummy fun x => { x with internal := { x.internal with
    origin := some (.lEdge surviving), representedLabels := labelIds, labelSide := side } }
  return (g, layer, #[source, dummy, target], #[sourcePort, dummyWest, dummyEast, targetPort], #[surviving, dropped], ls)

def removerProps (dir : Direction) (routing : EdgeRouting := .orthogonal) : PropertyMap :=
  ({} : PropertyMap).set LayeredOptions.DIRECTION dir |>.set LayeredOptions.EDGE_ROUTING routing
    |>.set LayeredOptions.SPACING_EDGE_LABEL 2.0 |>.set LayeredOptions.SPACING_LABEL_LABEL 1.0

def removerTests : Suite := suite "layered.intermediate.labelDummyRemover" do
  -- test_removed_nodes
  let ((layer, nodes, ports, edges, ls), a) ← LayeredM.run (do
    let (g, layer, nodes, ports, edges, ls) ← removerGraph (removerProps .right) ⟨10.0, 20.0⟩ ⟨60.0, 30.0⟩
      #[("edge-label", 20.0, 6.0, {})] .below
    runProc LabelDummyRemover.processor g
    return (layer, nodes, ports, edges, ls))
  let surviving := edges[0]!; let dropped := edges[1]!; let label := ls[0]!
  check "test_removed_nodes: all label dummy nodes must be removed"
    ((a.layer layer).nodes.all fun n => (a.node n).type != .label)
  check "test_removed_nodes: represented labels must be moved back to the origin edge" ((a.edge surviving).labels.contains label)
  checkEq "test_removed_nodes: joined edge must target the original downstream port" (a.edge surviving).target (some ports[3]!)
  check "test_removed_nodes: label position must be updated from dummy placement" ((a.label label).position.y > 20.0)
  -- hand: below → y = 20 + (1 + 2) = 23; label space (60, 30 - 1 - 2); x = 10 + (60 - 20) / 2 = 30
  checkVec "hand: label position below the edge" (a.label label).position ⟨30.0, 23.0⟩
  checkEq "hand: layer keeps source and target" (a.layer layer).nodes #[nodes[0]!, nodes[2]!]
  checkEq "hand: removed dummy has no layer" (a.node nodes[1]!).layer none
  checkEq "hand: dropped edge detached (source)" (a.edge dropped).source none
  checkEq "hand: dropped edge detached (target)" (a.edge dropped).target none
  checkEq "hand: surviving edge took the dropped bend points" (a.edge surviving).bendPoints.size 1
  checkEq "hand: target port's incoming edges" (a.port ports[3]!).incomingEdges #[surviving]
  -- test_vertical_up_reverses_label_iteration_order
  let ((ls2), a2) ← LayeredM.run (do
    let (g, _, _, _, _, ls) ← removerGraph (removerProps .up) ⟨5.0, 7.0⟩ ⟨40.0, 20.0⟩
      #[("a", 10.0, 6.0, {}), ("b", 10.0, 6.0, {})] .above
    runProc LabelDummyRemover.processor g
    return ls)
  let la := (a2.label ls2[0]!).position; let lb := (a2.label ls2[1]!).position
  check "test_vertical_up_reverses_label_iteration_order: UP direction must place labels in reverse iteration order" (lb.x < la.x)
  -- hand: label space (40, 20 - 3 = 17); right-aligned y = 7 + 17 - 6 = 18; b at x 5, a at 5 + 10 + 1
  checkVec "hand: UP label b" lb ⟨5.0, 18.0⟩
  checkVec "hand: UP label a" la ⟨16.0, 18.0⟩
  -- vertical DOWN, below (left aligned), inline labels are centred in the full height
  let (ls3, a3) ← LayeredM.run (do
    let inline := ({} : PropertyMap).set LayeredOptions.EDGE_LABELS_INLINE true
    let (g, _, _, _, _, ls) ← removerGraph (removerProps .down) ⟨5.0, 7.0⟩ ⟨40.0, 20.0⟩
      #[("a", 10.0, 6.0, inline), ("b", 10.0, 6.0, inline)] .inline
    runProc LabelDummyRemover.processor g
    return ls)
  -- inline: label space (40, 20); y = 7 + (20 - 6) / 2 = 14; a first at x 5, b at 16
  checkVec "hand: DOWN inline label a" (a3.label ls3[0]!).position ⟨5.0, 14.0⟩
  checkVec "hand: DOWN inline label b" (a3.label ls3[1]!).position ⟨16.0, 14.0⟩
  -- polyline routing adds the dummy's first port anchor as bend point before the dropped bend points
  let ((edges4, ports4, nodes4), a4) ← LayeredM.run (do
    let (g, _, nodes, ports, edges, _) ← removerGraph (removerProps .right .polyline) ⟨10.0, 20.0⟩ ⟨60.0, 30.0⟩
      #[("x", 20.0, 6.0, {})] .above
    LayeredM.modifyPort ports[1]! fun p => { p with position := ⟨0.0, 4.0⟩ }
    runProc LabelDummyRemover.processor g
    return (edges, ports, nodes))
  -- west port anchor (0, size.y / 2 = 0) → absolute (10 + 0 + 0, 20 + 4 + 0)
  checkEq "hand: polyline bend points" (a4.edge edges4[0]!).bendPoints.size 2
  checkVec "hand: polyline unnecessary bend point" (a4.edge edges4[0]!).bendPoints[0]! ⟨10.0, 24.0⟩
  checkVec "hand: dropped bend point appended" (a4.edge edges4[0]!).bendPoints[1]! ⟨1.0, 2.0⟩
  let _ := (ports4, nodes4)
  -- post compaction LEFT/RIGHT: like Java the labels stay at the dummy position (the compactor has
  -- moved the dummy; elk-rs moved them again to the source/target bounds: 70 resp. 140)
  for (strategy, expectedX) in #[(GraphCompactionStrategy.left, 120.0), (GraphCompactionStrategy.right, 120.0), (GraphCompactionStrategy.none, 120.0)] do
    let (ls5, a5) ← LayeredM.run (do
      let props := (removerProps .right).set LayeredOptions.COMPACTION_POST_COMPACTION_STRATEGY strategy
      let (g, _, _, _, _, ls) ← removerGraph props ⟨100.0, 20.0⟩ ⟨60.0, 30.0⟩ #[("x", 20.0, 6.0, {})] .above
        (sourceX := 0.0) (targetX := 200.0)
      LayeredM.modifyGraph g fun x => { x with internal := { x.internal with spacings := some (Spacings.new x.props) } }
      runProc LabelDummyRemover.processor g
      return ls)
    checkFloat s!"hand: post compaction {strategy} label x" (a5.label ls5[0]!).position.x expectedX

-- ===============================================================================================
-- LabelSideSelector

/-- Rust `test_removed_nodes` of `label_side_selector_test.rs` + hand checks of all strategies. -/
def sideSelectorTests : Suite := suite "layered.intermediate.labelSideSelector" do
  -- test_removed_nodes (ALWAYS_UP on an edge label)
  let (lbl, a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 1 (({} : PropertyMap).set LayeredOptions.EDGE_LABELS_SIDE_SELECTION EdgeLabelSideSelection.alwaysUp)
    let s ← addNode g layers[0]! .normal
    let t ← addNode g layers[0]! .normal
    let e ← connect (← addPort s .undefined) (← addPort t .undefined)
    let lbl ← mkLabel "edge-label" 1.0 1.0
    addEdgeLabel e lbl
    runProc LabelSideSelector.processor g
    return lbl)
  check "test_removed_nodes: label side assigned" ((a.label lbl).internal.labelSide != .unknown)
  checkEq "hand: ALWAYS_UP edge label ABOVE" (a.label lbl).internal.labelSide LabelSide.above

/-- A layer with the given node types; label dummies are 20 × 11 with a represented label and an
incoming/outgoing edge of thickness 2 (reversed when `reversed`). Returns the nodes. -/
def sideGraph (mode : EdgeLabelSideSelection) (types : Array NodeType) (reversed : Bool := false)
    (inline : Bool := false) : LayeredM (LGraphId × Array LNodeId) := do
  let (g, layers) ← mkGraph 3 (({} : PropertyMap).set LayeredOptions.EDGE_LABELS_SIDE_SELECTION mode)
  let left ← addNode g layers[0]! .normal
  let right ← addNode g layers[2]! .normal
  let mut nodes : Array LNodeId := #[]
  for t in types do
    let n ← addNode g layers[1]! t { size := ⟨20.0, 11.0⟩ }
    let pin ← addPort n .west
    let pout ← addPort n .east
    let edgeProps := ({} : PropertyMap).set CoreOptions.EDGE_THICKNESS 2.0
    let e1 ← connect (← addPort left .east) pin { props := edgeProps, internal := { reversed := reversed } }
    let _ ← connect pout (← addPort right .west) { props := edgeProps, internal := { reversed := reversed } }
    if t == .label then
      let lp := if inline then ({} : PropertyMap).set LayeredOptions.EDGE_LABELS_INLINE true else {}
      let l ← mkLabel "l" 10.0 5.0 lp
      setRepresented n #[l]
      LayeredM.modifyNode n fun x => { x with internal := { x.internal with origin := some (.lEdge e1) } }
    nodes := nodes.push n
  return (g, nodes)

/-- The label sides of the given nodes after running the selector. -/
def sidesOf (mode : EdgeLabelSideSelection) (types : Array NodeType) (reversed : Bool := false) : IO (Array LabelSide) := do
  let (nodes, a) ← LayeredM.run (do
    let (g, nodes) ← sideGraph mode types reversed
    runProc LabelSideSelector.processor g
    return nodes)
  return nodes.map fun n => (a.node n).internal.labelSide

def sideStrategyTests : Suite := suite "layered.intermediate.labelSideSelector.strategies" do
  let (nodes, a) ← LayeredM.run (do
    let (g, nodes) ← sideGraph .alwaysUp #[.label]
    runProc LabelSideSelector.processor g
    return nodes)
  let d := a.node nodes[0]!
  checkEq "hand: ALWAYS_UP dummy ABOVE" d.internal.labelSide LabelSide.above
  -- Java writes the side to the label dummy only (elk-rs also wrote it to the represented labels)
  checkEq "hand: ALWAYS_UP represented label keeps its side (Java)" (a.label d.internal.representedLabels[0]!).internal.labelSide LabelSide.unknown
  -- ports at height - ceil(thickness / 2) = 11 - 1
  checkFloat "hand: ABOVE moves the ports to 10" (a.port d.ports[0]!).position.y 10.0
  let (nodesB, b) ← LayeredM.run (do
    let (g, nodes) ← sideGraph .alwaysDown #[.label]
    runProc LabelSideSelector.processor g
    return nodes)
  checkEq "hand: ALWAYS_DOWN dummy BELOW" (b.node nodesB[0]!).internal.labelSide LabelSide.below
  checkFloat "hand: BELOW leaves the ports" (b.port (b.node nodesB[0]!).ports[0]!).position.y 0.0
  checkEq "hand: DIRECTION_UP rightward → ABOVE" (← sidesOf .directionUp #[.label]) #[LabelSide.above]
  checkEq "hand: DIRECTION_UP reversed → BELOW" (← sidesOf .directionUp #[.label] (reversed := true)) #[LabelSide.below]
  checkEq "hand: DIRECTION_DOWN rightward → BELOW" (← sidesOf .directionDown #[.label]) #[LabelSide.below]
  checkEq "hand: DIRECTION_DOWN reversed → ABOVE" (← sidesOf .directionDown #[.label] (reversed := true)) #[LabelSide.above]
  -- SMART: a lone label dummy (top and bottom group, run of one) → default side
  checkEq "hand: SMART_DOWN lone dummy → BELOW" (← sidesOf .smartDown #[.label]) #[LabelSide.below]
  checkEq "hand: SMART_UP lone dummy → ABOVE" (← sidesOf .smartUp #[.label]) #[LabelSide.above]
  -- top group with a single label dummy at the top → ABOVE; bottom group → BELOW
  checkEq "hand: SMART top label dummy → ABOVE" (← sidesOf .smartDown #[.label, .normal]) #[LabelSide.above, LabelSide.unknown]
  checkEq "hand: SMART bottom label dummy → BELOW" (← sidesOf .smartUp #[.normal, .label]) #[LabelSide.unknown, LabelSide.below]
  -- run of two label dummies → ABOVE, BELOW
  checkEq "hand: SMART two label dummies → ABOVE/BELOW" (← sidesOf .smartDown #[.label, .label]) #[LabelSide.above, LabelSide.below]
  -- a single label dummy between normal nodes → default side
  checkEq "hand: SMART_UP middle dummy → ABOVE" (← sidesOf .smartUp #[.normal, .label, .normal]) #[LabelSide.unknown, LabelSide.above, LabelSide.unknown]
  -- three label dummies: different long edge ends? all have none → one run of 3 → default side
  checkEq "hand: SMART three dummies → default side" (← sidesOf .smartDown #[.label, .label, .label]) #[LabelSide.below, LabelSide.below, LabelSide.below]
  -- inline labels: INLINE side, dummy shrinks by spacing + thickness, ports at ceil(11 - 2 - 2) / 2
  let (nodesI, ai) ← LayeredM.run (do
    let (g, nodes) ← sideGraph .alwaysDown #[.label] (inline := true)
    runProc LabelSideSelector.processor g
    return nodes)
  let di := ai.node nodesI[0]!
  checkEq "hand: inline label dummy → INLINE" di.internal.labelSide LabelSide.inline
  checkFloat "hand: inline dummy height 11 - 2 - 2" di.size.y 7.0
  checkFloat "hand: inline ports at ceil(7) / 2" (ai.port di.ports[0]!).position.y 3.5

/-- SMART end labels at a regular node: two east ports with tail labels get ABOVE/BELOW. -/
def sideEndLabelTests : Suite := suite "layered.intermediate.labelSideSelector.endLabels" do
  let ((p1, p2, t1, t2, west, e1), a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 2 (({} : PropertyMap).set LayeredOptions.EDGE_LABELS_SIDE_SELECTION EdgeLabelSideSelection.smartDown)
    let n ← addNode g layers[0]! .normal
    let m ← addNode g layers[1]! .normal
    let p1 ← addPort n .east
    let p2 ← addPort n .east
    let pw ← addPort n .west
    let tailProps := ({} : PropertyMap).set LayeredOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.tail
    let e1 ← connect p1 (← addPort m .west)
    let e2 ← connect p2 (← addPort m .west)
    let t1 ← mkLabel "t1" 5.0 5.0 tailProps
    let t2 ← mkLabel "t2" 5.0 5.0 tailProps
    addEdgeLabel e1 t1
    addEdgeLabel e2 t2
    -- a west port with an edge but a center label: gathered as an empty list
    let w ← mkLabel "w" 5.0 5.0
    let ew ← connect (← addPort m .east) pw
    addEdgeLabel ew w
    runProc LabelSideSelector.processor g
    return (p1, p2, t1, t2, w, e1))
  checkEq "hand: first east port end labels ABOVE" (a.label t1).internal.labelSide LabelSide.above
  checkEq "hand: second east port end labels BELOW" (a.label t2).internal.labelSide LabelSide.below
  checkEq "hand: END_LABEL_EDGE recorded" (a.label t1).internal.endLabelEdge (some e1)
  checkFloat "hand: MAX_EDGE_THICKNESS of the port" (a.port p1).internal.maxEdgeThickness 1.0
  checkFloat "hand: second port MAX_EDGE_THICKNESS" (a.port p2).internal.maxEdgeThickness 1.0
  checkEq "hand: center label of the west port's edge untouched" (a.label west).internal.labelSide LabelSide.unknown

-- ===============================================================================================
-- LabelManagementProcessor

/-- Rust `FixedLabelManager`: every label becomes `(targetWidth / 2, 5)`. -/
def fixedLabelManager : LabelManagementProcessor.LabelManager :=
  { manageLabelSize := fun _ targetWidth => pure (some ⟨targetWidth / 2.0, 5.0⟩) }

/-- Rust `add_label_with_origin`. -/
def labelWithOrigin (w h : Float) (id : Nat) : LayeredM LLabelId :=
  LayeredM.createLabel s!"label-{id}" { size := ⟨w, h⟩, internal := { origin := some (.elkLabel ⟨id⟩) } }

def managementTests : Suite := suite "layered.intermediate.labelManagementProcessor" do
  -- non_center_mode_manages_node_port_and_edge_labels
  let ((g, nodeLabel, portLabel, edgeLabel), a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 1 (({} : PropertyMap).set LayeredOptions.DIRECTION Direction.right
      |>.set LayeredOptions.SPACING_LABEL_LABEL 3.0)
    let node ← addNode g layers[0]! .normal
    let nodeLabel ← labelWithOrigin 100.0 12.0 1
    LayeredM.modifyNode node fun x => { x with labels := #[nodeLabel] }
    let nodePort ← addPort node .east
    let portLabel ← labelWithOrigin 70.0 11.0 2
    LayeredM.modifyPort nodePort fun x => { x with labels := #[portLabel] }
    let other ← addNode g layers[0]! .normal
    let otherPort ← addPort other .west
    let edge ← connect nodePort otherPort
    let edgeLabel ← labelWithOrigin 90.0 10.0 3
    addEdgeLabel edge edgeLabel
    LabelManagementProcessor.processWith false fixedLabelManager g
    return (g, nodeLabel, portLabel, edgeLabel))
  checkVec "non_center_mode_manages_node_port_and_edge_labels: node label" (a.label nodeLabel).size ⟨20.0, 5.0⟩
  checkVec "non_center_mode_manages_node_port_and_edge_labels: port label" (a.label portLabel).size ⟨10.0, 5.0⟩
  checkVec "non_center_mode_manages_node_port_and_edge_labels: edge label" (a.label edgeLabel).size ⟨30.0, 5.0⟩
  -- without a label manager (labelManagerOf = none) the registered processor changes nothing
  let ((), a') ← LayeredM.run (do
    let l := nodeLabel
    LayeredM.modifyLabel l fun x => { x with size := ⟨100.0, 12.0⟩ }
    runProc LabelManagementProcessor.endNodePortProcessor g) a
  checkVec "hand: no label manager → labels unchanged" (a'.label nodeLabel).size ⟨100.0, 12.0⟩
  -- center_mode_updates_label_dummy_size_with_spacing_and_edge_thickness
  let (dummy, b) ← LayeredM.run (do
    let (g, layers) ← mkGraph 1 (({} : PropertyMap).set LayeredOptions.DIRECTION Direction.right
      |>.set LayeredOptions.SPACING_EDGE_LABEL 2.0 |>.set LayeredOptions.SPACING_LABEL_LABEL 1.0)
    let normal ← addNode g layers[0]! .normal { size := ⟨200.0, 30.0⟩ }
    let dummy ← addNode g layers[0]! .label { size := ⟨10.0, 10.0⟩ }
    let sourcePort ← addPort normal .east
    let dummyPort ← addPort dummy .west
    let _ ← connect sourcePort dummyPort { props := ({} : PropertyMap).set CoreOptions.EDGE_THICKNESS 4.0 }
    let l1 ← labelWithOrigin 80.0 9.0 11
    let l2 ← labelWithOrigin 70.0 7.0 12
    setRepresented dummy #[l1, l2]
    LabelManagementProcessor.processWith true fixedLabelManager g
    return dummy)
  -- targetWidth = max(60, 200) → (100, 5) per label; required (100, 5 + 1 + 5) + 4 + 2
  checkVec "center_mode_updates_label_dummy_size_with_spacing_and_edge_thickness" (b.node dummy).size ⟨100.0, 17.0⟩
  -- vertical_layout_swaps_label_dimensions_from_manager_output
  let (label, c) ← LayeredM.run (do
    let (g, layers) ← mkGraph 1 (({} : PropertyMap).set LayeredOptions.DIRECTION Direction.down)
    let node ← addNode g layers[0]! .normal
    let label ← labelWithOrigin 55.0 11.0 21
    LayeredM.modifyNode node fun x => { x with labels := #[label] }
    LabelManagementProcessor.processWith false fixedLabelManager g
    return label)
  checkVec "vertical_layout_swaps_label_dimensions_from_manager_output" (c.label label).size ⟨5.0, 20.0⟩

-- ===============================================================================================
-- EndLabelSorter

open Elk.Alg.Common.NodeSpacing in
/-- The end label cell of `labels` (horizontal layout mode). -/
def endCell (labels : Array LLabelId) : CellSystem.Cell LLabelId :=
  let d0 : CellSystem.LabelCellData LLabelId := { gap := 1.0, horizontalLayoutMode := true }
  { kind := .label (labels.foldl (fun d l => CellSystem.LabelCell.addLabel d l ⟨10.0, 4.0⟩) d0) }

open Elk.Alg.Common.NodeSpacing in
/-- The labels of an end label cell, in cell order. -/
def endCellLabels (cell : CellSystem.Cell LLabelId) : Array LLabelId :=
  match cell.kind with
  | .label d => d.labels.map (·.1)
  | _ => #[]

def sorterTests : Suite := suite "layered.intermediate.endLabelSorter" do
  -- Java `EndLabelSorter`: the end labels of a port with two edges carrying tail labels are grouped
  -- by edge and sorted by target node id (ids assigned in layer/node/port order)
  let tailProps : PropertyMap := ({} : PropertyMap).set LayeredOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.tail
  let ((src, ok1, ok2, ok3), a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 2
    let src ← addNode g layers[0]! .normal
    let out ← addPort src .east
    let t1 ← addNode g layers[1]! .normal
    let t2 ← addNode g layers[1]! .normal
    let e2 ← connect out (← addPort t2 .west)
    let e1 ← connect out (← addPort t1 .west)
    let l2a ← mkLabel "e2a" 10.0 4.0 tailProps
    let l1 ← mkLabel "e1" 10.0 4.0 tailProps
    let l2b ← mkLabel "e2b" 10.0 4.0 tailProps
    addEdgeLabel e2 l2a
    addEdgeLabel e2 l2b
    addEdgeLabel e1 l1
    for (l, e) in #[(l2a, e2), (l1, e1), (l2b, e2)] do
      LayeredM.modifyLabel l fun x => { x with internal := { x.internal with endLabelEdge := some e } }
    LayeredM.modifyNode src fun x => { x with internal := { x.internal with
      endLabels := some #[(out, endCell #[l2a, l1, l2b])] } }
    runProc EndLabelSorter.processor g
    return (src, l1, l2a, l2b))
  let cell := ((a.node src).internal.endLabels.getD #[])[0]!.2
  checkEq "groups sorted by target node id, labels of a group stay together" (endCellLabels cell) #[ok1, ok2, ok3]
  -- a port that needs sorting without a label cell: Java `createLabelGroups(null)` throws
  checkThrows "port without label cell throws NullPointerException" (do
    let _ ← LayeredM.run (do
      let (g, layers) ← mkGraph 2
      let src ← addNode g layers[0]! .normal
      let out ← addPort src .east
      let other ← addPort src .east
      let t ← addNode g layers[1]! .normal
      let e1 ← connect out (← addPort t .west)
      let e2 ← connect out (← addPort t .west)
      addEdgeLabel e1 (← mkLabel "a" 10.0 4.0 tailProps)
      addEdgeLabel e2 (← mkLabel "b" 10.0 4.0 tailProps)
      LayeredM.modifyNode src fun x => { x with internal := { x.internal with
        endLabels := some #[(other, endCell #[])] } }
      runProc EndLabelSorter.processor g)
    pure ())

-- ===============================================================================================
-- EndLabelPostprocessor

open Elk.Alg.Common.NodeSpacing in
def postprocessorTests : Suite := suite "layered.intermediate.endLabelPostprocessor" do
  let ((l1, l2, node), a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 1
    let node ← addNode g layers[0]! .normal { position := ⟨100.0, 200.0⟩ }
    let port ← addPort node .east
    let l1 ← mkLabel "a" 10.0 4.0
    let l2 ← mkLabel "b" 20.0 6.0
    let d0 : CellSystem.LabelCellData LLabelId := { gap := 1.0, horizontalLayoutMode := true }
    let d := CellSystem.LabelCell.addLabel (CellSystem.LabelCell.addLabel d0 l1 ⟨10.0, 4.0⟩) l2 ⟨20.0, 6.0⟩
    let cell : CellSystem.Cell LLabelId := { cellRectangle := ⟨5.0, 6.0, 30.0, 20.0⟩, kind := .label d }
    EndLabelPostprocessor.processNode node #[(port, cell)]
    -- the registered processor finds no END_LABELS (TODO(end-labels)) and changes nothing
    runProc EndLabelPostprocessor.processor g
    return (l1, l2, node))
  -- cell moved to (105, 206); content height 4 + 6 + 1 = 11 → y = 206 + (20 - 11) / 2
  checkVec "hand: first end label centred in the moved cell" (a.label l1).position ⟨115.0, 210.5⟩
  checkVec "hand: second end label below the first" (a.label l2).position ⟨110.0, 215.5⟩
  checkVec "hand: node position unchanged" (a.node node).position ⟨100.0, 200.0⟩
  -- vertical mode (labels side by side), top aligned
  let ((m1, m2), b) ← LayeredM.run (do
    let (g, layers) ← mkGraph 1
    let node ← addNode g layers[0]! .externalPort { position := ⟨1.0, 2.0⟩ }
    let port ← addPort node .east
    let m1 ← mkLabel "a" 10.0 4.0
    let m2 ← mkLabel "b" 20.0 6.0
    let d0 : CellSystem.LabelCellData LLabelId :=
      { gap := 2.0, horizontalLayoutMode := false, verticalAlignment := .top, horizontalAlignment := .left }
    let d := CellSystem.LabelCell.addLabel (CellSystem.LabelCell.addLabel d0 m1 ⟨10.0, 4.0⟩) m2 ⟨20.0, 6.0⟩
    let cell : CellSystem.Cell LLabelId := { cellRectangle := ⟨0.0, 0.0, 40.0, 10.0⟩, kind := .label d }
    EndLabelPostprocessor.processNode node #[(port, cell)]
    return (m1, m2))
  checkVec "hand: vertical mode first label" (b.label m1).position ⟨1.0, 2.0⟩
  checkVec "hand: vertical mode second label at x + 10 + gap" (b.label m2).position ⟨13.0, 2.0⟩

-- ===============================================================================================
-- LayerSizeAndGraphHeightCalculator

/-- Rust `layer_size_and_graph_height_calculator_contains_all_nodes` /
`layer_size_and_graph_heigth_calculator_bounds_all_nodes` + hand values (with margins). -/
def layerSizeTests : Suite := suite "layered.intermediate.layerSizeAndGraphHeightCalculator" do
  let ((g, layers, nodes), a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 2
    let n1 ← addNode g layers[0]! .normal
      { position := ⟨0.0, -5.0⟩, size := ⟨20.0, 12.0⟩, margin := { top := 1.0, bottom := 2.0, left := 1.5, right := 2.5 } }
    let n2 ← addNode g layers[1]! .normal
      { position := ⟨0.0, 30.0⟩, size := ⟨25.0, 10.0⟩, margin := { top := 0.5, bottom := 2.0 } }
    runProc LayerSizeAndGraphHeightCalculator.processor g
    return (g, layers, #[n1, n2]))
  let gr := a.graph g
  let top := -gr.offset.y
  let bottom := gr.size.y - gr.offset.y
  let tol := 1e-6
  for n in nodes do
    let nd := a.node n
    let nodeTop := nd.position.y - nd.margin.top
    let nodeBottom := nd.position.y + nd.size.y + nd.margin.bottom
    check s!"layer_size_and_graph_height_calculator_contains_all_nodes: top of {n}" (nodeTop > top || (nodeTop - top).abs < tol)
    check s!"layer_size_and_graph_height_calculator_contains_all_nodes: bottom of {n}" (nodeBottom < bottom || (nodeBottom - bottom).abs < tol)
  -- hand: layer 0: width 20 + 1.5 + 2.5, top -6, bottom 9; layer 1: width 25, top 29.5, bottom 42
  checkVec "hand: layer 0 size" (a.layer layers[0]!).size ⟨24.0, 15.0⟩
  checkVec "hand: layer 1 size" (a.layer layers[1]!).size ⟨25.0, 12.5⟩
  checkFloat "hand: graph height maxY - minY = 42 + 6" gr.size.y 48.0
  checkFloat "hand: graph offset -= minY" gr.offset.y 6.0
  -- external port dummies add the surrounding port spacing; empty layers get size 0
  let ((g2, layers2), b) ← LayeredM.run (do
    let props := ({} : PropertyMap).set LayeredOptions.SPACING_PORTS_SURROUNDING ({ top := 3.0, bottom := 4.0 } : ElkMargin)
    let (g, layers) ← mkGraph 2 props
    LayeredM.modifyLayer layers[1]! fun l => { l with size := ⟨7.0, 7.0⟩ }
    let _ ← addNode g layers[0]! .externalPort { position := ⟨0.0, 10.0⟩, size := ⟨5.0, 5.0⟩ }
    let _ ← addNode g layers[0]! .normal { position := ⟨0.0, 20.0⟩, size := ⟨5.0, 5.0⟩ }
    let _ ← addNode g layers[0]! .externalPort { position := ⟨0.0, 30.0⟩, size := ⟨5.0, 5.0⟩ }
    LayeredM.modifyGraph g fun x => { x with offset := ⟨0.0, 1.0⟩ }
    runProc LayerSizeAndGraphHeightCalculator.processor g
    return (g, layers))
  -- top 10 - 3 = 7, bottom 35 + 4 = 39
  checkVec "hand: external port spacing in the layer height" (b.layer layers2[0]!).size ⟨5.0, 32.0⟩
  checkVec "hand: empty layer size reset to 0" (b.layer layers2[1]!).size ⟨0.0, 0.0⟩
  checkFloat "hand: graph height with port spacing" (b.graph g2).size.y 32.0
  checkFloat "hand: offset 1 - 7" (b.graph g2).offset.y (-6.0)
  -- no nodes at all: height 0, offset unchanged
  let (g3, c) ← LayeredM.run (do
    let (g, _) ← mkGraph 1
    LayeredM.modifyGraph g fun x => { x with offset := ⟨0.0, 5.0⟩, size := ⟨0.0, 99.0⟩ }
    runProc LayerSizeAndGraphHeightCalculator.processor g
    return g)
  checkFloat "hand: no nodes → height 0" (c.graph g3).size.y 0.0
  checkFloat "hand: no nodes → offset unchanged" (c.graph g3).offset.y 5.0

-- ===============================================================================================
-- Graph properties and registration

/-- Rust `graph_properties_include_end_labels` (importer test) on a hand-built layerless graph:
`computeGraphProperties` flags `END_LABELS` for a tail label. -/
def graphPropertiesTests : Suite := suite "layered.intermediate.labels.registration" do
  let (g, a) ← LayeredM.run (do
    let g ← LayeredM.createGraph
    let n1 ← LayeredM.createNode g
    let n2 ← LayeredM.createNode g
    LayeredM.modifyGraph g fun x => { x with layerlessNodes := #[n1, n2] }
    let p1 ← LayeredM.createPort
    let p2 ← LayeredM.createPort
    LayeredM.setPortNode p1 (some n1)
    LayeredM.setPortNode p2 (some n2)
    let e ← connect p1 p2
    addEdgeLabel e (← mkLabel "tail" 1.0 1.0 (({} : PropertyMap).set CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.tail))
    LGraphUtil.computeGraphProperties g
    return g)
  check "graph_properties_include_end_labels" ((a.graph g).internal.graphProperties.contains .endLabels)
  let expected : Array (IntermediateProcessorStrategy × String) := #[
    (.labelDummyInserter, "LabelDummyInserter"), (.labelDummySwitcher, "LabelDummySwitcher"),
    (.endNodePortLabelManagementProcessor, "LabelManagementProcessor"),
    (.centerLabelManagementProcessor, "LabelManagementProcessor"), (.labelSideSelector, "LabelSideSelector"),
    (.layerSizeAndGraphHeightCalculator, "LayerSizeAndGraphHeightCalculator"),
    (.labelDummyRemover, "LabelDummyRemover"), (.endLabelSorter, "EndLabelSorter"),
    (.endLabelPostprocessor, "EndLabelPostprocessor")]
  for (s, name) in expected do
    check s!"registered: {s}" (← IntermediateProcessorStrategy.isAvailable s)
    checkEq s!"processor name of {s}" (← IntermediateProcessorStrategy.create s).name name

def suites : Array Suite :=
  #[inserterTests, inserterTests2, switcherTests, switcherStrategyTests, removerTests, sideSelectorTests,
    sideStrategyTests, sideEndLabelTests, managementTests, sorterTests, postprocessorTests, layerSizeTests,
    graphPropertiesTests]

end Tests.Layered.IntermediateLabels
