import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Intermediate.NodeSizeProcessors
/-!
# Tests of the node size and margin processors (task I1b)

`LabelAndNodeSizeProcessor` (with its phase-1 helpers and the phase-3 external port dummy labels),
`InnermostNodeMarginCalculator`, `EndLabelPreprocessor` and `NodePlacementRepeater` on hand-built
layered graphs.

* "oracle: …" values were produced by the elk-rs oracle (`scripts/oracle_layout.sh` with a trace
  directory): the hand-built graphs reproduce the state of the trace step before the processor
  (node and port sizes, port order and positions, labels, options) and the checks compare with the
  trace step after it (`step_*_LabelAndNodeSizeProcessor.json`, `…_InnermostNodeMarginCalculator`,
  `…_EndLabelPreprocessor`). The models are described next to each suite.
* "hand: …" values are derived by hand from the Rust code (comments give the arithmetic).
* elk-rs tests are ported with their names in the check names: `node_placement_repeater_test.rs`
  (all three tests; the configurator one at configuration level, because the crossing minimizer is
  not ported yet), `end_label_pre_and_postprocessor_strategies_are_stable_on_simple_graph`
  (`intermediate_processors_test.rs`) and the pipeline-driven
  `label_and_node_size_processor_applies_port_offsets` and the port label placement variants
  (`port_label_placement_variants_test.rs`) asserted on hand-built graphs.
-/
namespace Tests.Layered.IntermediateNodeSize

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Alg Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate
open Elk.Alg.Layered.Intermediate.LabelAndNodeSize

def checkVec (name : String) (actual expected : KVector) : TestM Unit := do
  checkFloat s!"{name} x" actual.x expected.x
  checkFloat s!"{name} y" actual.y expected.y

def checkMargin (name : String) (m : ElkMargin) (top right bottom left : Float) : TestM Unit := do
  checkFloat s!"{name} top" m.top top
  checkFloat s!"{name} right" m.right right
  checkFloat s!"{name} bottom" m.bottom bottom
  checkFloat s!"{name} left" m.left left

/-- Runs a processor with a null monitor. -/
def runProc (p : LayeredProcessor) (g : LGraphId) : LayeredM Unit := p.process g ProgressMonitor.null

/-- A graph with `n` layers (ids = indices) and `Spacings.new props`. -/
def mkGraph (n : Nat) (props : PropertyMap := {}) : LayeredM (LGraphId × Array LayerId) := do
  let g ← LayeredM.createGraph { props := props }
  let mut layers : Array LayerId := #[]
  for i in [0:n] do
    let l ← LayeredM.createLayer g
    LayeredM.modifyLayer l fun x => { x with id := (i : Int) }
    layers := layers.push l
  let ls := layers
  LayeredM.modifyGraph g fun x =>
    { x with layers := ls, internal := { x.internal with spacings := some (Spacings.new props) } }
  return (g, layers)

/-- A node of the given size and options appended to `layer`. -/
def addNode (g : LGraphId) (layer : LayerId) (w h : Float) (props : PropertyMap := {}) (n : LNode := {}) :
    LayeredM LNodeId := do
  let node ← LayeredM.createNode g { n with size := ⟨w, h⟩, props := props }
  LayeredM.setNodeLayer node (some layer)
  return node

/-- A port of the given size, side (anchor from `setSide`) and position. -/
def addPort (node : LNodeId) (side : PortSide) (w h : Float) (pos : KVector := {}) (props : PropertyMap := {}) :
    LayeredM LPortId := do
  let p ← LayeredM.createPort { size := ⟨w, h⟩, position := pos, props := props }
  LayeredM.modifyPort p (·.setSide side)
  LayeredM.setPortNode p (some node)
  return p

def addPortLabel (port : LPortId) (text : String) (w h : Float) : LayeredM LLabelId := do
  let l ← LayeredM.createLabel text { size := ⟨w, h⟩ }
  LayeredM.modifyPort port fun x => { x with labels := x.labels.push l }
  return l

def addNodeLabel (node : LNodeId) (text : String) (w h : Float) : LayeredM LLabelId := do
  let l ← LayeredM.createLabel text { size := ⟨w, h⟩ }
  LayeredM.modifyNode node fun x => { x with labels := x.labels.push l }
  return l

def connect (s t : LPortId) (e : LEdge := {}) : LayeredM LEdgeId := do
  let edge ← LayeredM.createEdge e
  LayeredM.setEdgeSource edge (some s)
  LayeredM.setEdgeTarget edge (some t)
  return edge

def addEdgeLabel (e : LEdgeId) (text : String) (w h : Float) (placement : EdgeLabelPlacement) : LayeredM LLabelId := do
  let l ← LayeredM.createLabel text
    { size := ⟨w, h⟩, props := ({} : PropertyMap).set CoreOptions.EDGE_LABELS_PLACEMENT placement }
  LayeredM.modifyEdge e fun x => { x with labels := x.labels.push l }
  return l

/-- The `i`-th port of a node. -/
def portAt (a : LGraphArena) (n : LNodeId) (i : Nat) : LPortId := (a.node n).ports[i]!

/-- The position of the first label of a port. -/
def portLabelPos (a : LGraphArena) (p : LPortId) : KVector := (a.label (a.port p).labels[0]!).position

def sizeConstraints (cs : Array SizeConstraint) : EnumSet SizeConstraint := EnumSet.of cs
def portLabels (ps : Array PortLabelPlacement) : EnumSet PortLabelPlacement := EnumSet.of ps

-- ===============================================================================================
-- LabelAndNodeSizeProcessor + InnermostNodeMarginCalculator against the oracle

/-- The five oracle nodes in one layer (each was a separate component in the oracle models; the
graph options are the defaults plus the inferred `DIRECTION = RIGHT`):
* `A` 30×20, `[PORTS, PORT_LABELS, NODE_LABELS, MINIMUM_SIZE]`, FIXED_SIDE, node label `[H_CENTER,
  V_TOP, INSIDE]` 40×12, OUTSIDE port labels; ports (sorted) NORTH 8×8 label 10×6, EAST 8×8 label
  15×10, EAST 8×8 label 12×10, WEST 8×8;
* `B` 60×40, `[PORTS, PORT_LABELS]`, FIXED_POS, INSIDE; EAST (60, 5) label 14×8, EAST (60, 25)
  label 10×8, SOUTH (20, 40) label 12×6 (ports 6×6);
* `C` 20×20, `[PORTS, PORT_LABELS]`, FIXED_ORDER, `[OUTSIDE, SPACE_EFFICIENT]`; WEST ports 5×5 at
  y 15, 9, 2 (sorted) with labels 13×7, 9×7, 11×7;
* `D` 80×30, FIXED_RATIO, fixed size; NORTH (20, -4), SOUTH (60, 30) (4×4);
* `E` 10×10, `[PORTS, PORT_LABELS, NODE_LABELS]`, FIXED_SIDE, node label `[H_CENTER, V_TOP,
  OUTSIDE]` 30×9, `[INSIDE, NEXT_TO_PORT_IF_POSSIBLE]`; two WEST ports 6×6 at (0, 0) with labels
  16×8 and 8×8. -/
def buildOracleNodes : LayeredM (LGraphId × Array LNodeId) := do
  let (g, layers) ← mkGraph 1 (({} : PropertyMap).set CoreOptions.DIRECTION Direction.right)
  let l := layers[0]!
  -- A
  let propsA := ({} : PropertyMap)
    |>.set CoreOptions.NODE_SIZE_CONSTRAINTS (sizeConstraints #[.ports, .portLabels, .nodeLabels, .minimumSize])
    |>.set CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
    |>.set CoreOptions.NODE_LABELS_PLACEMENT (EnumSet.of #[NodeLabelPlacement.hCenter, .vTop, .inside])
    |>.set CoreOptions.PORT_LABELS_PLACEMENT (portLabels #[.outside])
  let nA ← addNode g l 30.0 20.0 propsA
  let _ ← addNodeLabel nA "node1" 40.0 12.0
  let _ ← addPortLabel (← addPort nA .north 8.0 8.0) "c" 10.0 6.0
  let _ ← addPortLabel (← addPort nA .east 8.0 8.0) "a" 15.0 10.0
  let _ ← addPortLabel (← addPort nA .east 8.0 8.0) "b" 12.0 10.0
  let _ ← addPort nA .west 8.0 8.0
  -- B
  let propsB := ({} : PropertyMap)
    |>.set CoreOptions.NODE_SIZE_CONSTRAINTS (sizeConstraints #[.ports, .portLabels])
    |>.set CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedPos
    |>.set CoreOptions.PORT_LABELS_PLACEMENT (portLabels #[.inside])
  let nB ← addNode g l 60.0 40.0 propsB
  let _ ← addPortLabel (← addPort nB .east 6.0 6.0 ⟨60.0, 5.0⟩) "e1" 14.0 8.0
  let _ ← addPortLabel (← addPort nB .east 6.0 6.0 ⟨60.0, 25.0⟩) "e2" 10.0 8.0
  let _ ← addPortLabel (← addPort nB .south 6.0 6.0 ⟨20.0, 40.0⟩) "s" 12.0 6.0
  -- C
  let propsC := ({} : PropertyMap)
    |>.set CoreOptions.NODE_SIZE_CONSTRAINTS (sizeConstraints #[.ports, .portLabels])
    |>.set CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedOrder
    |>.set CoreOptions.PORT_LABELS_PLACEMENT (portLabels #[.outside, .spaceEfficient])
  let nC ← addNode g l 20.0 20.0 propsC
  let _ ← addPortLabel (← addPort nC .west 5.0 5.0 ⟨-5.0, 15.0⟩) "w3" 13.0 7.0
  let _ ← addPortLabel (← addPort nC .west 5.0 5.0 ⟨-5.0, 9.0⟩) "w2" 9.0 7.0
  let _ ← addPortLabel (← addPort nC .west 5.0 5.0 ⟨-5.0, 2.0⟩) "w1" 11.0 7.0
  -- D
  let nD ← addNode g l 80.0 30.0 (({} : PropertyMap).set CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedRatio)
  let _ ← addPort nD .north 4.0 4.0 ⟨20.0, -4.0⟩
  let _ ← addPort nD .south 4.0 4.0 ⟨60.0, 30.0⟩
  -- E
  let propsE := ({} : PropertyMap)
    |>.set CoreOptions.NODE_SIZE_CONSTRAINTS (sizeConstraints #[.ports, .portLabels, .nodeLabels])
    |>.set CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
    |>.set CoreOptions.NODE_LABELS_PLACEMENT (EnumSet.of #[NodeLabelPlacement.hCenter, .vTop, .outside])
    |>.set CoreOptions.PORT_LABELS_PLACEMENT (portLabels #[.inside, .nextToPortIfPossible])
  let nE ← addNode g l 10.0 10.0 propsE
  let _ ← addNodeLabel nE "outer" 30.0 9.0
  let _ ← addPortLabel (← addPort nE .west 6.0 6.0) "x1" 16.0 8.0
  let _ ← addPortLabel (← addPort nE .west 6.0 6.0) "x2" 8.0 8.0
  return (g, #[nA, nB, nC, nD, nE])

def oracleSizeTests : Suite := suite "layered.intermediate.labelAndNodeSizeProcessor.oracle" do
  let ((nodes, before), a) ← LayeredM.run (do
    let (g, nodes) ← buildOracleNodes
    runProc LabelAndNodeSizeProcessor.processor g
    let before := (← get).nodes.map (·.margin)
    runProc InnermostNodeMarginCalculator.processor g
    return (nodes, before))
  let nA := nodes[0]!
  let nB := nodes[1]!
  let nC := nodes[2]!
  let nD := nodes[3]!
  let nE := nodes[4]!
  -- A
  checkVec "oracle: A size" (a.node nA).size ⟨50.0, 46.0⟩
  checkVec "oracle: A inside node label" (a.label (a.node nA).labels[0]!).position ⟨5.0, 5.0⟩
  checkVec "oracle: A north port" (a.port (portAt a nA 0)).position ⟨21.0, -8.0⟩
  checkVec "oracle: A north port label" (portLabelPos a (portAt a nA 0)) ⟨9.0, -7.0⟩
  checkVec "oracle: A first east port" (a.port (portAt a nA 1)).position ⟨50.0, 10.0⟩
  checkVec "oracle: A first east port label above" (portLabelPos a (portAt a nA 1)) ⟨9.0, -11.0⟩
  checkVec "oracle: A second east port" (a.port (portAt a nA 2)).position ⟨50.0, 28.0⟩
  checkVec "oracle: A second east port label below" (portLabelPos a (portAt a nA 2)) ⟨9.0, 9.0⟩
  checkVec "oracle: A west port" (a.port (portAt a nA 3)).position ⟨-8.0, 19.0⟩
  -- B (FIXED_POS shrinks to the inside labels; ports keep their axis coordinate)
  checkVec "oracle: B size" (a.node nB).size ⟨30.0, 31.0⟩
  checkVec "oracle: B east port 1" (a.port (portAt a nB 0)).position ⟨30.0, 5.0⟩
  checkVec "oracle: B east port 1 inside label" (portLabelPos a (portAt a nB 0)) ⟨-15.0, -1.0⟩
  checkVec "oracle: B east port 2" (a.port (portAt a nB 1)).position ⟨30.0, 25.0⟩
  checkVec "oracle: B east port 2 inside label" (portLabelPos a (portAt a nB 1)) ⟨-11.0, -1.0⟩
  checkVec "oracle: B south port" (a.port (portAt a nB 2)).position ⟨20.0, 31.0⟩
  checkVec "oracle: B south port inside label" (portLabelPos a (portAt a nB 2)) ⟨-6.0, -7.0⟩
  -- C
  checkVec "oracle: C size (west ports only)" (a.node nC).size ⟨0.0, 63.0⟩
  checkVec "oracle: C port w3" (a.port (portAt a nC 0)).position ⟨-5.0, 48.0⟩
  checkVec "oracle: C label w3" (portLabelPos a (portAt a nC 0)) ⟨-14.0, 6.0⟩
  checkVec "oracle: C port w2" (a.port (portAt a nC 1)).position ⟨-5.0, 25.0⟩
  checkVec "oracle: C label w2" (portLabelPos a (portAt a nC 1)) ⟨-10.0, 6.0⟩
  checkVec "oracle: C port w1" (a.port (portAt a nC 2)).position ⟨-5.0, 10.0⟩
  checkVec "oracle: C label w1 (space efficient: above)" (portLabelPos a (portAt a nC 2)) ⟨-12.0, -8.0⟩
  -- D (the port contexts' ratio stays 0)
  checkVec "oracle: D size unchanged" (a.node nD).size ⟨80.0, 30.0⟩
  checkVec "oracle: D north port" (a.port (portAt a nD 0)).position ⟨0.0, -4.0⟩
  checkVec "oracle: D south port" (a.port (portAt a nD 1)).position ⟨0.0, 30.0⟩
  -- E
  checkVec "oracle: E size" (a.node nE).size ⟨34.0, 46.0⟩
  checkVec "oracle: E outside node label" (a.label (a.node nE).labels[0]!).position ⟨2.0, -14.0⟩
  checkVec "oracle: E west port 1" (a.port (portAt a nE 0)).position ⟨-6.0, 29.0⟩
  checkVec "oracle: E west port 1 label" (portLabelPos a (portAt a nE 0)) ⟨7.0, -1.0⟩
  checkVec "oracle: E west port 2" (a.port (portAt a nE 1)).position ⟨-6.0, 11.0⟩
  checkVec "oracle: E west port 2 label" (portLabelPos a (portAt a nE 1)) ⟨7.0, -1.0⟩
  -- the processor itself leaves the margins at 0 (default path)
  check "oracle: LabelAndNodeSizeProcessor keeps zero margins" (before.all (· == ({} : ElkMargin)))
  -- InnermostNodeMarginCalculator
  checkMargin "oracle: A margins" (a.node nA).margin 15.0 24.0 1.0 8.0
  checkMargin "oracle: B margins" (a.node nB).margin 0.0 6.0 6.0 0.0
  checkMargin "oracle: C margins" (a.node nC).margin 0.0 0.0 0.0 19.0
  checkMargin "oracle: D margins" (a.node nD).margin 4.0 0.0 4.0 0.0
  checkMargin "oracle: E margins" (a.node nE).margin 14.0 0.0 0.0 6.0

/-- Rust `label_and_node_size_processor_applies_port_offsets` (pipeline test) on hand-built nodes:
100×100 nodes with FIXED_SIDE / FIXED_ORDER / FIXED_RATIO / FIXED_POS ports far away from the
node (border offset 0) end up touching the node border. -/
def portOffsetTests : Suite := suite "layered.intermediate.labelAndNodeSizeProcessor.portOffsets" do
  let (nodes, a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 4 (({} : PropertyMap).set CoreOptions.DIRECTION Direction.right)
    let zero := ({} : PropertyMap).set CoreOptions.PORT_BORDER_OFFSET 0.0
    let mut nodes : Array LNodeId := #[]
    let mut previousEast : Option LPortId := none
    let constraints := #[PortConstraints.fixedSide, .fixedOrder, .fixedRatio, .fixedPos]
    for i in [0:constraints.size] do
      let node ← addNode g layers[i]! 100.0 100.0 (({} : PropertyMap).set CoreOptions.PORT_CONSTRAINTS constraints[i]!)
      let _ ← addPort node .north 10.0 10.0 ⟨50.0, -300.0⟩ zero
      let _ ← addPort node .south 10.0 10.0 ⟨50.0, 300.0⟩ zero
      let east ← addPort node .east 10.0 10.0 ⟨300.0, 50.0⟩ zero
      let west ← addPort node .west 10.0 10.0 ⟨-300.0, 50.0⟩ zero
      if let some prev := previousEast then
        let _ ← connect prev west
      previousEast := some east
      nodes := nodes.push node
    runProc LabelAndNodeSizeProcessor.processor g
    return nodes)
  for node in nodes do
    let nd := a.node node
    for port in nd.ports do
      let pt := a.port port
      match pt.side with
      | .north => checkFloat s!"label_and_node_size_processor_applies_port_offsets: north port of {node} touches border" pt.position.y (-pt.size.y) 1e-6
      | .south => checkFloat s!"label_and_node_size_processor_applies_port_offsets: south port of {node} touches border" pt.position.y nd.size.y 1e-6
      | .east => checkFloat s!"label_and_node_size_processor_applies_port_offsets: east port of {node} touches border" pt.position.x nd.size.x 1e-6
      | .west => checkFloat s!"label_and_node_size_processor_applies_port_offsets: west port of {node} touches border" pt.position.x (-pt.size.x) 1e-6
      | .undefined => pure ()

/-- `port_label_placement_variants_test.rs` assertions on hand-built nodes of
`port_label_placement_variants.elkt` (120×80/90 nodes, FIXED_POS EAST ports 10×10 at x = 110, labels
24×10, no edges): label y < 0 = above, > 0 = below, centred = `label_y + h / 2 = port_h / 2`. -/
def variantNode (g : LGraphId) (layer : LayerId) (placement : Array PortLabelPlacement) (ys : Array Float)
    (h : Float) : LayeredM LNodeId := do
  let props := ({} : PropertyMap)
    |>.set CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedPos
    |>.set CoreOptions.PORT_LABELS_PLACEMENT (portLabels placement)
  let n ← addNode g layer 120.0 h props
  for y in ys do
    let _ ← addPortLabel (← addPort n .east 10.0 10.0 ⟨110.0, y⟩) "l" 24.0 10.0
  return n

def variantTests : Suite := suite "layered.intermediate.labelAndNodeSizeProcessor.portLabelVariants" do
  let (nodes, a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 1 (({} : PropertyMap).set CoreOptions.DIRECTION Direction.right)
    let l := layers[0]!
    let two := #[10.0, 45.0]
    let three := #[8.0, 35.0, 62.0]
    let o2d ← variantNode g l #[.outside] two 80.0
    let o2s ← variantNode g l #[.outside, .alwaysSameSide] two 80.0
    let o2n ← variantNode g l #[.outside, .nextToPortIfPossible] two 80.0
    let o3d ← variantNode g l #[.outside] three 90.0
    let o3s ← variantNode g l #[.outside, .spaceEfficient] three 90.0
    let i2d ← variantNode g l #[.inside] two 80.0
    runProc LabelAndNodeSizeProcessor.processor g
    return #[o2d, o2s, o2n, o3d, o3s, i2d])
  let labelY := fun (n : LNodeId) (i : Nat) => (portLabelPos a (portAt a n i)).y
  let centred := fun (n : LNodeId) (i : Nat) =>
    let p := portAt a n i
    let lb := a.label (a.port p).labels[0]!
    (lb.position.y + lb.size.y / 2.0 - (a.port p).size.y / 2.0).abs ≤ 1e-6
  check "test_outside_two_default: p0 above" (labelY nodes[0]! 0 < 0.0)
  check "test_outside_two_default: p1 below" (labelY nodes[0]! 1 > 0.0)
  check "test_outside_two_same_side: p0 below" (labelY nodes[1]! 0 > 0.0)
  check "test_outside_two_same_side: p1 below" (labelY nodes[1]! 1 > 0.0)
  check "test_outside_two_next_to_port: p0 centred" (centred nodes[2]! 0)
  check "test_outside_two_next_to_port: p1 centred" (centred nodes[2]! 1)
  for i in [0:3] do
    check s!"test_outside_three_default: p{i} below" (labelY nodes[3]! i > 0.0)
  check "test_outside_three_space_efficient: p0 above" (labelY nodes[4]! 0 < 0.0)
  check "test_outside_three_space_efficient: p1 below" (labelY nodes[4]! 1 > 0.0)
  check "test_outside_three_space_efficient: p2 below" (labelY nodes[4]! 2 > 0.0)
  check "test_inside_two_default: p0 centred" (centred nodes[5]! 0)
  check "test_inside_two_default: p1 centred" (centred nodes[5]! 1)
  -- every coordinate stays finite (common_port_label_external_sweep_test)
  for n in nodes do
    for p in (a.node n).ports do
      check s!"keep_finite_geometry: port {p}" ((a.port p).position.x.isFinite && (a.port p).position.y.isFinite)
      check s!"keep_finite_geometry: label of port {p}" ((portLabelPos a p).x.isFinite && (portLabelPos a p).y.isFinite)

-- ===============================================================================================
-- Phase 3: external port dummy labels

/-- An external port dummy of size `size` whose port (at `portPos`) has labels 6×4 and 8×5;
spacings label-port 2 (horizontal) / 3 (vertical), label-label 1. -/
def extDummy (g : LGraphId) (layer : LayerId) (side : PortSide) (size portPos : KVector) :
    LayeredM (LNodeId × LPortId × LLabelId × LLabelId) := do
  let props := ({} : PropertyMap)
    |>.set CoreOptions.SPACING_LABEL_PORT_HORIZONTAL 2.0
    |>.set CoreOptions.SPACING_LABEL_PORT_VERTICAL 3.0
    |>.set CoreOptions.SPACING_LABEL_LABEL 1.0
  let d ← addNode g layer size.x size.y props { type := .externalPort, internal := { extPortSide := side } }
  let p ← addPort d side.opposed 0.0 0.0 portPos
  let l1 ← addPortLabel p "l1" 6.0 4.0
  let l2 ← addPortLabel p "l2" 8.0 5.0
  return (d, p, l1, l2)

def externalPortTests : Suite := suite "layered.intermediate.labelAndNodeSizeProcessor.externalPortDummies" do
  -- INSIDE port labels with NEXT_TO_PORT_IF_POSSIBLE; label box 8 × (4 + 5 + 1) = 8 × 10
  let ((n, e, w, other), a) ← LayeredM.run (do
    let props := ({} : PropertyMap).set CoreOptions.PORT_LABELS_PLACEMENT (portLabels #[.inside, .nextToPortIfPossible])
    let (g, layers) ← mkGraph 2 props
    LayeredM.modifyGraph g fun x => { x with internal := { x.internal with graphProperties := EnumSet.of #[.externalPorts] } }
    let n ← extDummy g layers[0]! .north ⟨10.0, 4.0⟩ ⟨3.0, 0.0⟩
    let e ← extDummy g layers[0]! .east ⟨4.0, 20.0⟩ ⟨0.0, 8.0⟩
    let w ← extDummy g layers[1]! .west ⟨4.0, 20.0⟩ ⟨0.0, 8.0⟩
    -- the west dummy's port has an edge: labels below the port
    let target ← addNode g layers[1]! 10.0 10.0 {} { type := .longEdge }
    let _ ← connect (← addPort target .east 1.0 1.0) w.2.1
    -- other dummies' port labels are touched neither by step 1 (NORMAL only) nor by phase 3
    let otherLabel ← addPortLabel (← addPort target .west 1.0 1.0) "o" 3.0 3.0
    LayeredM.modifyLabel otherLabel fun l => { l with position := ⟨77.0, 77.0⟩ }
    runProc LabelAndNodeSizeProcessor.processor g
    return (n, e, w, otherLabel))
  -- NORTH: x = (10 - 8) / 2 - 3 = -2, y = 3; second label at 3 + 4 + 1
  checkVec "hand: inside NORTH first label" (a.label n.2.2.1).position ⟨-2.0, 3.0⟩
  checkVec "hand: inside NORTH second label" (a.label n.2.2.2).position ⟨-2.0, 8.0⟩
  -- EAST, next to the port (no edges, treated as group): y = (20 - 10) / 2 - 8 = -3, x = -2 - 8
  checkVec "hand: inside EAST first label next to port" (a.label e.2.2.1).position ⟨-10.0, -3.0⟩
  checkVec "hand: inside EAST second label" (a.label e.2.2.2).position ⟨-10.0, 2.0⟩
  -- WEST with an edge: y = 20 + 3 - 8 = 15, x = 2
  checkVec "hand: inside WEST label below the port" (a.label w.2.2.1).position ⟨2.0, 15.0⟩
  checkVec "hand: long edge dummy labels untouched" (a.label other).position ⟨77.0, 77.0⟩
  -- OUTSIDE port labels, not treated as group
  let ((s, e2, e3), b) ← LayeredM.run (do
    let props := ({} : PropertyMap)
      |>.set CoreOptions.PORT_LABELS_PLACEMENT (portLabels #[.outside, .nextToPortIfPossible])
      |>.set CoreOptions.PORT_LABELS_TREAT_AS_GROUP false
    let (g, layers) ← mkGraph 1 props
    LayeredM.modifyGraph g fun x => { x with internal := { x.internal with graphProperties := EnumSet.of #[.externalPorts] } }
    let s ← extDummy g layers[0]! .south ⟨10.0, 4.0⟩ ⟨3.0, 4.0⟩
    let e2 ← extDummy g layers[0]! .east ⟨4.0, 20.0⟩ ⟨0.0, 8.0⟩
    let e3 ← extDummy g layers[0]! .east ⟨4.0, 20.0⟩ ⟨0.0, 8.0⟩
    LayeredM.modifyPort e3.2.1 fun p => { p with connectedToExternalNodes := false }
    runProc LabelAndNodeSizeProcessor.processor g
    return (s, e2, e3))
  -- SOUTH: x = 3 + 2, y stays 0
  checkVec "hand: outside SOUTH label" (b.label s.2.2.1).position ⟨5.0, 0.0⟩
  -- EAST connected to external nodes: y = 8 + 3
  checkVec "hand: outside EAST label below" (b.label e2.2.2.1).position ⟨0.0, 11.0⟩
  -- EAST not connected: centred on the first label: y = (20 - 4) / 2 - 8 = 0
  checkVec "hand: outside EAST label next to the port (first label)" (b.label e3.2.2.1).position ⟨0.0, 0.0⟩
  checkVec "hand: outside EAST second label stacked" (b.label e3.2.2.2).position ⟨0.0, 5.0⟩
  -- without EXTERNAL_PORTS nothing happens
  let (l, c) ← LayeredM.run (do
    let (g, layers) ← mkGraph 1 (({} : PropertyMap).set CoreOptions.PORT_LABELS_PLACEMENT (portLabels #[.inside]))
    let d ← extDummy g layers[0]! .north ⟨10.0, 4.0⟩ ⟨3.0, 0.0⟩
    runProc LabelAndNodeSizeProcessor.processor g
    return d.2.2.1)
  checkVec "hand: no EXTERNAL_PORTS → dummy labels untouched" (c.label l).position ⟨0.0, 0.0⟩

-- ===============================================================================================
-- Phase-1 helpers (elk-rs phase-2 workaround)

def placementHelperTests : Suite := suite "layered.intermediate.labelAndNodeSize.portPlacement" do
  let ((east, north, center, south), a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 1
    let l := layers[0]!
    -- three EAST ports 10×10 on a 100×50 node, DISTRIBUTED (default), spacing 10, no surrounding:
    -- placement 3·10 + 2·10 + 2·10 = 70 > 50 → spacing 10 + (50 - 70) / 4 = 5, start 5
    let n1 ← addNode g l 100.0 50.0
    let east ← #[0, 1, 2].mapM fun _ => addPort n1 .east 10.0 10.0
    placePortsOnSide n1 .east 100.0 50.0 10.0 {}
    -- NORTH, BEGIN, surrounding 5/5: x = 5, 5 + 10 + 10
    let n2 ← addNode g l 100.0 50.0 (({} : PropertyMap).set CoreOptions.PORT_ALIGNMENT_NORTH PortAlignment.begin)
    let north ← #[0, 1].mapM fun _ => addPort n2 .north 10.0 10.0
    placePortsOnSide n2 .north 100.0 50.0 10.0 { left := 5.0, right := 5.0 }
    -- NORTH, CENTER: x = 5 + (90 - 30) / 2 = 35, then 55
    let n3 ← addNode g l 100.0 50.0 (({} : PropertyMap).set CoreOptions.PORT_ALIGNMENT_DEFAULT PortAlignment.center)
    let center ← #[0, 1].mapM fun _ => addPort n3 .north 10.0 10.0
    placePortsOnSide n3 .north 100.0 50.0 10.0 { left := 5.0, right := 5.0 }
    -- SOUTH, JUSTIFIED: reversed order, spacing 10 + (100 - 30) / 1 = 80; border offset 2
    let n4 ← addNode g l 100.0 50.0 (({} : PropertyMap).set CoreOptions.PORT_ALIGNMENT_SOUTH PortAlignment.justified)
    let south ← #[0, 1].mapM fun _ => addPort n4 .south 10.0 10.0 {} (({} : PropertyMap).set CoreOptions.PORT_BORDER_OFFSET 2.0)
    placePortsOnSide n4 .south 100.0 50.0 10.0 {}
    return (east, north, center, south))
  checkVec "hand: distributed east port 1" (a.port east[0]!).position ⟨100.0, 5.0⟩
  checkVec "hand: distributed east port 2" (a.port east[1]!).position ⟨100.0, 20.0⟩
  checkVec "hand: distributed east port 3" (a.port east[2]!).position ⟨100.0, 35.0⟩
  checkVec "hand: begin north port 1" (a.port north[0]!).position ⟨5.0, -10.0⟩
  checkVec "hand: begin north port 2" (a.port north[1]!).position ⟨25.0, -10.0⟩
  checkFloat "hand: center north port 1" (a.port center[0]!).position.x 35.0
  checkFloat "hand: center north port 2" (a.port center[1]!).position.x 55.0
  checkVec "hand: justified south: last port first" (a.port south[1]!).position ⟨0.0, 52.0⟩
  checkVec "hand: justified south: first port last" (a.port south[0]!).position ⟨90.0, 52.0⟩

def fixedPlacementTests : Suite := suite "layered.intermediate.labelAndNodeSize.fixedPlacement" do
  let ((pe, pw, pn, ps, pr, pw2, n), a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 1
    let offset := ({} : PropertyMap).set CoreOptions.PORT_BORDER_OFFSET 2.0
    let n ← addNode g layers[0]! 40.0 20.0
    let pe ← addPort n .east 6.0 4.0 ⟨1.0, 3.0⟩ offset
    let pw ← addPort n .west 6.0 4.0 ⟨1.0, 3.0⟩
    let pn ← addPort n .north 4.0 4.0 ⟨7.0, 9.0⟩
    let ps ← addPort n .south 4.0 4.0 ⟨7.0, 0.0⟩
    LayeredM.modifyPort ps fun p => { p with internal := { p.internal with portRatioOrPosition := 0.25 } }
    -- FIXED_POS snapping keeps the axis coordinate
    adjustPortsOnSide n .east 40.0 20.0
    adjustPortsOnSide n .west 40.0 20.0
    -- FIXED_RATIO: x = 40 · 0.25
    placePortsFixedRatioOnSide n .south 40.0 20.0
    let pe0 := (← LayeredM.getPort pe).position
    let pw0 := (← LayeredM.getPort pw).position
    let pr := (← LayeredM.getPort ps).position
    -- inside self loops: west/east centred, north snapped
    placeInsideSelfLoopPorts n 40.0 20.0
    let pw2 := (← LayeredM.getPort pw).position
    -- a port label sticking out to the right
    let lbl ← addPortLabel pe "x" 10.0 4.0
    LayeredM.modifyLabel lbl fun l => { l with position := ⟨6.0, -3.0⟩ }
    updateNodeMargin n
    return (pe0, pw0, pn, ps, pr, pw2, n))
  checkVec "hand: adjust east port (offset 2)" pe ⟨42.0, 3.0⟩
  checkVec "hand: adjust west port" pw ⟨-6.0, 3.0⟩
  checkVec "hand: fixed ratio south port" pr ⟨10.0, 20.0⟩
  checkVec "hand: inside self loop west port centred" pw2 ⟨-6.0, 8.0⟩
  checkVec "hand: inside self loop east port" (a.port (portAt a n 0)).position ⟨40.0, 8.0⟩
  checkVec "hand: inside self loop north port snapped" (a.port pn).position ⟨7.0, -4.0⟩
  checkVec "hand: inside self loop south port snapped" (a.port ps).position ⟨10.0, 20.0⟩
  -- east port (40, 8) 6×4 → right 6, label at (46, 5) 10×4 → right 16; west port → left 6
  checkMargin "hand: updateNodeMargin" (a.node n).margin 4.0 16.0 4.0 6.0

def clockwiseTests : Suite := suite "layered.intermediate.labelAndNodeSize.clockwiseOrder" do
  checkEq "hand: findPortSideRange south" (findPortSideRange #[.north, .east, .south, .south, .west] .south) (2, 4)
  checkEq "hand: findPortSideRange missing side" (findPortSideRange #[.north, .west] .east) (1, 1)
  checkEq "hand: reverseRange" (reverseRange #[1, 2, 3, 4, 5] 1 4) #[1, 4, 3, 2, 5]
  checkEq "hand: reverseRange of one element" (reverseRange #[1, 2, 3] 1 2) #[1, 2, 3]
  let ((ports, sorted, fixedOrder, withDummy), _) ← LayeredM.run (do
    let (g, layers) ← mkGraph 2
    let n ← addNode g layers[0]! 20.0 20.0 (({} : PropertyMap).set CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide)
    let sides := #[PortSide.west, .south, .east, .north, .south, .west]
    let ports ← sides.mapM fun s => addPort n s 2.0 2.0
    ensureClockwisePortOrder n .fixedSide
    let sorted := (← LayeredM.getNode n).ports
    -- FIXED_ORDER: unchanged
    let m ← addNode g layers[0]! 20.0 20.0
    let mp ← sides.mapM fun s => addPort m s 2.0 2.0
    ensureClockwisePortOrder m .fixedOrder
    let fixedOrder := (← LayeredM.getNode m).ports == mp
    -- a connected dummy edge (no ORIGIN): unchanged
    let k ← addNode g layers[0]! 20.0 20.0
    let kp ← sides.mapM fun s => addPort k s 2.0 2.0
    let other ← addNode g layers[1]! 20.0 20.0
    let _ ← connect kp[0]! (← addPort other .west 2.0 2.0)
    ensureClockwisePortOrder k .fixedSide
    let withDummy := (← LayeredM.getNode k).ports == kp
    return (ports, sorted, fixedOrder, withDummy))
  -- sides sorted N E S S W W, then SOUTH and WEST ranges reversed
  checkEq "hand: clockwise order" sorted #[ports[3]!, ports[2]!, ports[4]!, ports[1]!, ports[5]!, ports[0]!]
  check "hand: FIXED_ORDER keeps the port order" fixedOrder
  check "hand: dummy edges keep the port order" withDummy

def sizingTests : Suite := suite "layered.intermediate.labelAndNodeSize.portDrivenSizing" do
  let ((s1, s2, s3, s4), _) ← LayeredM.run (do
    let (g, layers) ← mkGraph 1
    -- two EAST ports 10×10: 10 + 10 + 10 (spacing) + 2 · 10 (DISTRIBUTED) = 50
    let n ← addNode g layers[0]! 10.0 10.0
    let _ ← addPort n .east 10.0 10.0
    let _ ← addPort n .east 10.0 10.0
    let s1 ← enforcePortDrivenMinimumSize n ⟨10.0, 10.0⟩ 10.0 {} false true
    -- no shrinking: max(80, 50)
    LayeredM.modifyNode n fun x => { x with size := ⟨10.0, 80.0⟩ }
    let s2 ← enforcePortDrivenMinimumSize n ⟨10.0, 80.0⟩ 10.0 {} false false
    -- shrinking: the requirement replaces the height
    let s3 ← enforcePortDrivenMinimumSize n ⟨10.0, 80.0⟩ 10.0 {} false true
    -- inside port labels: WEST label 12×6 and EAST label 8×6 on 5×5 ports, padding 0, gaps 1:
    -- width 0 + 0 + 2 + 12 + 8 = 22; height max(2 + 0 + 0, 5 + 2 · (6 + 1 - 5), …) = 9
    let props := ({} : PropertyMap).set CoreOptions.PORT_LABELS_PLACEMENT (portLabels #[.inside])
    let m ← addNode g layers[0]! 4.0 4.0 props
    let _ ← addPortLabel (← addPort m .west 5.0 5.0) "w" 12.0 6.0
    let _ ← addPortLabel (← addPort m .east 5.0 5.0) "e" 8.0 6.0
    let s4 ← enforceInsidePortLabelMinimumSize m ⟨4.0, 4.0⟩ 10.0 {} true
    return (s1, s2, s3, s4))
  checkVec "hand: port driven minimum size" s1 ⟨10.0, 50.0⟩
  checkVec "hand: port driven size does not shrink" s2 ⟨10.0, 80.0⟩
  checkVec "hand: port driven size shrinks when allowed" s3 ⟨10.0, 50.0⟩
  checkVec "hand: inside port label minimum size" s4 ⟨22.0, 9.0⟩

/-- `processWith` with the elk-rs phase-2 workaround enabled (`ELK_NODE_DIM_SKIP_FULL_PROCESS`
semantics: the label and node size calculation uses `processNode` + port label placement). -/
def phase2Tests : Suite := suite "layered.intermediate.labelAndNodeSizeProcessor.phase2" do
  let flags : LabelAndNodeSizeFlags := { useFullProcess := false, enablePhase1PortPlacement := true }
  let ((n, ports, selfLoop), a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 1
    let props := ({} : PropertyMap)
      |>.set CoreOptions.NODE_SIZE_CONSTRAINTS (sizeConstraints #[.ports])
      |>.set CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
    let n ← addNode g layers[0]! 20.0 20.0 props
    let ports ← #[0, 1, 2].mapM fun _ => addPort n .east 10.0 10.0
    -- INSIDE_SELF_LOOPS_ACTIVATE nodes are skipped by the phase-1 placement
    let sl ← addNode g layers[0]! 20.0 20.0 (props.set CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE true)
    let slPort ← addPort sl .east 10.0 10.0 ⟨3.0, 3.0⟩
    LabelAndNodeSizeProcessor.processWith flags g ProgressMonitor.null
    return (n, ports, slPort))
  -- height = 3 · 10 + 2 · 10 + 2 · 10 = 70 (shrink allowed); DISTRIBUTED with exact room: 10, 30, 50
  checkFloat "hand: phase 2 port driven height" (a.node n).size.y 70.0
  for (p, y) in ports.zip #[10.0, 30.0, 50.0] do
    checkVec s!"hand: phase 2 east port {p}" (a.port p).position ⟨(a.node n).size.x, y⟩
  checkMargin "hand: phase 2 margin (ports stick out by 10)" (a.node n).margin 0.0 10.0 0.0 0.0
  checkVec "hand: inside self loop node skipped by phase 2 (port not moved)" (a.port selfLoop).position ⟨3.0, 3.0⟩

-- ===============================================================================================
-- InnermostNodeMarginCalculator

def innermostTests : Suite := suite "layered.intermediate.innermostNodeMarginCalculator" do
  -- oracle model: n1 (30×30, FIXED_SIDE, EAST port 4×4) → n2 (20×40, WEST port 4×4); the edge has two
  -- TAIL labels and one HEAD label, which are excluded from the margins
  let ((n1, n2, dummy, layerless), a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 2 (({} : PropertyMap).set CoreOptions.DIRECTION Direction.right)
    let fixedSide := ({} : PropertyMap).set CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
    let n1 ← addNode g layers[0]! 30.0 30.0 fixedSide
    let n2 ← addNode g layers[1]! 20.0 40.0 fixedSide
    let p1 ← addPort n1 .east 4.0 4.0 ⟨30.0, 13.0⟩
    let q1 ← addPort n2 .west 4.0 4.0 ⟨-4.0, 18.0⟩
    let e ← connect p1 q1
    let _ ← addEdgeLabel e "t1" 20.0 8.0 .tail
    let _ ← addEdgeLabel e "t2" 14.0 6.0 .tail
    let _ ← addEdgeLabel e "h1" 18.0 7.0 .head
    -- every layer node counts (no type filter), layerless nodes do not
    let dummy ← addNode g layers[0]! 0.0 0.0 {} { type := .longEdge }
    let _ ← addPort dummy .east 2.0 2.0 ⟨0.0, -1.0⟩
    let layerless ← LayeredM.createNode g { size := ⟨5.0, 5.0⟩ }
    LayeredM.modifyGraph g fun x => { x with layerlessNodes := #[layerless] }
    let _ ← addPort layerless .east 2.0 2.0 ⟨5.0, 0.0⟩
    runProc InnermostNodeMarginCalculator.processor g
    return (n1, n2, dummy, layerless))
  checkMargin "oracle: n1 margins without end labels" (a.node n1).margin 0.0 4.0 0.0 0.0
  checkMargin "oracle: n2 margins without end labels" (a.node n2).margin 0.0 0.0 0.0 4.0
  checkMargin "hand: long edge dummy margins (port (0, -1) 2×2)" (a.node dummy).margin 1.0 2.0 1.0 0.0
  checkMargin "hand: layerless node untouched" (a.node layerless).margin 0.0 0.0 0.0 0.0

-- ===============================================================================================
-- EndLabelPreprocessor

/-- The label cell stored for a port (`END_LABELS`). -/
def cellOf (a : LGraphArena) (n : LNodeId) (p : LPortId) : Option EndLabelPreprocessor.EndLabelCell :=
  ((a.node n).internal.endLabels.getD #[]).find? (·.1 == p) |>.map (·.2)

def cellAlignments (c : EndLabelPreprocessor.EndLabelCell) :
    Option (Elk.Alg.Common.NodeSpacing.CellSystem.HorizontalLabelAlignment ×
      Elk.Alg.Common.NodeSpacing.CellSystem.VerticalLabelAlignment) :=
  match c.kind with
  | .label d => some (d.horizontalAlignment, d.verticalAlignment)
  | _ => none

def cellLabels (c : EndLabelPreprocessor.EndLabelCell) : Array LLabelId :=
  match c.kind with
  | .label d => d.labels.map (·.1)
  | _ => #[]

def endLabelOracleTests : Suite := suite "layered.intermediate.endLabelPreprocessor.oracle" do
  -- the oracle model of `innermostTests` after `InnermostNodeMarginCalculator` (margins n1 right 4,
  -- n2 left 4); the EndLabelPreprocessor runs before the LabelSideSelector (sides UNKNOWN)
  let ((n1, n2, p1, q1, t1, t2, h1, e), a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 2 (({} : PropertyMap).set CoreOptions.DIRECTION Direction.right)
    let n1 ← addNode g layers[0]! 30.0 30.0 {} { margin := { right := 4.0 } }
    let n2 ← addNode g layers[1]! 20.0 40.0 {} { margin := { left := 4.0 } }
    let p1 ← addPort n1 .east 4.0 4.0 ⟨30.0, 13.0⟩
    let q1 ← addPort n2 .west 4.0 4.0 ⟨-4.0, 18.0⟩
    let e ← connect p1 q1
    let t1 ← addEdgeLabel e "t1" 20.0 8.0 .tail
    let t2 ← addEdgeLabel e "t2" 14.0 6.0 .tail
    let h1 ← addEdgeLabel e "h1" 18.0 7.0 .head
    runProc EndLabelPreprocessor.processor g
    return (n1, n2, p1, q1, t1, t2, h1, e))
  checkMargin "oracle: n1 margins with the tail label cell" (a.node n1).margin 0.0 26.0 2.0 0.0
  checkMargin "oracle: n2 margins with the head label cell" (a.node n2).margin 0.0 0.0 0.0 24.0
  match cellOf a n1 p1, cellOf a n2 q1 with
  | some c1, some c2 =>
    -- anchor (34, 15): x = 30 + 4 + 2, y = 15 + 1 (thickness) + 2; 20 × (8 + 6)
    checkEqR "hand: tail cell rectangle" c1.cellRectangle ⟨36.0, 18.0, 20.0, 14.0⟩
    check "hand: tail cell alignment LEFT/TOP" (cellAlignments c1 == some (.left, .top))
    checkEq "hand: tail cell labels in edge order" (cellLabels c1) #[t1, t2]
    -- anchor (-4, 20): x = -4 - 2 - 18, y = 20 + 1 + 2
    checkEqR "hand: head cell rectangle" c2.cellRectangle ⟨-24.0, 23.0, 18.0, 7.0⟩
    check "hand: head cell alignment RIGHT/TOP" (cellAlignments c2 == some (.right, .top))
  | _, _ => check "hand: END_LABELS set on both nodes" false
  checkEq "hand: one cell per node" ((a.node n1).internal.endLabels.map (·.size)) (some 1)
  checkFloat "hand: MAX_EDGE_THICKNESS of the source port" (a.port p1).internal.maxEdgeThickness 1.0
  checkEq "hand: END_LABEL_EDGE of the head label" (a.label h1).internal.endLabelEdge (some e)
  checkEq "hand: END_LABEL_EDGE of a tail label" (a.label t2).internal.endLabelEdge (some e)

def endLabelHandTests : Suite := suite "layered.intermediate.endLabelPreprocessor.cases" do
  -- two NORTH ports with a tail label 10×5 each; label-label spacing 1 → overlap gap 2
  let ((n, pa, pb, m, pAbove), a) ← LayeredM.run (do
    let props := ({} : PropertyMap) |>.set CoreOptions.DIRECTION Direction.right |>.set CoreOptions.SPACING_LABEL_LABEL 1.0
    let (g, layers) ← mkGraph 2 props
    let n ← addNode g layers[0]! 40.0 20.0
    let other ← addNode g layers[1]! 10.0 10.0
    let pa ← addPort n .north 4.0 4.0 ⟨5.0, -4.0⟩
    let pb ← addPort n .north 4.0 4.0 ⟨12.0, -4.0⟩
    let _ ← addEdgeLabel (← connect pa (← addPort other .west 1.0 1.0)) "a" 10.0 5.0 .tail
    let _ ← addEdgeLabel (← connect pb (← addPort other .west 1.0 1.0)) "b" 10.0 5.0 .tail
    -- an ABOVE label on an EAST port of another node
    let m ← addNode g layers[0]! 30.0 30.0
    let pAbove ← addPort m .east 4.0 4.0 ⟨30.0, 13.0⟩
    let above ← addEdgeLabel (← connect pAbove (← addPort other .west 1.0 1.0)) "up" 20.0 8.0 .tail
    LayeredM.modifyLabel above fun l => { l with internal := { l.internal with labelSide := .above } }
    runProc EndLabelPreprocessor.processor g
    return (n, pa, pb, m, pAbove))
  match cellOf a n pa, cellOf a n pb with
  | some ca, some cb =>
    -- anchors (7, -4) / (14, -4): x = 7 + 1 + 2 = 10 and 17; y = -0 - 2 - 5 = -7 before removal;
    -- UP removal from -2: the first stays at -2 - 5 - 0, the second moves to -2 - 5 - 7
    checkEqR "hand: first north cell" ca.cellRectangle ⟨10.0, -7.0, 10.0, 5.0⟩
    checkEqR "hand: second north cell moved up" cb.cellRectangle ⟨17.0, -14.0, 10.0, 5.0⟩
    check "hand: north cell alignment LEFT/BOTTOM" (cellAlignments ca == some (.left, .bottom))
  | _, _ => check "hand: north cells exist" false
  checkMargin "hand: margins include the moved cell" (a.node n).margin 14.0 0.0 0.0 0.0
  match cellOf a m pAbove with
  | some c =>
    -- ABOVE: x = 30 + 0 + 2, y = 15 - 1 - 2 - 8 = 4, LEFT/BOTTOM
    checkEqR "hand: ABOVE east cell" c.cellRectangle ⟨32.0, 4.0, 20.0, 8.0⟩
    check "hand: ABOVE east alignment LEFT/BOTTOM" (cellAlignments c == some (.left, .bottom))
  | none => check "hand: ABOVE cell exists" false
  -- vertical layout: labels side by side (width 20 + 14 + 1, height 8); WEST port, PORT_DUMMY labels
  let ((vn, vp, dl), b) ← LayeredM.run (do
    let props := ({} : PropertyMap) |>.set CoreOptions.DIRECTION Direction.down |>.set CoreOptions.SPACING_LABEL_LABEL 1.0
    let (g, layers) ← mkGraph 2 props
    let vn ← addNode g layers[0]! 30.0 30.0
    let other ← addNode g layers[1]! 10.0 10.0
    let vp ← addPort vn .west 4.0 4.0 ⟨-4.0, 13.0⟩
    let e ← connect (← addPort other .east 1.0 1.0) vp
    let _ ← addEdgeLabel e "h1" 20.0 8.0 .head
    -- a north/south port dummy whose port originates from `vp` contributes its edges' end labels
    let dummy ← addNode g layers[1]! 1.0 1.0 {} { type := .northSouthPort }
    let dp ← addPort dummy .east 1.0 1.0
    LayeredM.modifyPort dp fun p => { p with internal := { p.internal with origin := some (.lPort vp) } }
    LayeredM.modifyPort vp fun p => { p with internal := { p.internal with portDummy := some dummy } }
    let e2 ← connect (← addPort other .east 1.0 1.0) dp
    let dl ← addEdgeLabel e2 "h2" 14.0 6.0 .head
    runProc EndLabelPreprocessor.processor g
    return (vn, vp, dl))
  match cellOf b vn vp with
  | some c =>
    checkEq "hand: PORT_DUMMY end labels gathered" (cellLabels c).size 2
    check "hand: dummy label second" ((cellLabels c)[1]? == some dl)
    -- vertical mode: width 20 + 14 + 1 = 35, height 8; x = -0 - 2 - 35, y = 15 + 1 + 2
    checkEqR "hand: vertical layout west cell" c.cellRectangle ⟨-37.0, 18.0, 35.0, 8.0⟩
  | none => check "hand: vertical cell exists" false

/-- Rust `end_label_pre_and_postprocessor_strategies_are_stable_on_simple_graph` (+ no `END_LABELS`
without end labels). -/
def endLabelStableTests : Suite := suite "layered.intermediate.endLabelPreprocessor.stable" do
  let snapshot := fun (a : LGraphArena) (g : LGraphId) =>
    let gr := a.graph g
    let firstLayerNodes := (gr.layers[0]?.map fun l => (a.layer l).nodes.size).getD 0
    let normal := gr.layers.foldl (fun acc l => acc + ((a.layer l).nodes.filter fun n => (a.node n).type == .normal).size) 0
    (gr.layers.size, firstLayerNodes, gr.layerlessNodes.size, normal)
  for s in #[IntermediateProcessorStrategy.endLabelPreprocessor, .endLabelPostprocessor] do
    let ((g, before, node), a) ← LayeredM.run (do
      let (g, layers) ← mkGraph 1
      let node ← addNode g layers[0]! 0.0 0.0
      let before := snapshot (← get) g
      runProc (← IntermediateProcessorStrategy.create s) g
      return (g, before, node))
    checkEq s!"end_label_pre_and_postprocessor_strategies_are_stable_on_simple_graph: {s}" (snapshot a g) before
    check s!"hand: no END_LABELS after {s}" (a.node node).internal.endLabels.isNone
  -- a port with an edge but only center labels: no cell, margins untouched
  let (n, b) ← LayeredM.run (do
    let (g, layers) ← mkGraph 2
    let n ← addNode g layers[0]! 10.0 10.0 {} { margin := { top := 1.0 } }
    let m ← addNode g layers[1]! 10.0 10.0
    let e ← connect (← addPort n .east 1.0 1.0) (← addPort m .west 1.0 1.0)
    let _ ← addEdgeLabel e "c" 5.0 5.0 .center
    runProc EndLabelPreprocessor.processor g
    return n)
  check "hand: center labels only → no END_LABELS" (b.node n).internal.endLabels.isNone
  checkMargin "hand: center labels only → margins untouched" (b.node n).margin 1.0 0.0 0.0 0.0

-- ===============================================================================================
-- NodePlacementRepeater

/-- Rust `second_placement_fixes_sizes_repositions_ports_and_disables_flexibility`. -/
def repeaterTests : Suite := suite "layered.intermediate.nodePlacementRepeater" do
  for strategy in #[NodePlacementStrategy.simple, .interactive, .linearSegments, .brandesKoepf, .networkSimplex] do
    let name := s!"second_placement_fixes_sizes_repositions_ports_and_disables_flexibility ({strategy})"
    let result ← EIO.toBaseIO (LayeredM.run (do
      let props := ({} : PropertyMap)
        |>.set LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT NodeFlexibility.nodeSize
        |>.set LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT strategy
      let (g, layers) ← mkGraph 1
      LayeredM.modifyGraph g fun x => { x with props := props }
      let nodeProps := ({} : PropertyMap)
        |>.set LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
        |>.set LayeredOptions.NODE_SIZE_CONSTRAINTS (sizeConstraints #[.minimumSize])
        |>.set LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY NodeFlexibility.nodeSize
      let node ← addNode g layers[0]! 70.0 90.0 nodeProps { position := ⟨13.0, 999.0⟩, margin := { right := 999.0 } }
      -- the first placer enlarged this node; this is the old border
      let port ← addPort node .east 4.0 4.0 ⟨30.0, 0.0⟩
      runProc NodePlacementRepeater.processor g
      return (g, node, port)))
    match result with
    | .error err => check s!"{name}: runs ({err})" false
    | .ok ((g, node, port), a) =>
      checkEq s!"{name}: flexibility default reset" ((a.graph g).props.get LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT) (some NodeFlexibility.none)
      let nd := a.node node
      checkFloat s!"{name}: width" nd.size.x 70.0
      checkFloat s!"{name}: height" nd.size.y 90.0
      checkFloat s!"{name}: x" nd.position.x 13.0
      check s!"{name}: y finite and reset" (nd.position.y.isFinite && nd.position.y < 999.0)
      check s!"{name}: node flexibility removed" (nd.props.get LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY).isNone
      check s!"{name}: size constraints removed" ((nd.props.get LayeredOptions.NODE_SIZE_CONSTRAINTS).map (·.isEmpty) == some true)
      checkFloat s!"{name}: margin recomputed" nd.margin.right 4.0
      checkFloat s!"{name}: port moved" (a.port port).position.x 70.0

/-- Rust `repeater_resets_dummy_nodes_without_resizing_them` + the missing strategy error. -/
def repeaterDummyTests : Suite := suite "layered.intermediate.nodePlacementRepeater.dummies" do
  let (node, a) ← LayeredM.run (do
    let (g, layers) ← mkGraph 1
    let props := ({} : PropertyMap).set
      LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT NodePlacementStrategy.simple
    LayeredM.modifyGraph g fun x => { x with props := props }
    let node ← addNode g layers[0]! 0.0 5.0 {} { type := .longEdge, position := ⟨0.0, 999.0⟩ }
    runProc NodePlacementRepeater.processor g
    return node)
  checkFloat "repeater_resets_dummy_nodes_without_resizing_them: height" (a.node node).size.y 5.0
  checkFloat "repeater_resets_dummy_nodes_without_resizing_them: y" (a.node node).position.y 0.0
  checkThrows "hand: missing second strategy throws" (do
    let _ ← LayeredM.run (do
      let (g, _) ← mkGraph 1
      runProc NodePlacementRepeater.processor g)
    pure ())

/-- Rust `configurator_schedules_repeater_before_graph_height_only_when_requested` at configuration
level (the assembled processor list needs the crossing minimizer, which is not ported yet): the
repeater is requested after P4 only with a second placer, and sorts before
`LayerSizeAndGraphHeightCalculator` in that slot (enum ordinal order). -/
def configuratorTests : Suite := suite "layered.intermediate.nodePlacementRepeater.configurator" do
  for secondPlacer in #[none, some NodePlacementStrategy.simple] do
    let (config, _) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let node ← LayeredM.createNode g
      let props := (({} : PropertyMap).set LayeredOptions.NODE_PLACEMENT_STRATEGY NodePlacementStrategy.networkSimplex).setOpt
        LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT secondPlacer
      LayeredM.modifyGraph g fun x => { x with layerlessNodes := #[node], props := props }
      GraphConfigurator.getPhaseIndependentLayoutProcessorConfiguration g)
    let afterP4 := config.getListItem (ElkEnum.ordinal LayeredPhases.p4NodePlacement + 1)
    checkEq s!"configurator_schedules_repeater_before_graph_height_only_when_requested: {secondPlacer}"
      (afterP4.contains .nodePlacementRepeater) secondPlacer.isSome
  check "configurator_schedules_repeater_before_graph_height_only_when_requested: before graph height"
    (ElkEnum.ordinal IntermediateProcessorStrategy.nodePlacementRepeater <
      ElkEnum.ordinal IntermediateProcessorStrategy.layerSizeAndGraphHeightCalculator)

-- ===============================================================================================
-- Registration

def registrationTests : Suite := suite "layered.intermediate.nodeSize.registration" do
  let expected : Array (IntermediateProcessorStrategy × String) := #[
    (.labelAndNodeSizeProcessor, "LabelAndNodeSizeProcessor"),
    (.innermostNodeMarginCalculator, "InnermostNodeMarginCalculator"),
    (.endLabelPreprocessor, "EndLabelPreprocessor"), (.nodePlacementRepeater, "NodePlacementRepeater")]
  for (s, name) in expected do
    check s!"registered: {s}" (← IntermediateProcessorStrategy.isAvailable s)
    checkEq s!"processor name of {s}" (← IntermediateProcessorStrategy.create s).name name
  let flags := LabelAndNodeSizeFlags.global
  check "hand: default flags (no environment switches in tests)"
    (flags.useFullProcess && !flags.enablePhase1PortPlacement && !flags.disableClockwiseSideOrder)

def suites : Array Suite :=
  #[oracleSizeTests, portOffsetTests, variantTests, externalPortTests, placementHelperTests, fixedPlacementTests,
    clockwiseTests, sizingTests, phase2Tests, innermostTests, endLabelOracleTests, endLabelHandTests,
    endLabelStableTests, repeaterTests, repeaterDummyTests, configuratorTests, registrationTests]

end Tests.Layered.IntermediateNodeSize
