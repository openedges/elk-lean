import Tests.Framework
import Elk.Alg.Common
import Elk.Text
/-! End-to-end tests of `org.eclipse.elk.alg.common.nodespacing` (task N3b):
`NodeDimensionCalculation` and `NodeMicroLayout` on `ElkGraph`s, ported from elk-rs
`plugins/org.eclipse.elk.alg.common/tests/all`. Expected numbers prefixed "rust:" are copied from
the named Rust test; "hand:" checks are derived from the elk-rs formulas.

Ported:
* `nodespacing_test.rs`: all tests. The `node_margin_calculator_*` graphs run through
  `NodeDimensionCalculation.calculateNodeMargins` / `getNodeMarginCalculator` (the same graphs run
  through `NodeMarginCalculator` directly in `Calculators.lean`);
  `inside_node_label_padding_uses_grid_cell_maxima_and_spacing` and
  `inside_node_label_container_minimum_size_handles_tabular_and_center_only_modes` are only in
  `Calculators.lean` (they do not touch the N3b modules). The `next_to_port_rule_*` tests check the
  test-local Rust rule and, additionally, the library rule `shouldLabelBePlacedNextToPortElk`.
  `node_dimension_calculation_generic_dispatch_places_port_labels_for_elk_adapter` calls
  `calculateLabelAndNodeSizesForElk` (Lean has no adapter downcast).
* `node_micro_layout_test.rs` (adapted): the Rust test runs the force, layered, mrtree, radial,
  rectpacking and stress providers (none is ported yet), which all call `NodeMicroLayout` unless
  `omitNodeMicroLayout` is set; here `NodeMicroLayout.execute` runs directly and the
  non-omitted expectations are checked.
* `cellsystem_process_test.rs` (adapted): the Rust test runs the layered provider, whose
  `LabelAndNodeSizeProcessor` calls the generic `calculate_label_and_node_sizes`; here the generic
  `NodeDimensionCalculation.calculateLabelAndNodeSizes` runs on the `ElkGraph` adapters.
* `issue_475_test.rs`: the model `tickets/core/475_fixedLayoutWithLongLabels.elkt` is inlined.

Skipped (need the layered provider, Phase 4, and `elk-models` resources):
`inside_port_label_test.rs`, `next_to_port_label_placement_test.rs`,
`port_label_placement_variants_test.rs`. -/
namespace Tests.AlgCommon.NodeSpacing.All

open Tests Elk Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.Common.NodeSpacing

/-! ### Helpers -/

private def close (a b : Float) (eps : Float := 1e-9) : Bool := (a - b).abs < eps

/-- Runs a graph construction / layout script on an empty arena. -/
private def runElk {α : Type} (x : ElkM α) : IO α := do
  let (r, _) ← ElkM.run x {}
  return r

/-- A child node with the given geometry. -/
private def mkNode (parent : NodeId) (x y w h : Float) : ElkM NodeId := do
  let n ← ElkM.createNode (some parent)
  ElkM.modifyNode n fun nd => { nd with x, y, width := w, height := h }
  return n

/-- A port with the given geometry, side and `PORT_INDEX`. -/
private def mkPort (node : NodeId) (x y w h : Float) (side : Option PortSide := none) (index : Option Int := none) :
    ElkM PortId := do
  let p ← ElkM.createPort (some node)
  ElkM.modifyPort p fun pt => { pt with x, y, width := w, height := h }
  if let some s := side then ElkM.setProp (.port p) CoreOptions.PORT_SIDE s
  if let some i := index then ElkM.setProp (.port p) CoreOptions.PORT_INDEX i
  return p

/-- A label with the given geometry. -/
private def mkLabel (parent : ElementId) (x y w h : Float) (text : String := "") : ElkM LabelId := do
  let l ← ElkM.createLabel (some parent) text
  ElkM.modifyLabel l fun lb => { lb with x, y, width := w, height := h }
  return l

private def labelPos (l : LabelId) : ElkM KVector := do
  let lb ← ElkM.getLabel l
  return ⟨lb.x, lb.y⟩

private def nodeSize (n : NodeId) : ElkM KVector := do
  let nd ← ElkM.getNode n
  return ⟨nd.width, nd.height⟩

private def nodeMargin (n : NodeId) : ElkM ElkMargin := do
  return (← ElkM.getNode n).props.getD CoreOptions.MARGINS {}

/-- `NodeMicroLayout::for_graph(graph).execute()`. -/
private def microLayout (graph : NodeId) : ElkM Unit := do
  (← NodeMicroLayout.forGraph graph).execute

/-- elk-rs' `NodeMicroLayout::execute` (`sortPortLists`, the simplified ELK path
`calculateLabelAndNodeSizesForElk`, `calculateNodeMargins`). `NodeMicroLayout` follows ELK Java and
no longer takes this path; the port label stacking tests below still exercise it. -/
private def elkRsMicroLayout (graph : NodeId) : ElkM Unit := do
  let a ← ElkGraphAdapters.adapt graph
  NodeDimensionCalculation.sortPortLists a graph
  NodeDimensionCalculation.calculateLabelAndNodeSizesForElk a graph
  NodeDimensionCalculation.calculateNodeMargins a graph

/-- Absolute rectangle `(port + label position, label size)` of a port's first label. -/
private def firstLabelRect (p : PortId) : ElkM ElkRectangle := do
  let pt ← ElkM.getPort p
  let lb ← ElkM.getLabel pt.labels[0]!
  return { x := pt.x + lb.x, y := pt.y + lb.y, width := lb.width, height := lb.height }

/-- Whether two of the rectangles overlap (open interiors). -/
private def anyOverlap (rects : Array ElkRectangle) : Bool := Id.run do
  for i in [0:rects.size] do
    for j in [i + 1:rects.size] do
      let l := rects[i]!
      let r := rects[j]!
      if l.x < r.x + r.width && l.x + l.width > r.x && l.y < r.y + r.height && l.y + l.height > r.y then
        return true
  return false

private def checkRects (name : String) (rects : Array ElkRectangle) (cond : ElkRectangle → Bool) : TestM Unit :=
  report name (rects.all cond) s!"rects {repr rects}"

/-! ### `nodespacing_test.rs`: node margins through `NodeDimensionCalculation` -/

/-- elk-rs `create_single_node_graph`: root ⊃ node at (10, 20), 40×30. -/
private def singleNode : ElkM (NodeId × NodeId) := do
  let root ← ElkM.createNode none
  let n ← mkNode root 10.0 20.0 40.0 30.0
  return (root, n)

/-- elk-rs `create_port_tail_label_setup`. -/
private def portTailLabelSetup : ElkM (NodeId × NodeId) := do
  let root ← ElkM.createNode none
  ElkM.setNodeProp root CoreOptions.SPACING_LABEL_NODE 2.0
  let source ← mkNode root 0.0 0.0 20.0 20.0
  ElkM.setNodeProp source CoreOptions.PORT_LABELS_PLACEMENT (EnumSet.of #[PortLabelPlacement.outside])
  let port ← mkPort source 20.0 8.0 2.0 4.0 (some .east)
  let _ ← mkLabel (.port port) 0.0 0.0 10.0 4.0
  let target ← mkNode root 80.0 0.0 20.0 20.0
  let edge ← ElkM.createSimpleEdge (.port port) (.node target)
  let el ← mkLabel (.edge edge) 0.0 0.0 6.0 3.0
  ElkM.setProp (.label el) CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.tail
  return (root, source)

/-- Runs `calculateNodeMargins` (or a configured `getNodeMarginCalculator`) and returns the margin. -/
private def marginsOf (setup : ElkM (NodeId × NodeId)) (configure : Option (NodeMarginCalculator → NodeMarginCalculator))
    (extra : NodeId → ElkM Unit := fun _ => pure ()) : IO ElkMargin := runElk do
  let (root, n) ← setup
  extra n
  let a ← ElkGraphAdapters.adapt root
  match configure with
  | none => NodeDimensionCalculation.calculateNodeMargins a root
  | some f => (f (NodeDimensionCalculation.getNodeMarginCalculator a)).process a root
  nodeMargin n

def nodeMarginTests : Suite := suite "alg.common.nodespacing.NodeDimensionCalculation.calculateNodeMargins" do
  let nodeLabel (n : NodeId) : ElkM Unit := do let _ ← mkLabel (.node n) (-6.0) 5.0 4.0 8.0
  checkFloat "rust: node_margin_calculator_includes_node_labels"
    (← marginsOf singleNode none nodeLabel).left 6.0
  checkFloat "rust: node_margin_calculator_excludes_node_labels_when_configured"
    (← marginsOf singleNode (some (·.excludeLabels)) nodeLabel).left 0.0
  let port (n : NodeId) : ElkM Unit := do let _ ← mkPort n 38.0 8.0 6.0 10.0
  checkFloat "rust: node_margin_calculator_includes_ports" (← marginsOf singleNode none port).right 4.0
  checkFloat "rust: node_margin_calculator_excludes_ports_when_configured"
    (← marginsOf singleNode (some (·.excludePorts)) port).right 0.0
  let portLabel (n : NodeId) : ElkM Unit := do
    let p ← mkPort n 5.0 10.0 4.0 4.0
    let _ ← mkLabel (.port p) 36.0 0.0 10.0 4.0
  checkFloat "rust: node_margin_calculator_includes_port_labels" (← marginsOf singleNode none portLabel).right 11.0
  checkFloat "rust: node_margin_calculator_excludes_port_labels_when_configured"
    (← marginsOf singleNode (some (·.excludePortLabels)) portLabel).right 0.0
  checkFloat "rust: node_margin_calculator_includes_tail_label_for_east_port_and_outside_port_labels"
    (← marginsOf portTailLabelSetup none).right 22.0
  checkFloat "rust: node_margin_calculator_ignores_edge_end_labels_when_disabled"
    (← marginsOf portTailLabelSetup (some (·.excludeEdgeHeadTailLabels))).right 10.0
  let headLabelLeft ← runElk do
    let root ← ElkM.createNode none
    ElkM.setNodeProp root CoreOptions.SPACING_LABEL_NODE 2.0
    let source ← mkNode root 0.0 0.0 20.0 20.0
    let target ← mkNode root 50.0 0.0 20.0 20.0
    let targetPort ← mkPort target (-2.0) 8.0 2.0 4.0 (some .west)
    let edge ← ElkM.createSimpleEdge (.node source) (.port targetPort)
    let el ← mkLabel (.edge edge) 0.0 0.0 6.0 3.0
    ElkM.setProp (.label el) CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.head
    NodeDimensionCalculation.calculateNodeMargins (← ElkGraphAdapters.adapt root) root
    return (← nodeMargin target).left
  checkFloat "rust: node_margin_calculator_places_head_label_left_of_west_port" headLabelLeft 12.0

/-! ### `nodespacing_test.rs`: `NodeDimensionCalculation` / `NodeMicroLayout` -/

/-- elk-rs `inside_west_port_label_y_with_node_compound(node_is_compound)` (with `generic`, the
generic `_with_process_node` pass runs instead of the micro layout). Returns the label position. -/
private def insideWestPortLabel (nodeIsCompound : Bool) (generic : Bool := false) : IO KVector := runElk do
  let root ← ElkM.createNode none
  let node ← mkNode root 0.0 0.0 40.0 20.0
  ElkM.setNodeProp node CoreOptions.PORT_LABELS_PLACEMENT (EnumSet.of #[PortLabelPlacement.inside])
  ElkM.setNodeProp node CoreOptions.PADDING (ElkPadding.ofAny 0.0)
  if nodeIsCompound then
    let _ ← mkNode node 2.0 2.0 10.0 5.0
  let port ← mkPort node 10.0 8.0 8.0 4.0 (some .west)
  let label ← mkLabel (.port port) 0.0 0.0 6.0 2.0
  let target ← mkNode root 20.0 0.0 12.0 12.0
  let _ ← ElkM.createSimpleEdge (.port port) (.node target)
  if generic then
    NodeDimensionCalculation.calculateLabelAndNodeSizesWith (← ElkGraphAdapters.adapt root) root false
  else
    microLayout root
  labelPos label

/-- elk-rs `node_dimension_calculation_sorts_ports_by_side_and_index` /
`node_micro_layout_executes_port_sort_and_margin_calculation` graph: a FIXED_ORDER node with ports
of the given sides and indices. -/
private def sortedPortsGraph (ports : Array (PortSide × Int)) :
    ElkM (NodeId × NodeId × Array PortId) := do
  let root ← ElkM.createNode none
  let node ← mkNode root 0.0 0.0 20.0 20.0
  ElkM.setNodeProp node CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedOrder
  let mut ids : Array PortId := #[]
  for (side, index) in ports do
    ids := ids.push (← mkPort node 0.0 0.0 0.0 0.0 (some side) (some index))
  return (root, node, ids)

def dimensionTests : Suite := suite "alg.common.nodespacing.NodeDimensionCalculation" do
  checkFloat "rust: node_dimension_calculation_places_inside_non_compound_port_labels_next_to_port_by_default"
    (← insideWestPortLabel false).y 1.0
  checkFloat "rust: node_dimension_calculation_places_inside_compound_port_labels_away_from_port_without_next_to_port_flag"
    (← insideWestPortLabel true).y 5.0
  -- Same graph through the generic pass: centered (non-compound), x = 8 + 0 (no border offset) + 0 + 1
  let generic ← insideWestPortLabel false (generic := true)
  checkFloat "hand: generic pass: inside WEST label right of the port (8 + 0 + 1)" generic.x 9.0
  checkFloat "hand: generic pass: centered on the port ((4 - 2) / 2)" generic.y 1.0
  -- The generic pass reads COMPOUND_NODE_PROPERTY, not the children: still centered
  checkFloat "hand: generic pass ignores the children of a node without compoundNode"
    (← insideWestPortLabel true (generic := true)).y 1.0
  -- Port sorting
  let (order, expected) ← runElk do
    let (root, node, ps) ← sortedPortsGraph #[(.west, 2), (.east, 0), (.west, 1)]
    NodeDimensionCalculation.sortPortLists (← ElkGraphAdapters.adapt root) root
    return ((← ElkM.getNode node).ports, #[ps[1]!, ps[2]!, ps[0]!])
  check "rust: node_dimension_calculation_sorts_ports_by_side_and_index" (order == expected)
  -- Generic dispatch for an ELK adapter = the ELK path
  let x ← runElk do
    let root ← ElkM.createNode none
    let node ← mkNode root 0.0 0.0 0.0 0.0
    ElkM.setNodeProp node CoreOptions.PORT_LABELS_PLACEMENT (EnumSet.of #[PortLabelPlacement.outside])
    let port ← mkPort node 0.0 0.0 8.0 4.0 (some .north)
    let label ← mkLabel (.port port) 0.0 0.0 6.0 2.0
    NodeDimensionCalculation.calculateLabelAndNodeSizesForElk (← ElkGraphAdapters.adapt root) root
    return (← labelPos label).x
  checkFloat "rust: node_dimension_calculation_generic_dispatch_places_port_labels_for_elk_adapter" x 9.0

def microLayoutTests : Suite := suite "alg.common.nodespacing.NodeMicroLayout" do
  let (marginLeft, order, expected) ← runElk do
    let (root, node, ps) ← sortedPortsGraph #[(.west, 2), (.west, 1)]
    let _ ← mkLabel (.node node) (-5.0) 0.0 4.0 4.0
    microLayout root
    return ((← nodeMargin node).left, (← ElkM.getNode node).ports, #[ps[1]!, ps[0]!])
  check "rust: node_micro_layout_executes_port_sort_and_margin_calculation (margin.left > 0)" (marginLeft > 0.0)
  check "rust: node_micro_layout_executes_port_sort_and_margin_calculation (ports sorted)" (order == expected)
  let size ← runElk do
    let root ← ElkM.createNode none
    let node ← mkNode root 0.0 0.0 100.0 100.0
    let _ ← mkLabel (.node node) 0.0 0.0 30.0 10.0
    microLayout root
    nodeSize node
  check "rust: node_micro_layout_does_not_resize_node_when_label_size_calculation_is_noop"
    (close size.x 100.0 && close size.y 100.0)
  let pos ← runElk do
    let root ← ElkM.createNode none
    let node ← mkNode root 0.0 0.0 80.0 60.0
    let label ← mkLabel (.node node) 7.0 9.0 15.0 8.0
    microLayout root
    labelPos label
  check "rust: node_micro_layout_does_not_move_existing_node_label_positions" (close pos.x 7.0 && close pos.y 9.0)
  -- Inside and outside node labels with NODE_LABELS
  let (size, inside, outside) ← runElk do
    let root ← ElkM.createNode none
    let node ← mkNode root 0.0 0.0 0.0 0.0
    ElkM.setNodeProp node CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.nodeLabels])
    ElkM.setNodeProp root CoreOptions.SPACING_LABEL_LABEL 1.0
    ElkM.setNodeProp root CoreOptions.SPACING_LABEL_NODE 3.0
    ElkM.setNodeProp root CoreOptions.NODE_LABELS_PADDING (ElkPadding.ofAny 2.0)
    let insideLabel ← mkLabel (.node node) 0.0 0.0 10.0 4.0
    ElkM.setProp (.label insideLabel) CoreOptions.NODE_LABELS_PLACEMENT NodeLabelPlacement.insideTopLeft
    let outsideLabel ← mkLabel (.node node) 0.0 0.0 30.0 5.0
    ElkM.setProp (.label outsideLabel) CoreOptions.NODE_LABELS_PLACEMENT NodeLabelPlacement.outsideTopCenter
    microLayout root
    return (← nodeSize node, ← labelPos insideLabel, ← labelPos outsideLabel)
  check "rust: node_micro_layout_places_inside_and_outside_node_labels_with_size_constraints (size 30×14)"
    (close size.x 30.0 && close size.y 14.0)
  check "rust: node_micro_layout_places_inside_and_outside_node_labels_with_size_constraints (inside (2, 2))"
    (close inside.x 2.0 && close inside.y 2.0)
  check "rust: node_micro_layout_places_inside_and_outside_node_labels_with_size_constraints (outside (0, -8))"
    (close outside.x 0.0 && close outside.y (-8.0))
  -- Outside label overhang
  let (size, outside) ← runElk do
    let root ← ElkM.createNode none
    let node ← mkNode root 0.0 0.0 10.0 4.0
    ElkM.setNodeProp node CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.nodeLabels])
    ElkM.setNodeProp node CoreOptions.NODE_SIZE_OPTIONS
      (EnumSet.of #[SizeOptions.outsideNodeLabelsOverhang, .asymmetrical])
    ElkM.setNodeProp root CoreOptions.SPACING_LABEL_LABEL 0.0
    ElkM.setNodeProp root CoreOptions.SPACING_LABEL_NODE 0.0
    ElkM.setNodeProp root CoreOptions.NODE_LABELS_PADDING (ElkPadding.ofAny 0.0)
    let insideLabel ← mkLabel (.node node) 0.0 0.0 10.0 4.0
    ElkM.setProp (.label insideLabel) CoreOptions.NODE_LABELS_PLACEMENT NodeLabelPlacement.insideCenter
    let outsideLabel ← mkLabel (.node node) 0.0 0.0 30.0 3.0
    ElkM.setProp (.label outsideLabel) CoreOptions.NODE_LABELS_PLACEMENT NodeLabelPlacement.outsideTopCenter
    microLayout root
    return (← nodeSize node, ← labelPos outsideLabel)
  check "rust: node_micro_layout_honors_outside_node_label_overhang (size 10×4)" (close size.x 10.0 && close size.y 4.0)
  check "rust: node_micro_layout_honors_outside_node_label_overhang (outside (-10, -3))"
    (close outside.x (-10.0) && close outside.y (-3.0))

/-! ### `nodespacing_test.rs`: next-to-port rules -/

/-- The test-local elk-rs `should_label_be_placed_next_to_port(port, parent, inside_label_placement)`:
`true` without edges; otherwise by the first target / source of the port's edges (inside = strict
descendant of the parent). -/
private def testRule (g : ElkGraph) (port : PortId) (parent : NodeId) (insideLabelPlacement : Bool) : Bool := Id.run do
  let pt := g.port port
  if pt.incomingEdges.isEmpty && pt.outgoingEdges.isEmpty then return true
  let mut edgesToInsides := false
  let mut edgesToSomewhereElse := false
  for e in pt.outgoingEdges do
    if let some target := (g.edge e).targets[0]? then
      if let some targetNode := ElkGraphUtil.connectableShapeToNode g target then
        let insideEdge := ElkGraphUtil.isDescendant g targetNode parent
        edgesToInsides := edgesToInsides || insideEdge
        edgesToSomewhereElse := edgesToSomewhereElse || !insideEdge
  for e in pt.incomingEdges do
    if let some source := (g.edge e).sources[0]? then
      if let some sourceNode := ElkGraphUtil.connectableShapeToNode g source then
        let insideEdge := ElkGraphUtil.isDescendant g sourceNode parent
        edgesToInsides := edgesToInsides || insideEdge
        edgesToSomewhereElse := edgesToSomewhereElse || !insideEdge
  return (insideLabelPlacement && !edgesToInsides) || (!insideLabelPlacement && !edgesToSomewhereElse)

/-- elk-rs `create_next_to_port_rule_graph`: root ⊃ parent ⊃ child, root ⊃ outside, a port on the
parent; `edge` adds an edge (`true`: port → child, `false`: outside → port). -/
private def nextToPortRuleGraph (edge : Option Bool) : IO (ElkGraph × PortId × NodeId) := do
  let ((port, parent), g) ← ElkM.run (do
    let root ← ElkM.createNode none
    let parent ← ElkM.createNode (some root)
    let child ← ElkM.createNode (some parent)
    let outside ← ElkM.createNode (some root)
    let port ← ElkM.createPort (some parent)
    match edge with
    | some true => let _ ← ElkM.createSimpleEdge (.port port) (.node child)
    | some false => let _ ← ElkM.createSimpleEdge (.node outside) (.port port)
    | none => pure ()
    return (port, parent)) {}
  return (g, port, parent)

open NodeDimensionCalculation in
def nextToPortRuleTests : Suite := suite "alg.common.nodespacing.NodeDimensionCalculation next-to-port rules" do
  let (g, port, parent) ← nextToPortRuleGraph none
  check "rust: next_to_port_rule_without_incident_edges (inside)" (testRule g port parent true)
  check "rust: next_to_port_rule_without_incident_edges (outside)" (testRule g port parent false)
  check "hand: library rule (NEXT_TO_PORT_IF_POSSIBLE): no edges → next to port (inside, compound parent)"
    (shouldLabelBePlacedNextToPortElk g port parent true true)
  check "hand: library rule: no edges → next to port (outside)" (shouldLabelBePlacedNextToPortElk g port parent false true)
  check "hand: library rule: outside without NEXT_TO_PORT_IF_POSSIBLE → not next to port"
    (!shouldLabelBePlacedNextToPortElk g port parent false false)
  let (g, port, parent) ← nextToPortRuleGraph (some true)
  check "rust: next_to_port_rule_inside_placement_rejects_inside_edges" (!testRule g port parent true)
  check "hand: library rule rejects inside edges for a compound parent"
    (!shouldLabelBePlacedNextToPortElk g port parent true true)
  let (g, port, parent) ← nextToPortRuleGraph (some false)
  check "rust: next_to_port_rule_inside_placement_accepts_only_external_edges" (testRule g port parent true)
  check "rust: next_to_port_rule_outside_placement_rejects_external_edges" (!testRule g port parent false)
  check "hand: library rule accepts external edges (inside)" (shouldLabelBePlacedNextToPortElk g port parent true true)
  check "hand: library rule rejects external edges (outside)" (!shouldLabelBePlacedNextToPortElk g port parent false true)
  -- Pure helpers
  checkEqR "hand: label placement relation: two outside ports, first above/left"
    (labelPlacementRelation 0 2 false false false false false false false) .aboveOrLeft
  checkEqR "hand: label placement relation: inside with edges, not next to port → below/right"
    (labelPlacementRelation 1 3 true true false false false false false) .belowOrRight
  checkEqR "hand: label placement relation: next to port → centered"
    (labelPlacementRelation 0 2 false false true false false false true) .centered

/-! ### `nodespacing_test.rs`: outside / constrained port label placement

These elk-rs tests check the label stacking of elk-rs' simplified ELK path, so they run
`elkRsMicroLayout` (ELK Java has no such stacking; `NodeMicroLayout` now runs the cell system). -/

/-- elk-rs `outside_north_label_x_positions(placements, port_count)`. -/
private def outsideNorthLabelXPositions (placements : Array PortLabelPlacement) (portCount : Nat) : IO (Array Float) :=
  runElk do
    let root ← ElkM.createNode none
    let node ← ElkM.createNode (some root)
    ElkM.setNodeProp node CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedOrder
    ElkM.setNodeProp node CoreOptions.PORT_LABELS_PLACEMENT (EnumSet.of placements)
    let mut ports : Array PortId := #[]
    for index in [0:portCount] do
      let port ← mkPort node (index.toFloat * 12.0) 0.0 8.0 4.0 (some .north) (some index)
      let _ ← mkLabel (.port port) 0.0 0.0 6.0 2.0
      ports := ports.push port
    elkRsMicroLayout root
    ports.mapM fun p => do return (← ElkM.getLabel (← ElkM.getPort p).labels[0]!).x

/-- elk-rs `constrained_outside_north_label_rectangles()`: sorted by x. -/
private def constrainedOutsideNorthLabelRectangles : IO (Array ElkRectangle) := runElk do
  let root ← ElkM.createNode none
  let node ← ElkM.createNode (some root)
  ElkM.setNodeProp node CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedOrder
  ElkM.setNodeProp node CoreOptions.PORT_LABELS_PLACEMENT
    (EnumSet.of #[PortLabelPlacement.outside, .alwaysSameSide])
  ElkM.setNodeProp node CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.portLabels])
  let mut ports : Array PortId := #[]
  for index in [0:3] do
    let port ← mkPort node (index.toFloat * 3.0) 0.0 8.0 4.0 (some .north) (some index)
    let _ ← mkLabel (.port port) 0.0 0.0 24.0 6.0
    ports := ports.push port
  elkRsMicroLayout root
  let rects ← ports.mapM firstLabelRect
  return stableSort rects fun l r => Float.comparePartial l.x r.x

/-- elk-rs `constrained_inside_custom_label_rectangles_with_options(port_side, node_width,
port_x_positions, label_width, node_padding, label_node_spacing, node_labels_padding)`. -/
private def constrainedInsideRects (side : PortSide) (nodeWidth : Float) (portXs : Array Float) (labelWidth : Float)
    (padding : Option ElkPadding := none) (labelNodeSpacing : Option Float := none)
    (nodeLabelsPadding : Option ElkPadding := none) : IO (Array ElkRectangle) := runElk do
  let root ← ElkM.createNode none
  let node ← mkNode root 0.0 0.0 nodeWidth 40.0
  ElkM.setNodeProp node CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedOrder
  ElkM.setNodeProp node CoreOptions.PORT_LABELS_PLACEMENT
    (EnumSet.of #[PortLabelPlacement.inside, .alwaysSameSide])
  ElkM.setNodeProp node CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.noneOf : EnumSet SizeConstraint)
  if let some p := padding then ElkM.setNodeProp node CoreOptions.PADDING p
  if let some s := labelNodeSpacing then ElkM.setNodeProp node CoreOptions.SPACING_LABEL_NODE s
  if let some p := nodeLabelsPadding then ElkM.setNodeProp node CoreOptions.NODE_LABELS_PADDING p
  let y := if side == .north then 0.0 else 36.0
  let mut ports : Array PortId := #[]
  for i in [0:portXs.size] do
    let port ← mkPort node portXs[i]! y 8.0 4.0 (some side) (some i)
    let _ ← mkLabel (.port port) 0.0 0.0 labelWidth 6.0
    ports := ports.push port
  elkRsMicroLayout root
  ports.mapM firstLabelRect

def portLabelPlacementTests : Suite := suite "alg.common.nodespacing.NodeMicroLayout port label placement (elk-rs path)" do
  let xs ← outsideNorthLabelXPositions #[.outside] 2
  check "rust: outside_two_ports_places_first_label_on_other_side (-7, 9)"
    (xs.size == 2 && close xs[0]! (-7.0) && close xs[1]! 9.0)
  let xs ← outsideNorthLabelXPositions #[.outside, .alwaysSameSide] 2
  check "rust: outside_two_ports_with_always_same_side_disables_first_special_case (9, 9)"
    (xs.size == 2 && close xs[0]! 9.0 && close xs[1]! 9.0)
  let xs ← outsideNorthLabelXPositions #[.outside, .spaceEfficient] 3
  check "rust: outside_three_ports_with_space_efficient_places_first_label_on_other_side (-7, 9, 9)"
    (xs.size == 3 && close xs[0]! (-7.0) && close xs[1]! 9.0 && close xs[2]! 9.0)
  -- Constrained outside: no overlaps, at least one stacked row
  let rects ← constrainedOutsideNorthLabelRectangles
  checkEq "rust: constrained_outside_north_port_labels_stack_without_overlap (3 labels)" rects.size 3
  report "rust: constrained_outside_north_port_labels_stack_without_overlap (no overlaps)" (!anyOverlap rects)
    s!"rects {repr rects}"
  report "rust: constrained_outside_north_port_labels_stack_without_overlap (stacked row)"
    (rects.any fun r => (r.y - rects[0]!.y).abs > 1e-9) s!"rects {repr rects}"
  -- Constrained inside NORTH: inside [0, 40], below the ports (port bottom + gap), no overlaps
  let rects ← constrainedInsideRects .north 40.0 #[0.0, 2.0, 4.0] 34.0
  checkEq "rust: constrained_inside_north_port_labels_are_clamped_and_stacked (3 labels)" rects.size 3
  checkRects "rust: constrained_inside_north_port_labels_are_clamped_and_stacked (bounds)" rects fun r =>
    r.x >= -1e-9 && r.x + r.width <= 40.0 + 1e-9 && r.y >= 5.0 - 1e-9 && r.height > 0.0
  report "rust: constrained_inside_north_port_labels_are_clamped_and_stacked (no overlaps)" (!anyOverlap rects)
    s!"rects {repr rects}"
  let rects ← constrainedInsideRects .south 40.0 #[0.0, 2.0, 4.0] 34.0
  checkEq "rust: constrained_inside_south_port_labels_are_clamped_and_stacked (3 labels)" rects.size 3
  checkRects "rust: constrained_inside_south_port_labels_are_clamped_and_stacked (bounds)" rects fun r =>
    r.x >= -1e-9 && r.x + r.width <= 40.0 + 1e-9 && r.y + r.height <= 35.0 + 1e-9
  report "rust: constrained_inside_south_port_labels_are_clamped_and_stacked (no overlaps)" (!anyOverlap rects)
    s!"rects {repr rects}"
  -- Centered, then clamped to the bounds widened by the port extent
  for side in #[PortSide.north, .south] do
    let rects ← constrainedInsideRects side 40.0 #[0.0, 35.0] 34.0
    check s!"rust: constrained_inside_{side}_labels_center_then_clamp_to_port_extent (0, 9)"
      (rects.size == 2 && close rects[0]!.x 0.0 && close rects[1]!.x 9.0)
    let rects ← constrainedInsideRects side 60.0 #[10.0, 45.0] 30.0
      (padding := some (ElkPadding.ofValues 0.0 11.0 0.0 7.0)) (labelNodeSpacing := some 9.0)
    check s!"rust: constrained_inside_{side}_labels_respect_explicit_padding_and_spacing_bounds (9, 23)"
      (rects.size == 2 && close rects[0]!.x 9.0 && close rects[1]!.x 23.0)
    let rects ← constrainedInsideRects side 60.0 #[10.0, 45.0] 30.0
      (nodeLabelsPadding := some (ElkPadding.ofValues 0.0 13.0 0.0 8.0))
    check s!"rust: constrained_inside_{side}_labels_respect_explicit_node_labels_padding_bounds (10, 23)"
      (rects.size == 2 && close rects[0]!.x 10.0 && close rects[1]!.x 23.0)

/-! ### `node_micro_layout_test.rs` (adapted) -/

/-- elk-rs `build_graph()`: node 100×100 with `MINIMUM_SIZE` 101×102 and labels A (inside top
center), B (inside bottom right), C (outside bottom center), D (outside V_CENTER H_LEFT), 10×10. -/
private def microLayoutGraph : ElkM (NodeId × NodeId × Array LabelId) := do
  let root ← ElkM.createNode none
  let node ← mkNode root 0.0 0.0 100.0 100.0
  ElkM.setNodeProp node CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.minimumSize])
  ElkM.setNodeProp node CoreOptions.NODE_SIZE_MINIMUM (⟨101.0, 102.0⟩ : KVector)
  let mut labels : Array LabelId := #[]
  for (text, placement) in #[("A", NodeLabelPlacement.insideTopCenter), ("B", NodeLabelPlacement.insideBottomRight),
      ("C", NodeLabelPlacement.outsideBottomCenter), ("D", EnumSet.of #[.outside, .vCenter, .hLeft])] do
    let l ← mkLabel (.node node) 0.0 0.0 10.0 10.0 text
    ElkM.setProp (.label l) CoreOptions.NODE_LABELS_PLACEMENT placement
    labels := labels.push l
  return (root, node, labels)

def nodeMicroLayoutTests : Suite := suite "alg.common.NodeMicroLayout (node_micro_layout_test)" do
  let (size, pos) ← runElk do
    let (root, node, labels) ← microLayoutGraph
    microLayout root
    return (← nodeSize node, ← labels.mapM labelPos)
  check "rust: test_minimum_size (101×102)" (close size.x 101.0 0.01 && close size.y 102.0 0.01)
  let (a, b, c, d) := (pos[0]!, pos[1]!, pos[2]!, pos[3]!)
  report "rust: test_node_label_positions: A y > 0" (a.y > 0.0) s!"A = {repr a}"
  report "rust: test_node_label_positions: B in the bottom right quadrant"
    (b.x > 60.0 && b.x < size.x && b.y > 60.0 && b.y < size.y) s!"B = {repr b}"
  report "rust: test_node_label_positions: C centered below the node"
    (c.x > 40.0 && c.x < 60.0 && c.y > size.y) s!"C = {repr c}"
  report "rust: test_node_label_positions: D left of the node, centered"
    (d.x < 0.0 && d.y > 40.0 && d.y < 60.0) s!"D = {repr d}"

/-! ### `cellsystem_process_test.rs` (adapted: generic path instead of the layered provider) -/

def cellSystemProcessTests : Suite := suite "alg.common.nodespacing.NodeDimensionCalculation generic process" do
  let (p0, p1) ← runElk do
    let root ← ElkM.createNode none
    let node ← mkNode root 0.0 0.0 200.0 75.0
    ElkM.setNodeProp node CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.nodeLabels, .minimumSize])
    let l0 ← mkLabel (.node node) 0.0 0.0 100.0 15.0 "First Label"
    ElkM.setProp (.label l0) CoreOptions.NODE_LABELS_PLACEMENT NodeLabelPlacement.insideTopCenter
    let l1 ← mkLabel (.node node) 0.0 0.0 117.0 15.0 "Second Label"
    ElkM.setProp (.label l1) CoreOptions.NODE_LABELS_PLACEMENT NodeLabelPlacement.insideTopCenter
    NodeDimensionCalculation.calculateLabelAndNodeSizes (← ElkGraphAdapters.adapt root) root
    return (← labelPos l0, ← labelPos l1)
  report "rust: cellsystem_multi_label_same_location_not_overwritten (first label placed)"
    (p0.x > 0.5 || p0.y > 0.5) s!"first = {repr p0}"
  report "rust: cellsystem_multi_label_same_location_not_overwritten (second label placed)"
    (p1.x > 0.5 || p1.y > 0.5) s!"second = {repr p1}"
  report "rust: cellsystem_multi_label_same_location_not_overwritten (second below first)"
    (p1.y > p0.y + 10.0) s!"first = {repr p0}, second = {repr p1}"
  let h ← runElk do
    let root ← ElkM.createNode none
    let node ← mkNode root 0.0 0.0 100.0 50.0
    ElkM.setNodeProp node CoreOptions.NODE_SIZE_CONSTRAINTS
      (EnumSet.of #[SizeConstraint.ports, .nodeLabels, .portLabels])
    ElkM.setNodeProp node CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
    ElkM.setNodeProp node CoreOptions.PORT_LABELS_PLACEMENT (EnumSet.noneOf : EnumSet PortLabelPlacement)
    let nodeLabel ← mkLabel (.node node) 0.0 0.0 50.0 17.0 "MyNode"
    ElkM.setProp (.label nodeLabel) CoreOptions.NODE_LABELS_PLACEMENT NodeLabelPlacement.insideTopCenter
    let port ← mkPort node 0.0 0.0 20.0 20.0 (some .north)
    ElkM.setProp (.port port) CoreOptions.PORT_BORDER_OFFSET (-8.0)
    let _ ← mkLabel (.port port) (-40.0) 21.0 100.0 17.0 "NorthFixedLabel"
    let _ ← mkNode root 0.0 0.0 30.0 20.0
    NodeDimensionCalculation.calculateLabelAndNodeSizes (← ElkGraphAdapters.adapt root) root
    return (← nodeSize node).y
  report "rust: cellsystem_fixed_port_label_inside_part_uses_real_position (height > 60)" (h > 60.0) s!"height {h}"

/-! ### `issue_475_test.rs` -/

/-- `tickets/core/475_fixedLayoutWithLongLabels.elkt` (comments dropped). -/
private def issue475Model : String := r"
node compound {
	layout[ size: 50, 50 position: 10, 10 ]
	algorithm: fixed

	// If this is false, the node will resize to contain its child
	nodeSize.fixedGraphSize: true

	node n1 {
		layout[ position: 200, 200 ]
	}
}
"

/-- `configure_fixed_graph_size` + `run_fixed_layout` + `assert_graph_size_behavior`. Returns one
message per violated expectation. -/
private def issue475 (fixedGraphSize : Bool) : IO (Array String) := do
  match ← Elk.Text.parseElkt issue475Model with
  | .error e => return #[s!"parse error: {e}"]
  | .ok (root, g) =>
    let (msgs, _) ← ElkM.run (do
      let children := (← ElkM.getNode root).children
      for child in children do
        ElkM.setNodeProp child FixedLayouterOptions.NODE_SIZE_FIXED_GRAPH_SIZE fixedGraphSize
        if fixedGraphSize then
          ElkM.modifyNode child fun nd => { nd with width := 20.0, height := 20.0 }
      if children.isEmpty then
        FixedLayoutProvider.layout root ProgressMonitor.null
      else
        for child in children do
          FixedLayoutProvider.layout child ProgressMonitor.null
      let mut msgs : Array String := #[]
      for node in children do
        let nd ← ElkM.getNode node
        if nd.props.getD FixedLayouterOptions.NODE_SIZE_FIXED_GRAPH_SIZE false then
          if !(close nd.width 20.0 && close nd.height 20.0) then
            msgs := msgs.push s!"fixed size changed to {nd.width}×{nd.height}"
        else
          let mut maxX := 0.0
          let mut maxY := 0.0
          for c in nd.children do
            let cn ← ElkM.getNode c
            maxX := fmax maxX (cn.x + cn.width)
            maxY := fmax maxY (cn.y + cn.height)
          if !(nd.width >= maxX && nd.height >= maxY) then
            msgs := msgs.push s!"size {nd.width}×{nd.height} does not contain ({maxX}, {maxY})"
      return msgs) g
    return msgs

def issue475Tests : Suite := suite "alg.common issue_475 (fixed layout with long labels)" do
  let fixedMsgs ← issue475 true
  report "rust: test_compound_node_size (fixed graph size keeps 20×20)" fixedMsgs.isEmpty (", ".intercalate fixedMsgs.toList)
  let resizableMsgs ← issue475 false
  report "rust: test_compound_node_size (resizable graph contains its child)" resizableMsgs.isEmpty
    (", ".intercalate resizableMsgs.toList)

def suites : Array Tests.Suite :=
  #[nodeMarginTests, dimensionTests, microLayoutTests, nextToPortRuleTests, portLabelPlacementTests,
    nodeMicroLayoutTests, cellSystemProcessTests, issue475Tests]

end Tests.AlgCommon.NodeSpacing.All
