import Tests.Framework
import Elk.Core
/-! Test suites for `org.eclipse.elk.core.util` (ported from elk-rs `plugins/org.eclipse.elk.core/tests/all`):
`basic_progress_monitor_test.rs`, `property_test.rs`, `elk_util_test.rs`, `individual_spacings_test.rs`,
`spacing_configuration_test.rs`, `layout_algorithm_resolver_test.rs`, `deprecated_layout_option_replacer_test.rs`,
`layout_configurator_test.rs`. Tests of `DefaultFactory`, `Maybe`, `Triple`,
`Quadruple` and `WrappedException` (`util_misc_test.rs`) are skipped: those utilities are not ported yet. -/
namespace Tests.Core.Util

open Tests Elk Elk.Core.Util Elk.Core.Math Elk.Graph

def basicProgressMonitor : Suite := suite "core.util.BasicProgressMonitor" do
  -- basic_progress_monitor_tracks_logs_and_time
  let m ← ProgressMonitor.basic
  let m ← (← m.withLogging).withExecutionTimeMeasurement
  check "begin" (← m.begin "Task" 10.0)
  m.worked 5.0
  m.log "hello"
  m.done
  check "not running after done" (!(← m.isRunning))
  checkEq "task name" (← m.taskName) (some "Task")
  let logs ← m.logs
  checkEq "log count" logs.size 1
  checkEq "log message" logs[0]! "hello"
  check "execution time >= 0" ((← m.executionTime) >= 0.0)
  check "execution time measured" (← m.isExecutionTimeMeasured)

def progressMonitorSemantics : Suite := suite "core.util.ProgressMonitor.semantics" do
  let m ← ProgressMonitor.basic
  check "begin once" (← m.begin "A" 4.0)
  check "begin twice returns false" (!(← m.begin "B" 1.0))
  check "running" (← m.isRunning)
  m.worked 1.5
  checkFloat "completed" (← m.completedWork) 1.5
  m.worked (-3.0)
  checkFloat "negative work ignored" (← m.completedWork) 1.5
  m.worked 100.0
  m.done
  checkFloat "worked saturates by done" (← m.completedWork) 101.5
  checkEq "task name kept" (← m.taskName) (some "A")
  checkThrows "begin after done throws" (do let _ ← m.begin "C" 1.0)
  m.done
  -- logs are only recorded when enabled
  let m2 ← ProgressMonitor.basic
  m2.log "ignored"
  checkEq "no logs without logging" (← m2.logs).size 0
  let _ ← m2.withLogging
  m2.log "kept"
  m2.logGraph "" .json
  checkEq "log recorded" (← m2.logs) #["kept"]
  checkEqR "logged graph" (← m2.loggedGraphs) #[{ tag := "Unnamed", graphType := .json : LoggedGraph }]
  let _ ← m2.withLogging false
  checkEq "disabling clears logs" (← m2.logs).size 0
  -- done without begin
  let m3 ← ProgressMonitor.basic
  checkThrows "done before begin throws" m3.done

def progressMonitorSubTasks : Suite := suite "core.util.ProgressMonitor.subTask" do
  let m ← ProgressMonitor.basic
  let _ ← m.withLogging
  let _ ← m.begin "root" 10.0
  let sub ← m.subTask 4.0
  check "sub logging inherited" (← sub.isLoggingEnabled)
  let _ ← sub.begin "sub" 2.0
  sub.worked 1.0
  checkFloat "propagated half of child share" (← m.completedWork) 2.0
  sub.done
  checkFloat "child done propagates the full share" (← m.completedWork) 4.0
  -- null monitors
  let n := ProgressMonitor.null
  check "null begin false" (!(← n.begin "x" 1.0))
  check "null not running" (!(← n.isRunning))
  check "null not canceled" (!(← n.isCanceled))
  checkEq "null task name" (← n.taskName) none
  let nsub ← n.subTask 1.0
  check "null sub task is null" (!(← nsub.begin "y" 1.0))
  -- closed monitors hand out null sub monitors
  m.done
  let late ← m.subTask 1.0
  check "sub task of closed monitor is null" (!(← late.begin "z" 1.0))
  -- max hierarchy levels: level 0 does not propagate
  let top ← ProgressMonitor.basic 0
  let _ ← top.begin "top" 10.0
  let child ← top.subTask 5.0
  let _ ← child.begin "child" 1.0
  child.worked 1.0
  checkFloat "no propagation with maxLevels = 0" (← top.completedWork) 0.0
  -- cancellation
  let c ← ProgressMonitor.basic
  check "not canceled" (!(← c.isCanceled))
  c.cancel
  check "canceled" (← c.asCancelIndicator.isCanceled)

def abstractRandomListAccessor : Suite := suite "core.util.AbstractRandomListAccessor" do
  let a : AbstractRandomListAccessor Nat := { provideDefault := fun _ => 7 }
  let a := a.setListItem 3 1
  checkEqR "set beyond end fills with defaults" a.list #[7, 7, 7, 1]
  let (v, a) := a.getListItem 5
  checkEq "get beyond end" v 7
  checkEq "size after get" a.getListSize 6
  let a := a.setListItem 0 9
  checkEqR "set inside" (a.list.extract 0 2) #[9, 7]
  checkEq "cleared" (a.clearList.getListSize) 0

def exclusiveBounds : Suite := suite "core.util.ExclusiveBounds" do
  let lo := ExclusiveBounds.greaterThan 0.0
  check "lower: 1 is above" (lo.compareTo 1.0 == .lt)
  check "lower: 0 is not above" (lo.compareTo 0.0 == .gt)
  check "lower: -1 is not above" (lo.compareTo (-1.0) == .gt)
  let hi := ExclusiveBounds.lessThan 5.0
  check "upper: 4 is below" (hi.compareTo 4.0 == .gt)
  check "upper: 5 is not below" (hi.compareTo 5.0 == .lt)
  checkEq "lower toString" (toString lo) "0.0 (exclusive)"
  check "lower equality" (lo == ExclusiveBounds.greaterThan 0.0)
  check "bound variants differ" (ExclusiveBound.lower lo != ExclusiveBound.upper (ExclusiveBounds.lessThan 0.0))

def elkTrace : Suite := suite "core.util.ElkTrace" do
  -- the flags are read once from the environment; just make sure they are accessible
  let t := ElkTrace.global
  check "flags readable" (t.trace || !t.trace)

/-! `property_test.rs`: `Property.with_default(...).get_default()` returns the default value. -/

elk_enum PortSideT := undefined north east south west
elk_enum SizeConstraintT := portLabels nodeLabels ports portsOverhang minimumSize

private def checkDefault {α : Type} [BEq α] (name : String) (d : α) : TestM Unit := do
  let p : Property α := Property.withDefault "dummy" d
  match p.default with
  | some c => check name (c == d)
  | none => check s!"{name} (no default)" false

def propertyTests : Suite := suite "core.util.Property" do
  -- test_property_default_primitives
  checkDefault "default int" (43 : Int)
  checkDefault "default float" (Float.toF32 23.3)
  checkDefault "default double" (32.3 : Float)
  checkDefault "default string" "foo"
  -- test_property_default_i_data_object
  let v : KVector := ⟨2.0, 3.0⟩
  checkDefault "default KVector" v
  checkDefault "default KVectorChain" (#[v, v] : KVectorChain)
  checkDefault "default ElkPadding" (⟨2.0, 3.0, 2.0, 3.0⟩ : ElkPadding)
  checkDefault "default ElkMargin" (⟨3.0, 2.0, 3.0, 2.0⟩ : ElkMargin)
  -- test_property_default_object (Vec / LinkedList / BTreeSet; HashSet and LinkedHashSet are skipped)
  let v : KVector := ⟨3.0, 2.0⟩
  let al : Array KVector := #[v, v.normalize, v.negate]
  checkDefault "default Vec<KVector>" al
  checkDefault "default LinkedList<KVector>" al
  checkDefault "default BTreeSet<i32>" (#[1, 2, 3, 4] : Array Nat)
  -- test_property_default_enum
  checkDefault "default enum" PortSideT.east
  -- test_property_default_enum_set
  checkDefault "default EnumSet" (EnumSet.empty : EnumSet SizeConstraintT)
  -- a property without default has none
  let q : Property Int := Property.mk' "nodefault"
  checkNone "no default" q.default

section ElkUtilTests

open Elk.Core.Options Elk.Core.Data

/-- Registers the metadata the ported tests rely on when the registry does not have it
(the core metadata providers are registered by another module). Existing entries are
never replaced. -/
def ensureTestMetadata : IO Unit := do
  if (← LayoutMetaDataService.getAlgorithmData "org.eclipse.elk.layered").isNone then
    LayoutMetaDataService.registerAlgorithm { id := "org.eclipse.elk.layered", name := "ELK Layered" }
  let ensureOption (o : LayoutOptionData) : IO Unit := do
    if (← LayoutMetaDataService.getOptionData o.id).isNone then
      LayoutMetaDataService.registerLayoutMetaDataProvider { apply := (·.registerOption o) }
  ensureOption (LayoutOptionData.mk' CoreOptions.NODE_LABELS_PADDING.id .object "Node Label Padding" ""
    #[.parents] (parser := some LayoutOptionData.paddingParser))
  ensureOption (LayoutOptionData.mk' CoreOptions.SPACING_PORTS_SURROUNDING.id .object "Additional Port Space" ""
    #[.parents] (parser := some LayoutOptionData.marginsParser))
  ensureOption (LayoutOptionData.mk' CoreOptions.ASPECT_RATIO.id .double "Aspect Ratio" ""
    #[.parents] (lowerBound := some (OptionBound.greaterThan 0.0)))

private def runM {α : Type} (g : ElkGraph) (x : ElkM α) : IO (α × ElkGraph) := ElkM.run x g

/-- elk_util_test.rs `create_content_alignment_test_graph`: returns the graph, the node and its child. -/
private def contentAlignmentGraph (alignment : Option (EnumSet ContentAlignment)) : ElkGraph × NodeId × NodeId :=
  let (g, parent) := ElkGraphUtil.createGraph
  let (g, node) := g.createNode (some parent)
  let g := match alignment with
    | some a => g.setNodeProp node CoreOptions.CONTENT_ALIGNMENT a
    | none => g
  let (g, inner) := g.createNode (some node)
  let g := g.modifyNode node (·.setSize ⟨100.0, 100.0⟩)
  let g := g.modifyNode inner (·.setSize ⟨80.0, 80.0⟩)
  (g, node, inner)

private def assertTranslation (name : String) (alignment : Option (EnumSet ContentAlignment))
    (expectedX expectedY : Float) : TestM Unit := do
  let (g, node, inner) := contentAlignmentGraph alignment
  let (_, g) ← runM g (ElkUtil.translateNodeWithSizes node ⟨120.0, 120.0⟩ ⟨100.0, 100.0⟩)
  let n := g.node inner
  check s!"{name} x" ((n.x - expectedX).abs <= 1.0)
  check s!"{name} y" ((n.y - expectedY).abs <= 1.0)

def elkUtilTests : Suite := suite "core.util.ElkUtil" do
  -- translate_with_content_alignment_test
  assertTranslation "none" none 0.0 0.0
  assertTranslation "topLeft" (some ContentAlignment.topLeft) 0.0 0.0
  assertTranslation "topCenter" (some ContentAlignment.topCenter) 10.0 0.0
  assertTranslation "vTop hRight" (some (EnumSet.of #[.vTop, .hRight])) 20.0 0.0
  assertTranslation "vCenter hLeft" (some (EnumSet.of #[.vCenter, .hLeft])) 0.0 10.0
  assertTranslation "centerCenter" (some ContentAlignment.centerCenter) 10.0 10.0
  assertTranslation "vCenter hRight" (some (EnumSet.of #[.vCenter, .hRight])) 20.0 10.0
  assertTranslation "vBottom hLeft" (some (EnumSet.of #[.vBottom, .hLeft])) 0.0 20.0
  assertTranslation "vBottom hCenter" (some (EnumSet.of #[.vBottom, .hCenter])) 10.0 20.0
  assertTranslation "bottomRight" (some ContentAlignment.bottomRight) 20.0 20.0
  -- absolute_position_test
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.modifyNode root (·.setPosition ⟨10.0, 20.0⟩)
  let (g, child) := g.createNode (some root)
  let g := g.modifyNode child (·.setPosition ⟨5.0, 7.0⟩)
  let (g, port) := g.createPort (some child)
  let g := g.modifyPort port (·.setPosition ⟨2.0, 3.0⟩)
  let (g, label) := g.createLabel (some (.port port))
  let g := g.modifyLabel label (·.setPosition ⟨1.0, 1.0⟩)
  checkEq "root position" (ElkUtil.absolutePosition g (.node root)) (some ⟨10.0, 20.0⟩)
  checkEq "child position" (ElkUtil.absolutePosition g (.node child)) (some ⟨15.0, 27.0⟩)
  checkEq "port position" (ElkUtil.absolutePosition g (.port port)) (some ⟨17.0, 30.0⟩)
  checkEq "label position" (ElkUtil.absolutePosition g (.label label)) (some ⟨18.0, 31.0⟩)
  -- vector_chain_round_trip_test
  let (g, s) := ({} : ElkGraph).createSection none
  let g := g.modifySection s fun sec =>
    { sec with startX := 0.0, startY := 0.0, endX := 10.0, endY := 0.0,
               bendPoints := #[⟨2.0, 0.0⟩, ⟨5.0, 5.0⟩] }
  let chain := ElkUtil.createVectorChain g s
  checkEq "vector chain" chain.toList [⟨0.0, 0.0⟩, ⟨2.0, 0.0⟩, ⟨5.0, 5.0⟩, ⟨10.0, 0.0⟩]
  let g := g.modifySection s fun sec => { sec with bendPoints := sec.bendPoints.push ⟨0.0, 0.0⟩ }
  let newChain : KVectorChain := #[⟨0.0, 0.0⟩, ⟨1.0, 1.0⟩, ⟨2.0, 2.0⟩, ⟨3.0, 3.0⟩]
  let (_, g) ← runM g (ElkUtil.applyVectorChain newChain s)
  let sec := g.edgeSection s
  checkFloat "start x" sec.startX 0.0
  checkFloat "start y" sec.startY 0.0
  checkFloat "end x" sec.endX 3.0
  checkFloat "end y" sec.endY 3.0
  checkEq "bend point count" sec.bendPoints.size 2
  checkEq "bend 0" sec.bendPoints[0]! ⟨1.0, 1.0⟩
  checkEq "bend 1" sec.bendPoints[1]! ⟨2.0, 2.0⟩
  check "short chain rejected" (ElkUtil.Pure.applyVectorChain g #[⟨0.0, 0.0⟩] s |>.toOption).isNone
  -- compute_inside_part_test
  checkFloat "inside part" (ElkUtil.computeInsidePart ⟨0.0, 5.0⟩ ⟨10.0, 10.0⟩ ⟨10.0, 10.0⟩ 0.0 .north) 5.0
  -- determine_junction_points_empty_for_single_edge
  let (g, graph) := ElkGraphUtil.createGraph
  let (g, sourceNode) := g.createNode (some graph)
  let (g, sourcePort) := g.createPort (some sourceNode)
  let (g, targetNode) := g.createNode (some graph)
  let (g, targetPort) := g.createPort (some targetNode)
  let (g, edge) := g.createEdge (some graph)
  let g := g.addEdgeSource edge (.port sourcePort)
  let g := g.addEdgeTarget edge (.port targetPort)
  let (g, s) := g.createSection (some edge)
  let g := g.modifySection s fun sec => { sec with startX := 0.0, startY := 0.0, endX := 10.0, endY := 0.0 }
  match ElkUtil.determineJunctionPoints g edge with
  | .ok jps => check "no junction points" jps.isEmpty
  | .error e => report "no junction points" false e
  -- an edge without section is rejected (Java IllegalArgumentException)
  let (g, edge2) := g.createEdge (some graph)
  check "edge without section rejected" (ElkUtil.determineJunctionPoints g edge2 |>.toOption).isNone

/-- `individual_spacings_test.rs`. -/
def individualSpacingsTests : Suite := suite "core.util.IndividualSpacings" do
  ensureTestMetadata
  -- individual_spacings_serializes_object_values
  let padding := ElkPadding.ofValues 1.0 2.0 3.0 4.0
  let margin := ElkMargin.ofValues 5.0 6.0 7.0 8.0
  let spacings : IndividualSpacings :=
    { props := (({} : PropertyMap).set CoreOptions.NODE_LABELS_PADDING padding).set
        CoreOptions.SPACING_PORTS_SURROUNDING margin }
  let serialized := toString spacings
  let contains (s sub : String) : Bool := (s.splitOn sub).length > 1
  check "contains padding id" (contains serialized "org.eclipse.elk.nodeLabels.padding")
  check "contains padding" (contains serialized "[top=1,left=4,bottom=3,right=2]")
  check "contains margin id" (contains serialized "org.eclipse.elk.spacing.portsSurrounding")
  check "contains margin" (contains serialized "[top=5,left=8,bottom=7,right=6]")
  match ← IndividualSpacings.parse serialized with
  | .error e => report "parse individual spacings" false e
  | .ok parsed =>
    checkEqR "padding parsed" (parsed.props.get CoreOptions.NODE_LABELS_PADDING) (some padding)
    checkEqR "margin parsed" (parsed.props.get CoreOptions.SPACING_PORTS_SURROUNDING) (some margin)
  -- (Lean) getIndividualOrInherited: individual value, then the parent's value
  let (g, root) := ElkGraphUtil.createGraph
  let (g, node) := g.createNode (some root)
  let g := g.setNodeProp root CoreOptions.SPACING_NODE_NODE 33.0
  checkEqR "inherited from parent" (IndividualSpacings.getIndividualOrInherited g node CoreOptions.SPACING_NODE_NODE) (some 33.0)
  let individual : IndividualSpacings := { props := ({} : PropertyMap).set CoreOptions.SPACING_NODE_NODE 7.0 }
  let g := g.setNodeProp node CoreOptions.SPACING_INDIVIDUAL individual
  checkEqR "individual value" (IndividualSpacings.getIndividualOrInherited g node CoreOptions.SPACING_NODE_NODE) (some 7.0)
  checkEqR "root without individual" (IndividualSpacings.getIndividualOrInherited g root CoreOptions.SPACING_NODE_NODE) none
  match ← IndividualSpacings.parse "unknown.option.id:3" with
  | .error e => checkEq "invalid id" e "Invalid option id: unknown.option.id"
  | .ok _ => report "invalid id" false "expected an error"

/-- spacing_configuration_test.rs `spacing_options()`. -/
private def spacingOptions : Array (Property Float) := #[
  CoreOptions.SPACING_COMPONENT_COMPONENT,
  CoreOptions.SPACING_EDGE_EDGE,
  CoreOptions.SPACING_EDGE_LABEL,
  CoreOptions.SPACING_EDGE_NODE,
  CoreOptions.SPACING_LABEL_LABEL,
  CoreOptions.SPACING_LABEL_NODE,
  CoreOptions.SPACING_LABEL_PORT_HORIZONTAL,
  CoreOptions.SPACING_LABEL_PORT_VERTICAL,
  CoreOptions.SPACING_NODE_SELF_LOOP,
  CoreOptions.SPACING_PORT_PORT]

private def spacingEpsilon : Float := 10e-5

/-- spacing_configuration_test.rs `create_simple_graph`: root, two 30x30 children, one edge. -/
private def simpleSpacingGraph : ElkGraph × NodeId × NodeId × NodeId :=
  let (g, graph) := ElkGraphUtil.createGraph
  let (g, n1) := g.createNode (some graph)
  let (g, n2) := g.createNode (some graph)
  let g := g.modifyNode n1 (·.setSize ⟨30.0, 30.0⟩)
  let g := g.modifyNode n2 (·.setSize ⟨30.0, 30.0⟩)
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node n1) (.node n2)
  (g, graph, n1, n2)

private def nodeValue (g : ElkGraph) (n : NodeId) (o : Property Float) : Float :=
  ((g.node n).props.get o).getD 0.0

private def configureSimpleGraph (b : Except String ElkCoreSpacingsBuilder) : IO (Except String ElkGraph) := do
  match b with
  | .error e => return .error e
  | .ok b =>
    let (g, graph, _, _) := simpleSpacingGraph
    let (_, g) ← ElkM.run (ElkUtil.applyVisitors graph #[b.toVisitor]) g
    return .ok g

private def checkOptionValue (name : String) (g : ElkGraph) (o : Property Float) (value : Float) : TestM Unit := do
  for n in ElkGraphUtil.allNodes g ⟨0⟩ do
    checkFloat s!"{name} {o.id} {n}" (nodeValue g n o) value spacingEpsilon

def spacingConfigurationTests : Suite := suite "core.util.ElkSpacings" do
  ensureTestMetadata
  -- test_create_visitor
  let (g, node) := ({} : ElkGraph).createNode none
  let (_, g) ← ElkM.run ((ElkSpacings.withBaseValue 3.0).toVisitor.visit (.node node)) g
  checkFloat "visitor base spacing" (nodeValue g node ElkCoreSpacingsBuilder.BASE_SPACING_OPTION) 3.0 spacingEpsilon
  -- test_apply_to
  let (g, node) := ({} : ElkGraph).createNode none
  let (_, g) ← ElkM.run ((ElkSpacings.withBaseValue 3.0).apply (.node node)) g
  checkFloat "apply base spacing" (nodeValue g node ElkCoreSpacingsBuilder.BASE_SPACING_OPTION) 3.0 spacingEpsilon
  -- test_spacing_with_negative_factor / test_spacing_with_negative_value (should_panic)
  check "negative factor rejected"
    ((ElkSpacings.withBaseValue 33.0).withFactor CoreOptions.SPACING_EDGE_EDGE (-1.0) |>.toOption).isNone
  check "negative value rejected"
    ((ElkSpacings.withBaseValue 33.0).withValue CoreOptions.SPACING_EDGE_EDGE (-1.0) |>.toOption).isNone
  -- test_default_factors
  let builder := ElkSpacings.withBaseValue 33.0
  let baseDefault := ElkCoreSpacingsBuilder.BASE_SPACING_OPTION.default.getD 0.0
  for o in spacingOptions do
    match builder.factors.find? (·.property.id == o.id) with
    | some f => checkFloat s!"default factor {o.id}" f.factor (o.default.getD 0.0 / baseDefault) spacingEpsilon
    | none => report s!"default factor {o.id}" false "missing factor"
  -- test_spacing_with_factor / test_spacing_with_value
  for o in spacingOptions do
    match ← configureSimpleGraph ((ElkSpacings.withBaseValue 33.0).withFactor o 2.0) with
    | .ok g => checkOptionValue "with factor" g o 66.0
    | .error e => report s!"with factor {o.id}" false e
    match ← configureSimpleGraph ((ElkSpacings.withBaseValue 33.0).withValue o 24.0) with
    | .ok g => checkOptionValue "with value" g o 24.0
    | .error e => report s!"with value {o.id}" false e
  -- test_overwrite_if_requested / test_dont_overwrite_if_not_requested
  for overwrite in #[true, false] do
    for o in spacingOptions do
      let (g, graph, n1, n2) := simpleSpacingGraph
      let g := g.setNodeProp n1 o 22.0
      match (ElkSpacings.withBaseValue 1.0).withValue o 3.0 with
      | .error e => report s!"overwrite {overwrite} {o.id}" false e
      | .ok b =>
        let (_, g) ← ElkM.run (ElkUtil.applyVisitors graph #[(b.withOverwrite overwrite).toVisitor]) g
        checkFloat s!"overwrite {overwrite} first {o.id}" (nodeValue g n1 o) (if overwrite then 3.0 else 22.0) spacingEpsilon
        checkFloat s!"overwrite {overwrite} second {o.id}" (nodeValue g n2 o) 3.0 spacingEpsilon
  -- test_invalid_option_with_factor_panics / test_invalid_option_with_value_panics
  check "base option with factor rejected"
    ((ElkSpacings.withBaseValue 33.0).withFactor ElkCoreSpacingsBuilder.BASE_SPACING_OPTION 2.0 |>.toOption).isNone
  check "unknown option with value rejected"
    ((ElkSpacings.withBaseValue 33.0).withValue CoreOptions.ASPECT_RATIO 24.0 |>.toOption).isNone

/-- `layout_algorithm_resolver_test.rs`. -/
def layoutAlgorithmResolverTests : Suite := suite "core.data.LayoutAlgorithmResolver" do
  ensureTestMetadata
  let resolved (g : ElkGraph) (n : NodeId) : Option String := (g.node n).props.get CoreOptions.RESOLVED_ALGORITHM
  let runResolver (g : ElkGraph) (root : NodeId) : IO (ElkGraph × Array String) := do
    let r ← LayoutAlgorithmResolver.new
    let (_, g) ← ElkM.run (ElkUtil.applyVisitors root #[r.toVisitor]) g
    return (g, ← r.errors)
  -- resolver_sets_default_for_hierarchical_node
  let (g, root) := ElkGraphUtil.createGraph
  let (g, _) := g.createNode (some root)
  let (g, errors) ← runResolver g root
  checkEq "default for hierarchical node" (resolved g root) (some "org.eclipse.elk.layered")
  check "no errors (hierarchical)" errors.isEmpty
  -- resolver_skips_leaf_node_without_inside_self_loops
  let (g, root) := ElkGraphUtil.createGraph
  let (g, errors) ← runResolver g root
  checkEq "leaf not resolved" (resolved g root) none
  check "no errors (leaf)" errors.isEmpty
  -- resolver_sets_default_for_inside_self_loops
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE true
  let (g, errors) ← runResolver g root
  checkEq "default for inside self loops" (resolved g root) (some "org.eclipse.elk.layered")
  check "no errors (self loops)" errors.isEmpty
  -- resolver_records_error_for_unknown_algorithm
  let (g, root) := ElkGraphUtil.createGraph
  let (g, _) := g.createNode (some root)
  let g := g.setNodeProp root CoreOptions.ALGORITHM "unknown.alg"
  let (_, errors) ← runResolver g root
  checkEq "one error" errors.size 1
  check "error names the algorithm" ((errors[0]!.splitOn "unknown.alg").length > 1)
  -- resolver_accepts_suffix_algorithm_id
  let (g, root) := ElkGraphUtil.createGraph
  let (g, _) := g.createNode (some root)
  let g := g.setNodeProp root CoreOptions.ALGORITHM "layered"
  let (g, errors) ← runResolver g root
  checkEq "suffix resolved" (resolved g root) (some "org.eclipse.elk.layered")
  check "no errors (suffix)" errors.isEmpty

/-- `deprecated_layout_option_replacer_test.rs`. -/
def deprecatedLayoutOptionReplacerTests : Suite := suite "core.data.DeprecatedLayoutOptionReplacer" do
  -- replacer_moves_next_to_port_option
  let (g, graph) := ElkGraphUtil.createGraph
  let (g, node) := g.createNode (some graph)
  let g := g.setNodeProp node CoreOptions.PORT_LABELS_NEXT_TO_PORT_IF_POSSIBLE true
  let (_, g) ← ElkM.run (ElkUtil.applyVisitors graph #[DeprecatedLayoutOptionReplacer.new]) g
  match (g.node node).props.get? CoreOptions.PORT_LABELS_PLACEMENT with
  | some placement =>
    check "outside kept" (placement.contains .outside)
    check "next to port added" (placement.contains .nextToPortIfPossible)
  | none => report "placement set" false "expected placement to be set"
  check "old flag removed" !((g.node node).props.has CoreOptions.PORT_LABELS_NEXT_TO_PORT_IF_POSSIBLE)
  -- replacer_moves_space_efficient_port_labels
  let (g, graph) := ElkGraphUtil.createGraph
  let (g, node) := g.createNode (some graph)
  let g := g.setNodeProp node CoreOptions.NODE_SIZE_OPTIONS (EnumSet.of #[SizeOptions.spaceEfficientPortLabels, .portsOverhang])
  let (_, g) ← ElkM.run (ElkUtil.applyVisitors graph #[DeprecatedLayoutOptionReplacer.new]) g
  match (g.node node).props.get? CoreOptions.NODE_SIZE_OPTIONS with
  | some options =>
    check "space efficient removed" !(options.contains .spaceEfficientPortLabels)
    check "ports overhang kept" (options.contains .portsOverhang)
  | none => report "size options set" false "expected size options to be set"
  match (g.node node).props.get? CoreOptions.PORT_LABELS_PLACEMENT with
  | some placement => check "space efficient placement" (placement.contains .spaceEfficient)
  | none => report "placement set (space efficient)" false "expected placement to be set"

/-- `layout_configurator_test.rs`. -/
def layoutConfiguratorTests : Suite := suite "core.LayoutConfigurator" do
  let newGraph : ElkGraph × NodeId × NodeId × NodeId :=
    let (g, root) := ElkGraphUtil.createGraph
    let (g, n1) := g.createNode (some root)
    let (g, n2) := g.createNode (some root)
    (g, root, n1, n2)
  let run (g : ElkGraph) (root : NodeId) (c : LayoutConfigurator) : IO ElkGraph := do
    let (_, g) ← ElkM.run (ElkUtil.applyVisitors root #[c.toVisitor]) g
    return g
  let value (g : ElkGraph) (n : NodeId) (p : Property Float) : Float := ((g.node n).props.get p).getD (-1.0)
  -- layout_configurator_element_overrides_class
  let (g, root, n1, n2) := newGraph
  let c := LayoutConfigurator.new
    |>.configureClass .node (·.set CoreOptions.SPACING_NODE_NODE 22.0)
    |>.configureNode n1 (·.set CoreOptions.SPACING_NODE_NODE 12.0)
    |>.configureNode n2 (·.set CoreOptions.SPACING_NODE_NODE 32.0)
  let g ← run g root c
  checkFloat "root from class" (value g root CoreOptions.SPACING_NODE_NODE) 22.0 0.0001
  checkFloat "n1 from element" (value g n1 CoreOptions.SPACING_NODE_NODE) 12.0 0.0001
  checkFloat "n2 from element" (value g n2 CoreOptions.SPACING_NODE_NODE) 32.0 0.0001
  -- layout_configurator_combine_element_and_class
  let (g, root, n1, _) := newGraph
  let c := LayoutConfigurator.new
    |>.configureClass .node (·.set CoreOptions.SPACING_NODE_NODE 42.0)
    |>.configureNode n1 (·.set CoreOptions.SPACING_EDGE_NODE 42.0)
  let g ← run g root c
  checkFloat "combine: class option" (value g n1 CoreOptions.SPACING_NODE_NODE) 42.0 0.0001
  checkFloat "combine: element option" (value g n1 CoreOptions.SPACING_EDGE_NODE) 42.0 0.0001
  -- layout_configurator_combine_multiple_class
  let (g, root, n1, _) := newGraph
  let c := LayoutConfigurator.new
    |>.configureClass .node (·.set CoreOptions.SPACING_NODE_NODE 42.0)
    |>.configureClass .graphElement (·.set CoreOptions.SPACING_EDGE_NODE 42.0)
  let g ← run g root c
  checkFloat "multiple: node class" (value g n1 CoreOptions.SPACING_NODE_NODE) 42.0 0.0001
  checkFloat "multiple: graph element class" (value g n1 CoreOptions.SPACING_EDGE_NODE) 42.0 0.0001
  -- layout_configurator_overrides_existing_options
  let (g, root, _, _) := newGraph
  let g := g.setNodeProp root CoreOptions.SPACING_NODE_NODE 13.0
  let c := LayoutConfigurator.new |>.configureClass .node (·.set CoreOptions.SPACING_NODE_NODE 42.0)
  let g ← run g root c
  checkFloat "overrides existing" (value g root CoreOptions.SPACING_NODE_NODE) 42.0 0.0001
  -- layout_configurator_prevent_overriding_existing_options
  let (g, root, _, _) := newGraph
  let g := g.setNodeProp root CoreOptions.SPACING_NODE_NODE 13.0
  let c := LayoutConfigurator.new
    |>.configureClass .node (·.set CoreOptions.SPACING_NODE_NODE 42.0)
    |>.addFilter LayoutConfigurator.NO_OVERWRITE
  let g ← run g root c
  checkFloat "no overwrite" (value g root CoreOptions.SPACING_NODE_NODE) 13.0 0.0001

end ElkUtilTests

def suites : Array Tests.Suite :=
  #[basicProgressMonitor, progressMonitorSemantics, progressMonitorSubTasks, abstractRandomListAccessor,
    exclusiveBounds, elkTrace, propertyTests, elkUtilTests, individualSpacingsTests, spacingConfigurationTests,
    layoutAlgorithmResolverTests, deprecatedLayoutOptionReplacerTests, layoutConfiguratorTests]

end Tests.Core.Util
