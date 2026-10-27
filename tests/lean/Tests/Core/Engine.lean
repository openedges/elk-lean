import Tests.Framework
import Elk.Api
/-! Test suites for the layout engine and the core providers (ported from elk-rs
`plugins/org.eclipse.elk.core/tests/all`): `recursive_graph_layout_engine_test.rs`,
`recursive_graph_layout_engine_integration_test.rs`, `fixed_layout_provider_test.rs`,
`issue_457_test.rs`, `issue_489_test.rs`, the not yet covered parts of
`layout_option_parse_test.rs`, plus the fixture-driven suite `core.engine.fixtures`
(`tests/fixtures/core/<name>.json` against the elk-rs oracle output `<name>.expected.json`).

Only the `fixed`, `random` and `box` providers exist; `org.eclipse.elk.layered` has no provider
yet, so tests that Rust runs with `layered` use `box` (or a compound-capable test algorithm
backed by the box provider, `test.engine.compound`) with a `TODO(phase4)` comment.

Skipped Rust tests: the `TestController` tests of
`recursive_graph_layout_engine_integration_test.rs` (no `TestController` in the Lean port) and
`util_misc_test.rs` (no `DefaultFactory`, `Maybe`, `Triple`, `Quadruple`, `WrappedException`).
-/
namespace Tests.Core.Engine

open Tests Elk Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Data

/-! ### Helpers -/

/-- Substring test. -/
private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- `RecursiveGraphLayoutEngine::layout(root, monitor)` on the arena; returns the laid-out graph. -/
private def layoutRoot (g : ElkGraph) (root : NodeId) (monitor : ProgressMonitor := ProgressMonitor.null) :
    IO ElkGraph := do
  let (_, g) ← ElkM.run (RecursiveGraphLayoutEngine.layout root monitor) g
  return g

/-- Message of the exception thrown by the layout, `none` when it succeeds. -/
private def layoutError (g : ElkGraph) (root : NodeId) : IO (Option String) := do
  try
    let _ ← layoutRoot g root
    return none
  catch e => return some (toString e)

/-- `TestGraph::new()` / `create_graph(algorithm)`: root with two 10x10 children. The algorithm is
set on the root when given. Returns the graph, the root and the children. -/
private def twoChildGraph (algorithm : Option String) : ElkGraph × NodeId × NodeId × NodeId :=
  let (g, root) := ElkGraphUtil.createGraph
  let g := match algorithm with
    | some a => g.setNodeProp root CoreOptions.ALGORITHM a
    | none => g
  let (g, left) := g.createNode (some root)
  let (g, right) := g.createNode (some root)
  let g := g.modifyNode left (·.setSize ⟨10.0, 10.0⟩)
  let g := g.modifyNode right (·.setSize ⟨10.0, 10.0⟩)
  (g, root, left, right)

/-- Adds an 8x8 child to `parent`. -/
private def addGrandchild (g : ElkGraph) (parent : NodeId) : ElkGraph × NodeId :=
  let (g, gc) := g.createNode (some parent)
  (g.modifyNode gc (·.setSize ⟨8.0, 8.0⟩), gc)

/-- Id of a compound-capable test algorithm that is laid out by the box provider. -/
private def compoundId : String := "test.engine.compound"

/-- Registers `test.engine.compound`: supports `COMPOUND` (so that `INCLUDE_CHILDREN` takes
effect in the engine) and runs the `box` provider.
TODO(phase4): Rust uses `org.eclipse.elk.layered` for these tests. -/
private def registerCompound : IO Unit := do
  if (← LayoutMetaDataService.getAlgorithmData compoundId).isNone then
    let data : LayoutAlgorithmData := { id := compoundId, name := "Test Compound Box" }
    LayoutMetaDataService.registerAlgorithm (data.addSupportedFeature .compound)
  LayoutProvider.register compoundId (fun _ => BoxLayoutProvider.provider)

/-! ### `recursive_graph_layout_engine_test.rs` -/

/-- `recursive_graph_layout_engine_test.rs`. -/
def recursiveEngineTests : Suite := suite "core.engine.RecursiveGraphLayoutEngine" do
  Elk.Api.ensureInitialized
  -- test_unresolved_graph
  let (g, root, _, _) := twoChildGraph (some "org.eclipse.elk.box")
  let g ← layoutRoot g root (← ProgressMonitor.basic)
  check "test_unresolved_graph: width > 0" ((g.node root).width > 0.0)
  check "test_unresolved_graph: height > 0" ((g.node root).height > 0.0)
  -- test_resolved_graph
  let (g, root, _, _) := twoChildGraph none
  match ← LayoutMetaDataService.getAlgorithmData "org.eclipse.elk.box" with
  | none => report "test_resolved_graph: box algorithm data" false "missing"
  | some algorithm =>
    let g := g.setNodeProp root CoreOptions.RESOLVED_ALGORITHM algorithm.id
    let g ← layoutRoot g root (← ProgressMonitor.basic)
    check "test_resolved_graph: width > 0" ((g.node root).width > 0.0)
    check "test_resolved_graph: height > 0" ((g.node root).height > 0.0)
  -- test_unknown_algorithm_id (#[should_panic])
  let (g, root, _, _) := twoChildGraph (some "foo.Bar")
  match ← layoutError g root with
  | some msg =>
    check "test_unknown_algorithm_id: class" (msg.startsWith "org.eclipse.elk.core.UnsupportedConfigurationException: ")
    check "test_unknown_algorithm_id: names the algorithm" (has msg "Layout algorithm 'foo.Bar' not found for")
  | none => report "test_unknown_algorithm_id: throws" false "expected an exception"
  -- test_empty_algorithm_id: the default algorithm is resolved to layered.
  -- The layered provider runs the real pipeline; while P3 is unported the layout throws after the
  -- resolver ran (the state survives the exception because `ElkM` is a `StateRefT`).
  let (g, root, _, _) := twoChildGraph none
  let (msg, g) ← ElkM.run (do
    try
      RecursiveGraphLayoutEngine.layout root ProgressMonitor.null
      return (none : Option String)
    catch e => return some (toString e)) g
  checkEq "test_empty_algorithm_id: resolved algorithm" ((g.node root).props.get CoreOptions.RESOLVED_ALGORITHM)
    (some "org.eclipse.elk.layered")
  check "test_empty_algorithm_id: layered provider exists (Lean)"
    (msg.map (·.endsWith "is not available in this build.") != some true)
  -- (Lean) NO_LAYOUT: nothing is resolved or laid out, even for the default algorithm
  let (g, root, _, _) := twoChildGraph none
  let g := g.setNodeProp root CoreOptions.NO_LAYOUT true
  let g ← layoutRoot g root
  checkFloat "NO_LAYOUT keeps width" (g.node root).width 0.0
  checkNone "NO_LAYOUT does not resolve" ((g.node root).props.get CoreOptions.RESOLVED_ALGORITHM)
  -- (Lean) validateGraph: an unconnected edge is reported as a GraphValidationException
  let (g, root, _, _) := twoChildGraph (some "org.eclipse.elk.box")
  let (g, _) := g.createEdge (some root)
  let g := g.setNodeProp root CoreOptions.VALIDATE_GRAPH true
  match ← layoutError g root with
  | some msg => check "validate graph: reports the edge" (has msg "Edge is not connected.")
  | none => report "validate graph: throws" false "expected a GraphValidationException"

/-! ### `recursive_graph_layout_engine_integration_test.rs` -/

/-- `recursive_graph_layout_engine_integration_test.rs`. The `TestController` tests
(`non_target_test_controller_does_not_install`, `target_test_controller_attempts_install`,
`target_test_controller_attempts_install_on_target_descendant`) are skipped: the Lean port has no
`TestController`. The hierarchy tests use `test.engine.compound` (box provider with the
`COMPOUND` feature) instead of `layered`. -/
def recursiveEngineIntegrationTests : Suite := suite "core.engine.RecursiveGraphLayoutEngine.integration" do
  Elk.Api.ensureInitialized
  registerCompound
  -- include_children_conflicts_with_topdown_layout (#[should_panic]), TODO(phase4): layered
  let (g, root, _, _) := twoChildGraph (some compoundId)
  let g := g.setNodeProp root CoreOptions.HIERARCHY_HANDLING HierarchyHandling.includeChildren
  let g := g.setNodeProp root CoreOptions.TOPDOWN_LAYOUT true
  checkEq "include_children_conflicts_with_topdown_layout" (← layoutError g root)
    (some "org.eclipse.elk.core.UnsupportedConfigurationException: Topdown layout cannot be used together with hierarchy handling.")
  -- include_children_inherits_hierarchy_handling_for_descendants, TODO(phase4): layered
  let (g, root, left, _) := twoChildGraph (some compoundId)
  let g := g.setNodeProp root CoreOptions.HIERARCHY_HANDLING HierarchyHandling.includeChildren
  let (g, _) := addGrandchild g left
  let g ← layoutRoot g root (← ProgressMonitor.basic)
  checkEqR "include_children_inherits_hierarchy_handling_for_descendants"
    ((g.node left).props.get CoreOptions.HIERARCHY_HANDLING) (some HierarchyHandling.includeChildren)
  -- include_children_switching_algorithm_forces_separate_children, TODO(phase4): layered
  let (g, root, left, _) := twoChildGraph (some compoundId)
  let g := g.setNodeProp root CoreOptions.HIERARCHY_HANDLING HierarchyHandling.includeChildren
  let g := g.setNodeProp left CoreOptions.ALGORITHM "org.eclipse.elk.box"
  let (g, _) := addGrandchild g left
  let g ← layoutRoot g root (← ProgressMonitor.basic)
  checkEqR "include_children_switching_algorithm_forces_separate_children"
    ((g.node left).props.get CoreOptions.HIERARCHY_HANDLING) (some HierarchyHandling.separateChildren)
  -- hierarchy_handling_inherit_defaults_to_separate_children
  -- TODO(phase4): Rust uses layered for root and child; the child needs an algorithm of its own here
  -- because the default (layered) has no provider.
  let (g, root, left, _) := twoChildGraph (some "org.eclipse.elk.box")
  let g := g.setNodeProp left CoreOptions.ALGORITHM "org.eclipse.elk.box"
  let (g, _) := addGrandchild g left
  let g ← layoutRoot g root (← ProgressMonitor.basic)
  checkEqR "hierarchy_handling_inherit_defaults_to_separate_children: root"
    ((g.node root).props.get CoreOptions.HIERARCHY_HANDLING) (some HierarchyHandling.separateChildren)
  checkEqR "hierarchy_handling_inherit_defaults_to_separate_children: child"
    ((g.node left).props.get CoreOptions.HIERARCHY_HANDLING) (some HierarchyHandling.separateChildren)
  -- include_children_nested_algorithm_switch_forces_separate_children, TODO(phase4): layered
  let (g, root, left, _) := twoChildGraph (some compoundId)
  let g := g.setNodeProp root CoreOptions.HIERARCHY_HANDLING HierarchyHandling.includeChildren
  let (g, grandchild) := addGrandchild g left
  let g := g.setNodeProp grandchild CoreOptions.ALGORITHM "org.eclipse.elk.box"
  let g ← layoutRoot g root (← ProgressMonitor.basic)
  checkEqR "include_children_nested_algorithm_switch_forces_separate_children: child"
    ((g.node left).props.get CoreOptions.HIERARCHY_HANDLING) (some HierarchyHandling.includeChildren)
  checkEqR "include_children_nested_algorithm_switch_forces_separate_children: grandchild"
    ((g.node grandchild).props.get CoreOptions.HIERARCHY_HANDLING) (some HierarchyHandling.separateChildren)

/-! ### `fixed_layout_provider_test.rs` -/

/-- `fixed_layout_provider_test.rs`. -/
def fixedLayoutProviderTests : Suite := suite "core.engine.FixedLayoutProvider" do
  Elk.Api.ensureInitialized
  -- fixed_layout_applies_positions_and_sizes
  let (g, root) := ElkGraphUtil.createGraph
  let (g, child) := g.createNode (some root)
  let g := g.modifyNode child fun n =>
    { n.setSize ⟨30.0, 40.0⟩ with props := n.props.set FixedLayouterOptions.POSITION (KVector.mk 10.0 20.0) }
  let (g, label) := g.createLabel (some (.node child))
  let g := g.modifyLabel label fun l =>
    { l.setSize ⟨5.0, 5.0⟩ with props := l.props.set FixedLayouterOptions.POSITION (KVector.mk 2.0 3.0) }
  let g := g.setNodeProp root FixedLayouterOptions.PADDING ({} : ElkPadding)
  let (_, g) ← ElkM.run (FixedLayoutProvider.layout root ProgressMonitor.null) g
  let c := g.node child
  checkFloat "child x" c.x 10.0 0.0
  checkFloat "child y" c.y 20.0 0.0
  let r := g.node root
  checkFloat "root x" r.x 0.0 0.0
  checkFloat "root y" r.y 0.0 0.0
  check "root width >= child right" (r.width >= c.x + c.width)
  check "root height >= child bottom" (r.height >= c.y + c.height)
  let l := g.label label
  checkFloat "label x" l.x 2.0 0.0
  checkFloat "label y" l.y 3.0 0.0

/-! ### `issue_457_test.rs`, `issue_489_test.rs` -/

/-- `issue_457_test.rs`, `issue_489_test.rs`. -/
def issueTests : Suite := suite "core.engine.issues" do
  Elk.Api.ensureInitialized
  -- issue_457_minimum_size_respected
  let minSize : Float := 60.0
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root CoreOptions.ALGORITHM "org.eclipse.elk.box"
  let (g, node1) := g.createNode (some root)
  let (g, node2) := g.createNode (some root)
  let mut h := g
  for node in #[node1, node2] do
    h := h.setNodeProp node CoreOptions.ALGORITHM "org.eclipse.elk.box"
    h := h.setNodeProp node BoxLayouterOptions.NODE_SIZE_CONSTRAINTS SizeConstraint.minimumSizeSet
    h := h.setNodeProp node BoxLayouterOptions.NODE_SIZE_MINIMUM (KVector.mk minSize minSize)
    let (g', child) := h.createNode (some node)
    h := g'.modifyNode child (·.setSize ⟨5.0, 5.0⟩)
  let g ← layoutRoot h root
  for node in #[node1, node2] do
    checkFloat "issue_457: width" (g.node node).width minSize 1.0
    checkFloat "issue_457: height" (g.node node).height minSize 1.0
  -- issue_489_padding_and_min_size
  let padding : Float := 5.0
  let (g0, root) := ElkGraphUtil.createGraph
  let g0 := g0.setNodeProp root CoreOptions.ALGORITHM "org.eclipse.elk.box"
  let (g0, node1) := g0.createNode (some root)
  let (g0, node2) := g0.createNode (some root)
  let mut k := g0
  for node in #[node1, node2] do
    k := k.setNodeProp node CoreOptions.ALGORITHM "org.eclipse.elk.box"
    k := k.setNodeProp node BoxLayouterOptions.PADDING (ElkPadding.ofAny padding)
    let (g', child) := k.createNode (some node)
    k := g'.modifyNode child (·.setSize ⟨20.0, 20.0⟩)
  let g ← layoutRoot k root
  for node in #[node1, node2] do
    let children := (g.node node).children
    checkEq "issue_489: one child" children.size 1
    if h : 0 < children.size then
      let child := g.node children[0]
      let parent := g.node node
      checkFloat "issue_489: child x" child.x padding 0.1
      checkFloat "issue_489: child y" child.y padding 0.1
      checkFloat "issue_489: child width" child.width (parent.width - 2.0 * padding) 0.1
      checkFloat "issue_489: child height" child.height (parent.height - 2.0 * padding) 0.1

/-! ### `layout_option_parse_test.rs` (parts not covered by `core.meta.parsing`) -/

private def optionBySuffix (suffix : String) : TestM LayoutOptionData := do
  match ← LayoutMetaDataService.getOptionDataBySuffix suffix with
  | some d => return d
  | none =>
    report s!"option '{suffix}' registered" false "missing"
    return { id := suffix }

/-- The value of the option parsed from `s`, decoded as `α`. -/
private def parsedAs {α : Type} [PropCodec α] (d : LayoutOptionData) (s : String) : Option α :=
  (d.parseValue s).bind PropCodec.dec

/-- `layout_option_parse_test.rs`. Covered elsewhere (`core.meta.parsing`, `core.util.IndividualSpacings`)
in other input forms; here the Rust inputs and the by-suffix option lookup are exercised. -/
def optionParseTests : Suite := suite "core.engine.LayoutOptionParse" do
  Elk.Api.ensureInitialized
  -- parse_object_options_kvector_and_chain
  let position ← optionBySuffix "position"
  checkEqR "kvector (1.5, 2.5)" (parsedAs position "(1.5, 2.5)" : Option KVector) (some (KVector.mk 1.5 2.5))
  let bendPoints ← optionBySuffix "bendPoints"
  match (parsedAs bendPoints "(1,2; 3,4)" : Option KVectorChain) with
  | some chain =>
    checkEq "chain size" chain.size 2
    checkEqR "chain 0" chain[0]! (KVector.mk 1.0 2.0)
    checkEqR "chain 1" chain[1]! (KVector.mk 3.0 4.0)
  | none => report "kvector chain (1,2; 3,4)" false "not parsed"
  -- parse_object_options_padding_and_margin
  let paddingOption ← optionBySuffix "nodeLabels.padding"
  checkEqR "padding" (parsedAs paddingOption "[top=1,left=2,bottom=3,right=4]" : Option ElkPadding)
    (some (ElkPadding.ofValues 1.0 4.0 3.0 2.0))
  let marginOption ← optionBySuffix "spacing.portsSurrounding"
  checkEqR "margin" (parsedAs marginOption "[top=5,left=6,bottom=7,right=8]" : Option ElkMargin)
    (some (ElkMargin.ofValues 5.0 8.0 7.0 6.0))
  -- parse_object_option_individual_spacings
  -- (Lean) `LayoutOptionData.parseValue` has no usable parser for `spacing.individual` (see
  -- `core.meta.parsing`); the string form is parsed by `IndividualSpacings.parse` against the registry.
  let individual ← optionBySuffix "spacing.individual"
  check "spacing.individual has a parser" individual.canParseValue
  match ← IndividualSpacings.parse "nodeNode:10;,;nodeLabels.padding:[top=1,left=2,bottom=3,right=4]" with
  | .error e => report "individual spacings parsed" false e
  | .ok spacings =>
    checkEqR "individual nodeNode" (spacings.props.get CoreOptions.SPACING_NODE_NODE) (some 10.0)
    checkEqR "individual nodeLabels.padding" (spacings.props.get CoreOptions.NODE_LABELS_PADDING)
      (some (ElkPadding.ofValues 1.0 4.0 3.0 2.0))
  -- parse_enum_and_enumset_options
  let direction ← optionBySuffix "elk.direction"
  checkEqR "direction DOWN" (parsedAs direction "DOWN" : Option Direction) (some Direction.down)
  checkEqR "direction ordinal 3" (parsedAs direction "3" : Option Direction) (some Direction.down)
  let nodeLabelsPlacement ← optionBySuffix "nodeLabels.placement"
  match (parsedAs nodeLabelsPlacement "[H_CENTER, V_TOP, INSIDE]" : Option (EnumSet NodeLabelPlacement)) with
  | some p =>
    check "nodeLabels.placement H_CENTER" (p.contains .hCenter)
    check "nodeLabels.placement V_TOP" (p.contains .vTop)
    check "nodeLabels.placement INSIDE" (p.contains .inside)
  | none => report "nodeLabels.placement parsed" false "not parsed"
  let portLabelsPlacement ← optionBySuffix "portLabels.placement"
  match (parsedAs portLabelsPlacement "[OUTSIDE, NEXT_TO_PORT_IF_POSSIBLE]" : Option (EnumSet PortLabelPlacement)) with
  | some p =>
    check "portLabels.placement OUTSIDE" (p.contains .outside)
    check "portLabels.placement NEXT_TO_PORT_IF_POSSIBLE" (p.contains .nextToPortIfPossible)
  | none => report "portLabels.placement parsed" false "not parsed"
  let edgeRouting ← optionBySuffix "edgeRouting"
  checkEqR "edgeRouting ORTHOGONAL" (parsedAs edgeRouting "ORTHOGONAL" : Option EdgeRouting) (some EdgeRouting.orthogonal)
  let shapeCoords ← optionBySuffix "json.shapeCoords"
  checkEqR "shapeCoords ROOT" (parsedAs shapeCoords "ROOT" : Option ShapeCoords) (some ShapeCoords.root)
  let edgeCoords ← optionBySuffix "json.edgeCoords"
  checkEqR "edgeCoords PARENT" (parsedAs edgeCoords "PARENT" : Option EdgeCoords) (some EdgeCoords.parent)
  let hierarchy ← optionBySuffix "hierarchyHandling"
  checkEqR "hierarchyHandling INCLUDE_CHILDREN" (parsedAs hierarchy "INCLUDE_CHILDREN" : Option HierarchyHandling)
    (some HierarchyHandling.includeChildren)
  let contentAlignment ← optionBySuffix "contentAlignment"
  match (parsedAs contentAlignment "[V_BOTTOM, H_RIGHT]" : Option (EnumSet ContentAlignment)) with
  | some a =>
    check "contentAlignment V_BOTTOM" (a.contains .vBottom)
    check "contentAlignment H_RIGHT" (a.contains .hRight)
  | none => report "contentAlignment parsed" false "not parsed"

/-! ### Fixtures: elk-rs oracle output -/

/-- Fixture input names (`<name>.json` without the `.expected.json` files), sorted. -/
private def fixtureNames (dir : System.FilePath) : IO (Array String) := do
  let entries ← System.FilePath.readDir dir
  let names := entries.filterMap fun e =>
    if e.fileName.endsWith ".json" && !e.fileName.endsWith ".expected.json" then
      some (e.fileName.dropEnd ".json".length).toString
    else none
  return names.qsort (fun a b => a < b)

/-- Directory of the fixtures (`lake test` runs in the project root). -/
private def fixtureDir : System.FilePath := "tests/fixtures/core"

/-- Fixtures whose oracle output needs `org.eclipse.elk.layered` (a nested node without an
algorithm falls back to the default algorithm): skipped while the layered pipeline is incomplete.
`box`: node `n4` has a child and no `elk.algorithm`. -/
private def layeredFixtures : Array String := #["box"]

/-- `core.engine.fixtures`: `Elk.Api.layoutJson` on every `tests/fixtures/core/<name>.json` must
reproduce `<name>.expected.json` (the elk-rs oracle output) byte-for-byte. The directory is
enumerated at run time, so new fixtures are picked up automatically. -/
def fixtureTests : Suite := suite "core.engine.fixtures" do
  let names ← fixtureNames fixtureDir
  check "fixtures found" (names.size > 0)
  for name in names do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    let expectedPath := fixtureDir / s!"{name}.expected.json"
    if !(← expectedPath.pathExists) then
      report s!"{name}: expected output exists" false s!"missing {expectedPath}"
    else
      let expected ← IO.FS.readFile expectedPath
      match ← Elk.Api.layoutJson input "{}" (lenient := false) (pretty := true) (sortKeys := true) with
      | .error e =>
        -- TODO(phase4): remove the entry once the layered pipeline is complete (P3 pending).
        if layeredFixtures.contains name && has e "is not ported yet" then
          IO.println s!"SKIP core.engine.fixtures / {name}: needs the complete layered pipeline"
        else
          report s!"{name}: layout" false e
      | .ok actual => checkEq s!"{name}: matches oracle" actual expected

def suites : Array Tests.Suite :=
  #[recursiveEngineTests, recursiveEngineIntegrationTests, fixedLayoutProviderTests, issueTests,
    optionParseTests, fixtureTests]

end Tests.Core.Engine
