import Tests.Framework
import Tests.JsonCompare
import Elk.Api
import Elk.Alg.TopdownPacking
/-!
# Tests for `org.eclipse.elk.alg.topdownpacking`

Ports of the elk-rs tests `plugins/org.eclipse.elk.alg.topdownpacking/tests/all`:
`topdownpacking_metadata_test.rs`, `topdown_packing_test.rs`, `topdown_layout_test.rs`; plus the
fixture suite `topdownpacking.fixtures` (`tests/fixtures/topdownpacking/<name>.json` against
`<name>.expected.json`, produced by elk-rs with `TopdownpackingMetaDataProvider` and the
topdownpacking provider registered; the stock oracle runner `model_parity_layout_runner` does not
register topdownpacking).

Skipped / adapted Rust tests:
* `port_placement_calculation_test.rs` (`test_bottom_up`, `test_top_down`) lay out a hierarchical
  node with the default algorithm `org.eclipse.elk.layered`, whose pipeline is incomplete.
  TODO(phase4): port them once layered is complete.
* `topdown_layout_test.rs`: the root graph uses `org.eclipse.elk.fixed` instead of the default
  algorithm layered (`TODO(phase4)`), and `test_child_dimension_calculation` runs the top-level
  node with `fixed` instead of `layered` (the checked size is fixed by `fixedGraphSize`).
-/
namespace Tests.TopdownPacking

open Tests Elk Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Data
open Elk.Alg.TopdownPacking Elk.Alg.TopdownPacking.Options

/-! ### `topdownpacking_metadata_test.rs` -/

/-- `arrangement_strategy_defaults`, `whitespace_elimination_defaults` and the algorithm entry. -/
def metadataTests : Suite := suite "topdownpacking.metadata" do
  LayoutMetaDataService.ensureInitialized
  match ← LayoutMetaDataService.getOptionData TopdownpackingOptions.NODE_ARRANGEMENT_STRATEGY.id with
  | none => report "node arrangement option registered" false
  | some o =>
    checkEq "node arrangement group" o.group "nodeArrangement"
    check "node arrangement targets parents" (o.targets.contains .parents)
    check "node arrangement default" (((o.defaultValue.bind PropCodec.dec : Option NodeArrangementStrategy)) ==
      some .leftRightTopDownNodePlacer)
    checkEq "node arrangement choices" o.choices #["LEFT_RIGHT_TOP_DOWN_NODE_PLACER"]
    checkEq "node arrangement name" o.name "Node arrangement strategy"
    checkEq "node arrangement type" o.type LayoutOptionType.enum
  match ← LayoutMetaDataService.getOptionData TopdownpackingOptions.WHITESPACE_ELIMINATION_STRATEGY.id with
  | none => report "whitespace elimination option registered" false
  | some o =>
    checkEq "whitespace elimination group" o.group "whitespaceElimination"
    check "whitespace elimination targets parents" (o.targets.contains .parents)
    check "whitespace elimination default"
      (((o.defaultValue.bind PropCodec.dec : Option WhitespaceEliminationStrategy)) ==
        some .bottomRowEqualWhitespaceEliminator)
    checkEq "whitespace elimination choices" o.choices #["BOTTOM_ROW_EQUAL_WHITESPACE_ELIMINATOR"]
  match ← LayoutMetaDataService.getAlgorithmData TopdownpackingOptions.ALGORITHM_ID with
  | none => report "algorithm registered" false
  | some a =>
    checkEq "algorithm name" a.name "ELK Top-down Packing"
    checkEq "algorithm bundle" a.definingBundleId (some "org.eclipse.elk.alg.topdownpacking")
    checkEq "algorithm known options" a.knownOptionIds #[
      CoreOptions.PADDING.id, CoreOptions.SPACING_NODE_NODE.id,
      CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH.id, CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO.id,
      CoreOptions.TOPDOWN_LAYOUT.id, CoreOptions.TOPDOWN_NODE_TYPE.id,
      TopdownpackingOptions.NODE_ARRANGEMENT_STRATEGY.id,
      TopdownpackingOptions.WHITESPACE_ELIMINATION_STRATEGY.id]
    check "topdown node type default PARALLEL_NODE"
      (a.defaultValue CoreOptions.TOPDOWN_NODE_TYPE == some TopdownNodeTypes.parallelNode)
    check "provider registered" (← LayoutProvider.isRegistered TopdownpackingOptions.ALGORITHM_ID)
    match ← LayoutProvider.create TopdownpackingOptions.ALGORITHM_ID with
    | some p =>
      -- elk-rs does not expose `ITopdownLayoutProvider` through `AbstractLayoutProvider`
      check "registered provider has no predicted size (elk-rs)" p.predictedGraphSize.isNone
      check "providerWithPrediction (Java) has a predicted size"
        TopdownpackingLayoutProvider.providerWithPrediction.predictedGraphSize.isSome
    | none => report "provider created" false

/-! ### `topdown_packing_test.rs` -/

/-- `create_graph(n)`: a root with `n` children. -/
private def createGraph (n : Nat) : ElkGraph × NodeId × Array NodeId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let mut g := g
  let mut kids : Array NodeId := #[]
  for _ in [0:n] do
    let (g', k) := g.createNode (some root)
    g := g'
    kids := kids.push k
  return (g, root, kids)

private def layoutDirect (g : ElkGraph) (root : NodeId) : IO ElkGraph := do
  let monitor ← ProgressMonitor.basic
  let (_, g) ← ElkM.run (TopdownpackingLayoutProvider.layout root monitor) g
  return g

private def predicted (g : ElkGraph) (root : NodeId) : IO KVector := do
  let (v, _) ← ElkM.run (TopdownpackingLayoutProvider.predictedGraphSize root) g
  return v

private def checkShape (name : String) (g : ElkGraph) (n : NodeId) (x y w h : Float) : TestM Unit := do
  let nd := g.node n
  checkFloat s!"{name} x" nd.x x 1.0e-5
  checkFloat s!"{name} y" nd.y y 1.0e-5
  checkFloat s!"{name} width" nd.width w 1.0e-5
  checkFloat s!"{name} height" nd.height h 1.0e-5

/-- `test_empty_graph`, `test_two_nodes`, `test_three_nodes`, `test_five_nodes`. -/
def packingTests : Suite := suite "topdownpacking.TopdownPackingTest" do
  LayoutMetaDataService.ensureInitialized
  -- test_empty_graph
  let (g, root, _) := createGraph 0
  let g ← layoutDirect g root
  checkEq "empty graph: no children" (g.node root).children.size 0
  -- defaults
  let hw := (CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH).default.getD 0.0
  let ar := (CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO).default.getD 0.0
  let padding := (CoreOptions.PADDING).default.getD {}
  let sp := (CoreOptions.SPACING_NODE_NODE).default.getD 0.0
  -- test_two_nodes
  let (g, root, kids) := createGraph 2
  let size ← predicted g root
  checkFloat "two nodes: predicted width" size.x (padding.left + 2.0 * hw + sp + padding.right) 1.0e-5
  checkFloat "two nodes: predicted height" size.y (padding.top + hw / ar + padding.bottom) 1.0e-5
  let g ← layoutDirect g root
  checkShape "two nodes: child one" g kids[0]! padding.left padding.top hw (hw / ar)
  checkShape "two nodes: child two" g kids[1]! (padding.left + hw + sp) padding.top hw (hw / ar)
  -- test_three_nodes
  let (g, root, kids) := createGraph 3
  let size ← predicted g root
  checkFloat "three nodes: predicted width" size.x (padding.left + 2.0 * hw + sp + padding.right) 1.0e-5
  checkFloat "three nodes: predicted height" size.y
    (padding.top + 2.0 * (hw / ar) + sp + padding.bottom) 1.0e-5
  let g ← layoutDirect g root
  checkShape "three nodes: child one" g kids[0]! padding.left padding.top hw (hw / ar)
  checkShape "three nodes: child two" g kids[1]! (padding.left + hw + sp) padding.top hw (hw / ar)
  checkShape "three nodes: child three" g kids[2]! padding.left (padding.top + (hw / ar) + sp)
    (2.0 * hw + sp) (hw / ar)
  -- test_five_nodes
  let (g, root, kids) := createGraph 5
  let size ← predicted g root
  checkFloat "five nodes: predicted width" size.x (padding.left + 3.0 * hw + 2.0 * sp + padding.right) 1.0e-5
  checkFloat "five nodes: predicted height" size.y
    (padding.top + 2.0 * (hw / ar) + sp + padding.bottom) 1.0e-5
  let g ← layoutDirect g root
  let expandedWidth := hw + 0.5 * (hw + sp)
  checkShape "five nodes: child four" g kids[3]! padding.left (padding.top + (hw / ar) + sp)
    expandedWidth (hw / ar)
  -- the Rust test lays the graph out a second time before checking child five
  let g ← layoutDirect g root
  checkShape "five nodes: child five" g kids[4]! (padding.left + expandedWidth + sp)
    (padding.top + (hw / ar) + sp) expandedWidth (hw / ar)

/-! ### `topdown_layout_test.rs` -/

private def setTopdown (g : ElkGraph) (n : NodeId) (t : TopdownNodeTypes) : ElkGraph :=
  (g.setNodeProp n CoreOptions.TOPDOWN_LAYOUT true).setNodeProp n CoreOptions.TOPDOWN_NODE_TYPE t

/-- `configure_toplevel_for_scaling` + `add_fixed_child` ×2 + `run_recursive_layout`; returns the
scale factor of the top-level node. -/
private def scaleOf (width aspectRatio scaleCap : Float) : IO (Option Float) := do
  let (g, root) := ElkGraphUtil.createGraph
  let g := (setTopdown g root .rootNode).setNodeProp root CoreOptions.ALGORITHM "org.eclipse.elk.fixed"
  let (g, top) := g.createNode (some root)
  let g := setTopdown g top .hierarchicalNode
  let g := g.setNodeProp top CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE true
  let g := g.setNodeProp top CoreOptions.TOPDOWN_SCALE_CAP scaleCap
  let g := g.setNodeProp top CoreOptions.ALGORITHM "org.eclipse.elk.fixed"
  let g := g.setNodeProp top CoreOptions.PADDING ({} : ElkPadding)
  let g := g.setNodeProp top CoreOptions.SPACING_NODE_NODE 0.0
  let g := g.setNodeProp top CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH width
  let g0 := g.setNodeProp top CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO aspectRatio
  let mut g := g0
  for (x, y) in [(0.0, 0.0), (0.0, 40.0)] do
    let (g', c) := g.createNode (some top)
    g := setTopdown g' c .hierarchicalNode
    g := g.setNodeProp c CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE true
    g := g.modifyNode c fun n => { n with x := x, y := y, width := 30.0, height := 30.0 }
  let (_, g2) ← ElkM.run (RecursiveGraphLayoutEngine.layout root ProgressMonitor.null) g
  return g2.getNodeProp top CoreOptions.TOPDOWN_SCALE_FACTOR

private def checkScale (name : String) (actual : Option Float) (expected : Float) : TestM Unit :=
  match actual with
  | some s => checkFloat name s expected 1.0e-4
  | none => report name false "topdown scale factor should be set"

/-- `test_two_level_layout_horizontal_scaling`, `..._vertical_scaling`, `test_scale_cap`,
`test_scale_cap_bounded`, `test_child_dimension_calculation`. -/
def layoutTests : Suite := suite "topdownpacking.TopdownLayoutTest" do
  Elk.Api.ensureInitialized
  checkScale "horizontal scale" (← scaleOf 20.0 0.4 1.0) (20.0 / 30.0)
  checkScale "vertical scale" (← scaleOf 40.0 1.33333 1.0) (30.0 / 70.0)
  checkScale "scale cap not bounding" (← scaleOf 300.0 1.0 100.0) (300.0 / 70.0)
  checkScale "scale cap bounding" (← scaleOf 300.0 1.0 3.0) 3.0
  -- test_child_dimension_calculation (top-level node with `fixed` instead of `layered`)
  let (g, root) := ElkGraphUtil.createGraph
  let g := (setTopdown g root .rootNode).setNodeProp root CoreOptions.ALGORITHM "org.eclipse.elk.fixed"
  let (g, top) := g.createNode (some root)
  let g := setTopdown g top .hierarchicalNode
  let g := g.setNodeProp top CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE true
  let g := g.setNodeProp top CoreOptions.ALGORITHM "org.eclipse.elk.fixed"
  let g := g.setNodeProp top CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH 20.0
  let g := g.setNodeProp top CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO 1.0
  let padding : ElkPadding := { top := 10.0, right := 10.0, bottom := 10.0, left := 10.0 }
  let g := g.setNodeProp top CoreOptions.PADDING padding
  let (g, child) := g.createNode (some top)
  let g := setTopdown g child .hierarchicalNode
  let g := g.setNodeProp child CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE true
  let g := g.setNodeProp child CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH 20.0
  let g := g.setNodeProp child CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO 1.0
  let g := g.modifyNode child fun n => { n with x := 0.0, y := 0.0 }
  let (_, g) ← ElkM.run (RecursiveGraphLayoutEngine.layout root ProgressMonitor.null) g
  checkFloat "child dimension width" (g.node top).width (20.0 + padding.left + padding.right) 1.0e-4
  checkFloat "child dimension height" (g.node top).height (20.0 + padding.top + padding.bottom) 1.0e-4

/-! ### Fixtures against the elk-rs oracle -/

/-- Fixture input names (`<name>.json` without `.expected.json`), sorted. -/
private def fixtureNames (dir : System.FilePath) : IO (Array String) := do
  let entries ← System.FilePath.readDir dir
  let names := entries.filterMap fun e =>
    if e.fileName.endsWith ".json" && !e.fileName.endsWith ".expected.json" then
      some (e.fileName.dropEnd ".json".length).toString
    else none
  return names.qsort (fun a b => a < b)

private def fixtureDir : System.FilePath := "tests/fixtures/topdownpacking"

/-- `topdownpacking.fixtures`: `Elk.Api.layoutJson` on every fixture reproduces the elk-rs output
byte-for-byte. -/
def fixtureTests : Suite := suite "topdownpacking.fixtures" do
  let names ← fixtureNames fixtureDir
  check "fixtures found" (names.size >= 8)
  for name in names do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    let expected ← IO.FS.readFile (fixtureDir / s!"{name}.expected.json")
    match ← Elk.Api.layoutJson input "{}" (lenient := false) (pretty := true) (sortKeys := true) with
    | .error e => report s!"{name}: layout" false e
    | .ok actual => checkJson s!"{name}: matches oracle" actual expected (tol := ELK_RS_FIXTURE_TOL)

def suites : Array Tests.Suite := #[metadataTests, packingTests, layoutTests, fixtureTests]

end Tests.TopdownPacking
