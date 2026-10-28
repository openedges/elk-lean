import Tests.Framework
import Tests.JsonCompare
import Elk.Api
import Elk.Alg.VertiFlex
/-!
# Tests for `org.eclipse.elk.alg.vertiflex`

Port of the elk-rs test `plugins/org.eclipse.elk.alg.vertiflex/tests/vertiflex_metadata_test.rs`
(`layout_strategy_defaults`, `layer_distance_defaults`, `consider_model_order_defaults`) plus the
metadata of the algorithm entry, unit tests of the outline helpers and the fixture suite
`vertiflex.fixtures` (`tests/fixtures/vertiflex/`).

Fixtures (all produced by elk-rs `model_parity_layout_runner` or, for `bend_*`, by an elk-rs
probe, see below) are checked byte-for-byte:

* `<name>.json` / `<name>.expected.json`: input graph and the laid-out graph. `bend_*` fixtures
  are laid out with `EdgeRoutingStrategy.BEND` set on the root node *programmatically*: elk-rs
  registers `elk.vertiflex.layoutStrategy` without an enum parser, so the option string in a JSON
  input is ignored (always `STRAIGHT`), in elk-rs and here. The expected files of the `bend_*`
  fixtures were produced by a small elk-rs program that imports the JSON, sets
  `VertiFlexOptions::LAYOUT_STRATEGY = Bend` on the root and runs `RecursiveGraphLayoutEngine`.
  `vf_strategy_ignored` is a JSON input that sets `"elk.vertiflex.layoutStrategy": "BEND"`: the
  oracle ignores it (straight edges, no bend points), so does the Lean port.
* `sp_*` fixtures: special tree shapes (hyperedge, existing multi-section edges, empty graph) and
  the error cases double edge / self loop (a node with two incoming edges).
* `<name>.json` / `<name>.expected.err` (`err_*`): the layout fails; the file holds the message of
  the elk-rs panic (`UnsupportedConfigurationException` text or `index out of bounds`).

Re-pinned fixtures (RJ1, ELK Java 0.12.0 as the reference): `vf_ports_labels` is an elk-lean output since RJ1 (Java's node micro layout; every changed value equals ELK Java's).

Agent OPT (Java option semantics): `elk.vertiflex.layoutStrategy` is parsed like in Java, so the
`bend_*` inputs now also carry `"elk.vertiflex.layoutStrategy": "BEND"` and `vf_strategy_ignored`
is laid out with bends; `err_two_children` / `err_deep_two_children` are laid out like ELK Java
(elk-rs panics). All of them are elk-lean outputs equal to ELK Java 0.12.0 at tolerance 0
(`tests/fixtures/opt_java_status.tsv`).
-/
namespace Tests.VertiFlex

open Tests Elk Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Data Elk.Json
open Elk.Alg.VertiFlex Elk.Alg.VertiFlex.Options Elk.Alg.VertiFlex.P2Relative

/-! ### `vertiflex_metadata_test.rs` and the algorithm entry -/

/-- The three Rust tests, the option metadata and the algorithm entry of `VertiFlexMetaDataProvider`. -/
def metadataTests : Suite := suite "vertiflex.metadata" do
  LayoutMetaDataService.ensureInitialized
  -- layout_strategy_defaults
  match ← LayoutMetaDataService.getOptionData VertiFlexOptions.LAYOUT_STRATEGY.id with
  | none => report "layout strategy option registered" false
  | some o =>
    check "layout strategy targets nodes" (o.targets.contains .nodes)
    check "layout strategy default STRAIGHT"
      (((o.defaultValue.bind PropCodec.dec : Option EdgeRoutingStrategy)) == some .straight)
    checkEq "layout strategy type" o.type LayoutOptionType.enum
    checkEq "layout strategy name" o.name "Edge layout strategy"
    checkEq "layout strategy group" o.group ""
    check "layout strategy visible" (o.visibility == .visible)
    -- Java registers the enum class (choices and parser); elk-rs had neither (agent OPT)
    checkEq "layout strategy choices (Java)" o.choices #["STRAIGHT", "BEND"]
    check "layout strategy parseable (Java)" o.canParseValue
    check "layout strategy value parsed"
      ((o.parseValue "BEND").bind PropCodec.dec == some EdgeRoutingStrategy.bend)
  -- layer_distance_defaults
  match ← LayoutMetaDataService.getOptionData VertiFlexOptions.LAYER_DISTANCE.id with
  | none => report "layer distance option registered" false
  | some o =>
    check "layer distance targets parents" (o.targets.contains .parents)
    check "layer distance default 50" (((o.defaultValue.bind PropCodec.dec : Option Float)) == some 50.0)
    checkEq "layer distance type" o.type LayoutOptionType.double
    checkEq "layer distance name" o.name "Layer distance"
  -- consider_model_order_defaults
  match ← LayoutMetaDataService.getOptionData VertiFlexOptions.CONSIDER_NODE_MODEL_ORDER.id with
  | none => report "consider model order option registered" false
  | some o =>
    check "consider model order default true" (((o.defaultValue.bind PropCodec.dec : Option Bool)) == some true)
    check "consider model order targets parents" (o.targets.contains .parents)
    checkEq "consider model order type" o.type LayoutOptionType.boolean
  match ← LayoutMetaDataService.getOptionData VertiFlexOptions.VERTICAL_CONSTRAINT.id with
  | none => report "vertical constraint option registered" false
  | some o =>
    check "vertical constraint targets nodes" (o.targets.contains .nodes)
    check "vertical constraint has no default" o.defaultValue.isNone
    checkEq "vertical constraint type" o.type LayoutOptionType.double
    checkEq "vertical constraint name" o.name "Fixed vertical position"
    check "vertical constraint parseable" (o.parseValue "120").isSome
  -- the algorithm entry
  match ← LayoutMetaDataService.getAlgorithmData VertiFlexOptions.ALGORITHM_ID with
  | none => report "algorithm registered" false
  | some a =>
    checkEq "algorithm name" a.name "ELK VertiFlex"
    checkEq "algorithm category" a.categoryId (some "org.eclipse.elk.tree")
    checkEq "algorithm bundle" a.definingBundleId (some "org.eclipse.elk.alg.vertiflex")
    check "algorithm supports MULTI_EDGES" (a.supportsFeature .multiEdges)
    check "algorithm supports EDGE_LABELS" (a.supportsFeature .edgeLabels)
    check "algorithm does not support PORTS" (!a.supportsFeature .ports)
    checkEq "algorithm known options" a.knownOptionIds #[
      CoreOptions.SPACING_NODE_NODE.id, CoreOptions.PADDING.id, CoreOptions.INTERACTIVE.id,
      CoreOptions.PORT_CONSTRAINTS.id, CoreOptions.EDGE_LABELS_INLINE.id,
      CoreOptions.OMIT_NODE_MICRO_LAYOUT.id, CoreOptions.MARGINS.id,
      VertiFlexOptions.VERTICAL_CONSTRAINT.id, VertiFlexOptions.LAYOUT_STRATEGY.id,
      VertiFlexOptions.LAYER_DISTANCE.id, VertiFlexOptions.CONSIDER_NODE_MODEL_ORDER.id]
    check "algorithm default spacing 20" (a.defaultValue CoreOptions.SPACING_NODE_NODE == some 20.0)
    check "algorithm default padding 5"
      (a.defaultValue CoreOptions.PADDING == some (⟨5.0, 5.0, 5.0, 5.0⟩ : ElkPadding))
    check "algorithm default edge labels inline false" (a.defaultValue CoreOptions.EDGE_LABELS_INLINE == some false)
    check "algorithm: interactive has no default" (a.defaultValue CoreOptions.INTERACTIVE).isNone
  let service ← LayoutMetaDataService.getInstance
  match service.categoryData? "org.eclipse.elk.tree" with
  | none => report "tree category" false
  | some c => check "tree category lists vertiflex" (c.layouters.contains VertiFlexOptions.ALGORITHM_ID)
  check "provider registered" (← LayoutProvider.isRegistered VertiFlexOptions.ALGORITHM_ID)
  match ← LayoutProvider.create VertiFlexOptions.ALGORITHM_ID with
  | some p => check "registered provider has no predicted size" p.predictedGraphSize.isNone
  | none => report "provider created" false
  -- the registry the provider contributes: 1 algorithm, 4 options, 11 option supports
  let r := VertiFlexMetaDataProvider.metaDataProvider.apply {}
  checkEq "provider algorithms" r.algorithms.size 1
  checkEq "provider options" r.options.size 4
  checkEq "provider option supports" r.optionSupport.size 11
  checkEq "provider categories" r.categories.size 0

/-! ### Unit tests of the helper types -/

/-- A list of outline nodes from `(relative_x, absolute_y)` pairs. -/
private def mkOutline (pts : Array (Float × Float)) : OutlineNode :=
  let rec go (i : Nat) (fuel : Nat) : Option OutlineNode :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if i < pts.size then some (OutlineNode.new pts[i]!.1 pts[i]!.2 (go (i + 1) fuel)) else none
  (go 0 pts.size).getD (OutlineNode.new 0.0 0.0)

/-- The `(relative_x, absolute_y)` pairs of an outline. -/
private def outlinePoints (o : OutlineNode) : Array (Float × Float) := Id.run do
  let mut pts := #[(o.relativeX, o.absoluteY)]
  let mut cur := o
  while true do
    match cur.next with
    | some n =>
      pts := pts.push (n.relativeX, n.absoluteY)
      cur := n
    | none => break
  return pts

/-- `OutlineNode`, `NodeComparator`, `outline_distance`. -/
def unitTests : Suite := suite "vertiflex.units" do
  let o := mkOutline #[(1.0, 2.0), (3.0, 4.0), (5.0, 6.0), (7.0, 8.0)]
  check "isLast" ((((o.next).bind (·.next)).bind (·.next)).map (·.isLast) == some true)
  checkEqR "outline points" (outlinePoints o) #[(1.0, 2.0), (3.0, 4.0), (5.0, 6.0), (7.0, 8.0)]
  let tail := o.appendToTail (OutlineNode.new 9.0 10.0)
  checkEqR "appendToTail" (outlinePoints tail) #[(1.0, 2.0), (3.0, 4.0), (5.0, 6.0), (7.0, 8.0), (9.0, 10.0)]
  let tail2 := o.setThirdNext (mkOutline #[(0.5, 0.5), (0.25, 0.75)])
  checkEqR "setThirdNext replaces the successor of the fourth node" (outlinePoints tail2)
    #[(1.0, 2.0), (3.0, 4.0), (5.0, 6.0), (7.0, 8.0), (0.5, 0.5), (0.25, 0.75)]
  let short := mkOutline #[(1.0, 2.0), (3.0, 4.0)]
  checkEqR "setThirdNext leaves short outlines unchanged" (outlinePoints (short.setThirdNext (OutlineNode.new 9.0 9.0)))
    #[(1.0, 2.0), (3.0, 4.0)]
  let (absX, lastY) := o.absXAndLastY 10.0
  checkFloat "absXAndLastY x" absX 26.0
  checkFloat "absXAndLastY y" lastY 8.0
  -- outline_distance of two identical boxes next to each other: right outline of the left box
  -- against the left outline of the right box; no horizontal gap -> distance of the half widths
  let right := mkOutline #[(25.0, 0.0), (20.0, 0.0), (0.0, 20.0), (-20.0, 30.0)]
  let left := mkOutline #[(-25.0, 0.0), (-20.0, 0.0), (0.0, 20.0), (20.0, 30.0)]
  let d := RelativeXPlacer.outlineDistance right left
  check "outlineDistance is finite and positive" (d > 0.0 && d < 1000.0)
  -- NodeComparator: y ascending (descending when inverted), then model order
  let k (id : Nat) (y : Float) (order : Int) : NodeKey := { node := ⟨id⟩, y, modelOrder := order }
  check "compare by y" (NodeComparator.compare false (k 0 1.0 5) (k 1 2.0 0) == .lt)
  check "compare inverted by y" (NodeComparator.compare true (k 0 1.0 5) (k 1 2.0 0) == .gt)
  check "tie broken by model order" (NodeComparator.compare false (k 0 1.0 5) (k 1 1.0 6) == .lt)
  check "inverted tie keeps model order ascending" (NodeComparator.compare true (k 0 1.0 5) (k 1 1.0 6) == .lt)
  check "NaN y compares equal, then model order"
    (NodeComparator.compare false (k 0 (0.0 / 0.0) 7) (k 1 1.0 6) == .gt)

/-! ### Direct layouts -/

private def layoutDirect (g : ElkGraph) (root : NodeId) : IO (Except String ElkGraph) := do
  let monitor ← ProgressMonitor.basic
  try
    let (_, g) ← ElkM.run (VertiFlexLayoutProvider.layout root monitor) g
    return .ok g
  catch e => return .error (toString e)

private def addChild (g : ElkGraph) (root : NodeId) (w h : Float) : ElkGraph × NodeId :=
  let (g, n) := g.createNode (some root)
  (g.modifyNode n fun nd => { nd with width := w, height := h }, n)

/-- Direct runs of the provider on graphs built with the `ElkGraph` API. -/
def providerTests : Suite := suite "vertiflex.provider" do
  LayoutMetaDataService.ensureInitialized
  -- a parent above two children needs `considerNodeModelOrder = false` (elk-rs panics otherwise)
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root VertiFlexOptions.CONSIDER_NODE_MODEL_ORDER false
  let (g, a) := addChild g root 30.0 20.0
  let (g, b) := addChild g root 40.0 20.0
  let (g, c) := addChild g root 20.0 30.0
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node a) (.node b)
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node a) (.node c)
  match ← layoutDirect g root with
  | .error e => report "straight layout" false e
  | .ok g =>
    -- y of the children: 0 + layer distance 50 + height 20 + max(margin 0, node spacing 20) = 90
    checkFloat "root y" (g.node a).y 0.0
    checkFloat "child y" (g.node b).y 90.0
    checkFloat "other child y" (g.node c).y 90.0
    -- positions reported by the elk-rs oracle for this graph (fixture `vf_two_nomodel`)
    checkFloat "root x" (g.node a).x 25.0
    checkFloat "child x" (g.node b).x 0.0
    checkFloat "other child x" (g.node c).x 60.0
    check "leftmost node at x = 0" (fmin (g.node a).x (fmin (g.node b).x (g.node c).x) == 0.0)
    checkFloat "graph width" (g.node root).width 92.0
    checkFloat "graph height" (g.node root).height 132.0
  -- bend routing: set programmatically
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root VertiFlexOptions.LAYOUT_STRATEGY EdgeRoutingStrategy.bend
  let (g, a) := addChild g root 30.0 20.0
  let (g, b) := addChild g root 40.0 20.0
  let (g, c) := addChild g root 20.0 30.0
  let (g, e1) := ElkGraphUtil.createSimpleEdge g (.node a) (.node b)
  let (g, e2) := ElkGraphUtil.createSimpleEdge g (.node a) (.node c)
  match ← layoutDirect g root with
  | .error e => report "bend layout" false e
  | .ok g =>
    checkEq "bend: edges have one section each" ((g.edge e1).sections.size, (g.edge e2).sections.size) (1, 1)
    checkFloat "bend: start y is the bottom of the parent" (g.edgeSection (g.edge e1).sections[0]!).startY 20.0
    checkFloat "bend: end y is the top of the child" (g.edgeSection (g.edge e1).sections[0]!).endY (g.node b).y
  -- error paths
  let (g, root) := ElkGraphUtil.createGraph
  let (g, a) := addChild g root 30.0 20.0
  let (g, b) := addChild g root 40.0 20.0
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node a) (.node b)
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node b) (.node a)
  match ← layoutDirect g root with
  | .error e => checkEq "cycle: not a tree" e "org.eclipse.elk.core.UnsupportedConfigurationException: The given graph is not a tree!"
  | .ok _ => report "cycle: not a tree" false "expected an exception"
  -- exactly two children with considerNodeModelOrder (default true): elk-rs panics (index overflow),
  -- Java cuts the doubled split to the number of children and lays the tree out (agent OPT)
  let (g, root) := ElkGraphUtil.createGraph
  let (g, a) := addChild g root 30.0 20.0
  let (g, b) := addChild g root 40.0 20.0
  let (g, c) := addChild g root 40.0 20.0
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node a) (.node b)
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node a) (.node c)
  match ← layoutDirect g root with
  | .error e => report "two children: laid out like Java" false e
  | .ok _ => report "two children: laid out like Java" true

/-! ### Fixtures against the elk-rs oracle -/

/-- Fixture input names (`<name>.json` without `.expected.json`), sorted. -/
private def fixtureNames (dir : System.FilePath) : IO (Array String) := do
  let entries ← System.FilePath.readDir dir
  let names := entries.filterMap fun e =>
    if e.fileName.endsWith ".json" && !e.fileName.endsWith ".expected.json" then
      some (e.fileName.dropEnd ".json".length).toString
    else none
  return stableSort names (fun a b => compare a b)

private def fixtureDir : System.FilePath := "tests/fixtures/vertiflex"

/-- `Elk.Api.layoutJson` (pretty, sorted keys) with `LAYOUT_STRATEGY = BEND` set on the imported
root before the layout. -/
private def layoutJsonBend (graphJson : String) : IO (Except String String) := do
  match Elk.Json.parse graphJson false with
  | .error e => return .error s!"Failed to parse graph JSON: {e}"
  | .ok input =>
    Elk.Api.ensureInitialized
    let result ← Elk.Api.catchLayout do
      let defaults ← match ← GlobalOptions.parse "{}" with
        | .ok g => pure g
        | .error e => throw (IO.userError e)
      let ((root, st), g) ← (ImportM.run (JsonImporter.transform input) { defaults := some defaults }).run {}
      let g := g.setNodeProp root VertiFlexOptions.LAYOUT_STRATEGY EdgeRoutingStrategy.bend
      let ((), g) ← (RecursiveGraphLayoutEngine.layout root (ProgressMonitor.null)).run g
      let materialized ← (st.defaults.getD defaults).materialize st.model
      let st := { st with model := materialized }
      let (((), st), _) ← (ImportM.run JsonImporter.transferLayout st).run g
      return st.model
    match result with
    | .error e => return .error e
    | .ok v => return .ok (v.renderPretty true)

/-- Optional debugging aid: `ELK_VERTIFLEX_ACTUAL_DIR` receives the actual outputs. -/
private def dumpActual (name actual : String) : IO Unit := do
  if let some dir ← IO.getEnv "ELK_VERTIFLEX_ACTUAL_DIR" then
    IO.FS.createDirAll dir
    IO.FS.writeFile (System.FilePath.mk dir / s!"{name}.json") actual

/-- `vertiflex.fixtures`: every fixture reproduces the elk-rs output byte-for-byte (or fails with
the same message). -/
def fixtureTests : Suite := suite "vertiflex.fixtures" do
  let names ← fixtureNames fixtureDir
  check "fixtures found" (names.size >= 40)
  let mut errors := 0
  let mut bends := 0
  for name in names do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    let isBend := name.startsWith "bend_"
    let result ← if isBend then layoutJsonBend input
      else Elk.Api.layoutJson input "{}" (lenient := false) (pretty := true) (sortKeys := true)
    if isBend then bends := bends + 1
    let errPath := fixtureDir / s!"{name}.expected.err"
    if ← errPath.pathExists then
      errors := errors + 1
      let message := (← IO.FS.readFile errPath).trimAscii.toString
      match result with
      | .error e => checkEq s!"{name}: error message" e s!"org.eclipse.elk.core.UnsupportedConfigurationException: {message}"
      | .ok actual =>
        dumpActual name actual
        report s!"{name}: expected the error '{message}'" false
    else
      let expected ← IO.FS.readFile (fixtureDir / s!"{name}.expected.json")
      match result with
      | .error e => report s!"{name}: layout" false e
      | .ok actual =>
        dumpActual name actual
        checkJson s!"{name}: matches oracle" actual expected (tol := ELK_RS_FIXTURE_TOL)
  check "error fixtures found" (errors >= 5)
  check "bend fixtures found" (bends >= 10)

def suites : Array Tests.Suite := #[metadataTests, unitTests, providerTests, fixtureTests]

end Tests.VertiFlex
