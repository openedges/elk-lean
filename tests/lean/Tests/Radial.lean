import Tests.Framework
import Tests.JsonCompare
import Elk.Api
import Elk.Alg.Radial
/-!
# Tests for `org.eclipse.elk.alg.radial`

Ports of the elk-rs tests `plugins/org.eclipse.elk.alg.radial/tests/all`
(`radial_metadata_test.rs`: `radial_algorithm_registered`, `wedge_criteria_metadata`,
`order_id_targets_nodes`; `center_on_root_test.rs`: `test_simple_centering`,
`test_larger_graph_centering`), unit tests of the helpers, a differential test of the unboxed
overlap removal loop (`radial.overlapRemoval.differential`: `expandLoop` and `overlapBoundsGrouped`
against the reference `overlapLayerSoa`/`contractLayerSoa` loop on random layers), and two fixture
suites:

* `radial.fixtures` (`tests/fixtures/radial/<name>.json` against `<name>.expected.json`): produced
  by the stock elk-rs oracle (`model_parity_layout_runner`, commit eb586b6d). The stock oracle
  registers the four enum options of the radial algorithm (`compactor`, `sorter`,
  `wedgeCriteria`, `optimizationCriteria`) without a value parser, so these option strings in the
  JSON are ignored by the oracle, and by the port; the expected files document that;
* `radial.fixtures.enum` (`tests/fixtures/radial/enum/<name>.json`): the same kind of models with
  the enum options effective. The expected files were produced by an elk-rs oracle build whose
  radial metadata provider additionally registers the enum choices and parsers (the only change
  to elk-rs; the algorithm code is the stock one). The suite installs
  `RadialMetaDataProvider.enumParserProvider` for the duration of the run.

Re-pinned fixtures (RJ1, ELK Java 0.12.0 as the reference): `rad_ports` (and `enum/rad_ports`) hold ELK Java's exception text (`<name>.error`) since RJ1.
-/
namespace Tests.Radial

open Tests Elk Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Util Elk.Core.Options
open Elk.Core.Data
open Elk.Alg.Radial Elk.Alg.Radial.Options Elk.Alg.Radial.Intermediate
open Elk.Alg.Radial.Intermediate.Compaction Elk.Alg.Radial.Sorting

/-! ### `radial_metadata_test.rs` -/

/-- `radial_algorithm_registered`, `wedge_criteria_metadata`, `order_id_targets_nodes` and the
rest of the provider output. -/
def metadataTests : Suite := suite "radial.metadata" do
  LayoutMetaDataService.ensureInitialized
  match ← LayoutMetaDataService.getAlgorithmData RadialOptions.ALGORITHM_ID with
  | none => report "radial algorithm registered" false
  | some a =>
    checkEq "algorithm name" a.name "ELK Radial"
    checkEq "algorithm category" a.categoryId (some "org.eclipse.elk.radial")
    checkEq "algorithm bundle" a.definingBundleId (some "org.eclipse.elk.alg.radial")
    checkEq "algorithm preview image" a.previewImagePath (some "images/radial_layout.png")
    check "algorithm description" (a.description.startsWith "A radial layout provider which is based on the algorithm of Peter Eades")
    checkEq "algorithm known options" a.knownOptionIds #[
      CoreOptions.POSITION.id, CoreOptions.SPACING_NODE_NODE.id, CoreOptions.NODE_SIZE_CONSTRAINTS.id,
      CoreOptions.NODE_SIZE_MINIMUM.id, CoreOptions.NODE_SIZE_OPTIONS.id,
      CoreOptions.NODE_LABELS_PLACEMENT.id, CoreOptions.OMIT_NODE_MICRO_LAYOUT.id,
      CoreOptions.PORT_LABELS_PLACEMENT.id,
      RadialOptions.COMPACTION_STEP_SIZE.id, RadialOptions.COMPACTOR.id, RadialOptions.ROTATE.id,
      RadialOptions.ROTATION_TARGET_ANGLE.id, RadialOptions.ROTATION_COMPUTE_ADDITIONAL_WEDGE_SPACE.id,
      RadialOptions.ROTATION_OUTGOING_EDGE_ANGLES.id, RadialOptions.OPTIMIZATION_CRITERIA.id,
      RadialOptions.ORDER_ID.id, RadialOptions.RADIUS.id, RadialOptions.SORTER.id,
      RadialOptions.WEDGE_CRITERIA.id, RadialOptions.CENTER_ON_ROOT.id]
  match ← LayoutMetaDataService.getCategoryData "org.eclipse.elk.radial" with
  | none => report "radial category registered" false
  | some c =>
    checkEq "radial category name" c.name "Radial"
    check "radial algorithm is in the radial category" (c.layouters.contains RadialOptions.ALGORITHM_ID)
  check "radial layout provider registered" (← LayoutProvider.isRegistered RadialOptions.ALGORITHM_ID)
  -- wedge_criteria_metadata
  match ← LayoutMetaDataService.getOptionData RadialOptions.WEDGE_CRITERIA.id with
  | none => report "wedge criteria option registered" false
  | some o =>
    check "wedge criteria targets parents" (o.targets.contains .parents)
    checkEq "wedge criteria visibility" o.visibility LayoutOptionVisibility.visible
    check "wedge criteria default NODE_SIZE"
      (((o.defaultValue.bind PropCodec.dec : Option AnnulusWedgeCriteria)) == some .nodeSize)
    checkEq "wedge criteria name" o.name "Annulus Wedge Criteria"
    checkEq "wedge criteria type" o.type LayoutOptionType.enum
    -- Java registers the enum class (choices and parser); elk-rs had neither (agent OPT)
    checkEq "wedge criteria choices (Java)" o.choices #["LEAF_NUMBER", "NODE_SIZE"]
    check "wedge criteria parser (Java)" o.parser.isSome
    check "wedge criteria value strings are parsed"
      ((o.parseValue "LEAF_NUMBER").bind PropCodec.dec == some AnnulusWedgeCriteria.leafNumber)
  -- order_id_targets_nodes
  match ← LayoutMetaDataService.getOptionData RadialOptions.ORDER_ID.id with
  | none => report "order id option registered" false
  | some o =>
    check "order id targets nodes" (o.targets.contains .nodes)
    check "order id only targets nodes" (o.targets == EnumSet.of #[.nodes])
    checkEq "order id type" o.type LayoutOptionType.int
    check "order id default 0" (o.defaultValue.bind PropCodec.dec == some (0 : Int))
  -- the remaining options of `register_options`
  let opt (id : String) : TestM LayoutOptionData := do
    match ← LayoutMetaDataService.getOptionData id with
    | some d => pure d
    | none => report s!"option {id} registered" false; pure { id }
  let step ← opt RadialOptions.COMPACTION_STEP_SIZE.id
  checkEq "step size type" step.type LayoutOptionType.int
  check "step size default 1" (step.defaultValue.bind PropCodec.dec == some (1 : Int))
  check "step size lower bound 0 (inclusive)" (match step.lowerBound with
    | some b => !b.isExclusive && (PropCodec.dec b.value : Option Int) == some 0
    | none => false)
  let radius ← opt RadialOptions.RADIUS.id
  checkEq "radius type" radius.type LayoutOptionType.double
  check "radius default 0" (radius.defaultValue.bind PropCodec.dec == some (0.0 : Float))
  let rotAngle ← opt RadialOptions.ROTATION_TARGET_ANGLE.id
  checkEq "target angle group" rotAngle.group "rotation"
  checkEq "target angle visibility" rotAngle.visibility LayoutOptionVisibility.visible
  let rotWedge ← opt RadialOptions.ROTATION_COMPUTE_ADDITIONAL_WEDGE_SPACE.id
  checkEq "additional wedge space group" rotWedge.group "rotation"
  checkEq "additional wedge space visibility" rotWedge.visibility LayoutOptionVisibility.advanced
  let rotOut ← opt RadialOptions.ROTATION_OUTGOING_EDGE_ANGLES.id
  checkEq "outgoing edge angles visibility" rotOut.visibility LayoutOptionVisibility.advanced
  let center ← opt RadialOptions.CENTER_ON_ROOT.id
  checkEq "center on root type" center.type LayoutOptionType.boolean
  check "center on root default false" (center.defaultValue.bind PropCodec.dec == some false)
  let compactor ← opt RadialOptions.COMPACTOR.id
  check "compactor default NONE" (((compactor.defaultValue.bind PropCodec.dec : Option CompactionStrategy)) == some .none)
  let sorter ← opt RadialOptions.SORTER.id
  check "sorter default NONE" (((sorter.defaultValue.bind PropCodec.dec : Option SortingStrategy)) == some .none)
  let optim ← opt RadialOptions.OPTIMIZATION_CRITERIA.id
  check "optimization criteria default NONE"
    (((optim.defaultValue.bind PropCodec.dec : Option RadialTranslationStrategy)) == some .none)
  -- registration order
  let s ← LayoutMetaDataService.getInstance
  let idx (id : String) : Nat := (s.optionOrder.findIdx? (· == id)).getD 0
  let ids : Array String := #[RadialOptions.CENTER_ON_ROOT.id, RadialOptions.ORDER_ID.id,
      RadialOptions.RADIUS.id, RadialOptions.ROTATE.id, RadialOptions.ROTATION_TARGET_ANGLE.id, RadialOptions.ROTATION_COMPUTE_ADDITIONAL_WEDGE_SPACE.id,
      RadialOptions.ROTATION_OUTGOING_EDGE_ANGLES.id, RadialOptions.COMPACTOR.id,
      RadialOptions.COMPACTION_STEP_SIZE.id, RadialOptions.SORTER.id, RadialOptions.WEDGE_CRITERIA.id,
      RadialOptions.OPTIMIZATION_CRITERIA.id]
  check "twelve radial options registered in the Rust order"
    (ids.size == 12 && (List.range 11).all fun i => idx ids[i]! + 1 == idx ids[i + 1]!)
  -- the Java-like variant replaces the four enum options in place
  let before ← LayoutMetaDataService.getInstance
  LayoutMetaDataService.registerLayoutMetaDataProvider RadialMetaDataProvider.enumParserProvider
  let after ← LayoutMetaDataService.getInstance
  checkEq "enumParserProvider keeps the option count" after.optionOrder.size before.optionOrder.size
  match after.optionData? RadialOptions.COMPACTOR.id with
  | some o =>
    checkEq "enum variant choices" o.choices #["NONE", "RADIAL_COMPACTION", "WEDGE_COMPACTION"]
    check "enum variant parses WEDGE_COMPACTION"
      ((o.parseValue "WEDGE_COMPACTION").bind PropCodec.dec == some CompactionStrategy.wedgeCompaction)
  | none => report "enum variant compactor registered" false
  LayoutMetaDataService.instanceRef.set before

/-! ### Graph construction helpers -/

/-- A tree given by the parent index of every node `i + 1` (node `0` is the root); all nodes
`size x size` square, in a fresh graph (`parent` is the layout graph). -/
private def buildTree (parents : Array Nat) (size : Float := 30.0) : ElkGraph × NodeId × Array NodeId := Id.run do
  let (g, parent) := ElkGraphUtil.createGraph
  let mut g := g
  let mut nodes : Array NodeId := #[]
  for _ in [0:parents.size + 1] do
    let (g', n) := g.createNode (some parent)
    g := g'.modifyNode n fun x => { x with width := size, height := size }
    nodes := nodes.push n
  for i in [0:parents.size] do
    let (g', _) := ElkGraphUtil.createSimpleEdge g (.node nodes[parents[i]!]!) (.node nodes[i + 1]!)
    g := g'
  return (g, parent, nodes)

private def layoutDirect (g : ElkGraph) (parent : NodeId) : IO ElkGraph := do
  let monitor ← ProgressMonitor.basic
  let (_, g) ← ElkM.run (RadialLayoutProvider.layout parent monitor) g
  return g

/-! ### `center_on_root_test.rs` -/

private def checkCentered (name : String) (g : ElkGraph) (parent root : NodeId) : TestM Unit := do
  let margins := (g.node root).props.getD CoreOptions.MARGINS {}
  let p := g.node parent
  let r := g.node root
  report s!"{name}: horizontally centered" (((p.width / 2.0) - (r.x + margins.left + r.width / 2.0)).abs < 0.1)
  report s!"{name}: vertically centered" (((p.height / 2.0) - (r.y + margins.top + r.height / 2.0)).abs < 0.1)

/-- `test_simple_centering`, `test_larger_graph_centering`. -/
def centerOnRootTests : Suite := suite "radial.centerOnRoot" do
  LayoutMetaDataService.ensureInitialized
  let (g, parent, nodes) := buildTree #[0, 0, 0]
  let g := g.setNodeProp parent CoreOptions.ALGORITHM RadialOptions.ALGORITHM_ID
  let g := g.setNodeProp parent RadialOptions.CENTER_ON_ROOT true
  let g ← layoutDirect g parent
  checkCentered "simple" g parent nodes[0]!
  let (g, parent, nodes) := buildTree #[0, 0, 0, 1, 1, 1]
  let g := g.setNodeProp parent RadialOptions.CENTER_ON_ROOT true
  let g ← layoutDirect g parent
  checkCentered "larger" g parent nodes[0]!
  -- without centerOnRoot the root is not in the middle of this graph
  let (g, parent, nodes) := buildTree #[0, 0, 0, 1, 1, 1]
  let g ← layoutDirect g parent
  let r := g.node nodes[0]!
  check "larger graph without centering is off center"
    (((g.node parent).width / 2.0 - (r.x + r.width / 2.0)).abs > 0.1)

/-! ### Helpers -/

/-- Runs a `RadialM` computation on a graph. -/
private def runRadial {α : Type} (x : RadialM α) (g : ElkGraph) : IO (α × ElkGraph) :=
  ElkM.run (StateRefT'.run' x {}) g

private def idsOf (a : Array NodeId) : Array Nat := a.map (·.idx)

/-- `RadialUtil` and `InternalProperties`. -/
def utilTests : Suite := suite "radial.util" do
  -- tree: 0 -> {1, 2, 3}; 1 -> {4, 5}; 2 -> {6}; plus a multi edge 0 -> 1
  let (g, parent, n) := buildTree #[0, 0, 0, 1, 1, 2]
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node n[0]!) (.node n[1]!)
  let (succ, _) ← runRadial (RadialUtil.getSuccessors n[0]!) g
  checkEqR "successors keep multi edges" (idsOf succ) #[n[1]!.idx, n[2]!.idx, n[3]!.idx, n[1]!.idx]
  let (set, _) ← runRadial (RadialUtil.getSuccessorSet n[0]!) g
  checkEqR "successor set removes duplicates" (idsOf set) #[n[1]!.idx, n[2]!.idx, n[3]!.idx]
  let (root, _) ← runRadial (RadialUtil.findRoot parent) g
  check "find root" (root == some n[0]!)
  let (leaves, _) ← runRadial (RadialUtil.getNumberOfLeaves n[0]!) (g)
  -- the duplicate edge counts the subtree of node 1 (two leaves) twice: 2 + 1 + 1 + 2
  checkFloat "number of leaves" leaves 6.0
  let (parentOf5, _) ← runRadial (RadialUtil.getTreeParent n[5]!) g
  check "tree parent" (parentOf5 == some n[1]!)
  let (rootOf5, _) ← runRadial (RadialUtil.findRootOfNode n[5]!) g
  check "find root of node" (rootOf5 == n[0]!)
  let (next, _) ← runRadial (RadialUtil.getNextLevelNodes #[n[1]!, n[2]!]) g
  checkEqR "next level nodes" (idsOf next) #[n[4]!.idx, n[5]!.idx, n[6]!.idx]
  let (nextSet, _) ← runRadial (RadialUtil.getNextLevelNodeSet #[n[0]!, n[1]!]) g
  checkEqR "next level node set" (idsOf nextSet) #[n[1]!.idx, n[2]!.idx, n[3]!.idx, n[4]!.idx, n[5]!.idx]
  let (last, _) ← runRadial (RadialUtil.getLastLevelNodes #[n[4]!, n[6]!]) g
  checkEqR "last level nodes" (idsOf last) #[n[1]!.idx, n[2]!.idx]
  -- largest node diagonal, centering
  let g := g.modifyNode n[3]! fun x => { x with width := 30.0, height := 40.0 }
  let (largest, _) ← runRadial (RadialUtil.findLargestNodeInGraph parent) g
  checkFloat "largest node diagonal" largest 50.0
  let (_, g2) ← runRadial (RadialUtil.centerNodesOnRadi n[3]! 100.0 50.0) g
  check "center nodes on radi" ((g2.node n[3]!).x == 85.0 && (g2.node n[3]!).y == 30.0)
  let (_, g3) ← runRadial (RadialUtil.shiftClosestEdgeToRadi n[3]! (-10.0) (-5.0)) g
  check "shift closest edge (x < 0, y < 0)" ((g3.node n[3]!).x == -40.0 && (g3.node n[3]!).y == -5.0)
  let (_, g4) ← runRadial (RadialUtil.shiftClosestEdgeToRadi n[3]! 10.0 5.0) g
  check "shift closest edge (x >= 0, y >= 0)" ((g4.node n[3]!).x == 10.0 && (g4.node n[3]!).y == 45.0)
  let (_, g5) ← runRadial (RadialUtil.shiftClosestEdgeToRadi n[3]! 0.0 0.0) g
  check "shift closest edge (origin)" ((g5.node n[3]!).x == -15.0 && (g5.node n[3]!).y == -20.0)
  -- the root side table
  let (rootAfter, _) ← runRadial (do
      InternalProperties.setRootNode parent n[2]!
      RadialUtil.rootFromGraph parent) g
  check "root_from_graph uses the ROOT_NODE side table" (rootAfter == some n[2]!)
  let (rootStale, _) ← runRadial (do
      InternalProperties.setRootNode parent ⟨9999⟩
      RadialUtil.rootFromGraph parent) g
  check "root_from_graph falls back to find_root for a stale root" (rootStale == some n[0]!)
  -- edges leaving a port are not tree edges
  let (g, parent) := ElkGraphUtil.createGraph
  let (g, a) := g.createNode (some parent)
  let (g, b) := g.createNode (some parent)
  let (g, p) := g.createPort (some a)
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.port p) (.node b)
  let (succ, _) ← runRadial (RadialUtil.getSuccessors a) g
  check "edges leaving a port are skipped" succ.isEmpty
  let (root, _) ← runRadial (RadialUtil.findRoot parent) g
  check "root is the first node without incoming edges" (root == some a)

/-- `AbstractRadiusExtensionCompaction` helpers and the polar comparison. -/
def compactionHelperTests : Suite := suite "radial.compactionHelpers" do
  let fa (a : Array Float) : FloatArray := ⟨a⟩
  -- two overlapping boxes and two separate ones
  check "overlap_layer_soa: overlapping neighbours"
    (AbstractRadiusExtensionCompaction.overlapLayerSoa (fa #[0.0, 10.0]) (fa #[0.0, 5.0]) (fa #[20.0, 20.0]) (fa #[20.0, 20.0]) 0.0)
  -- Java's corner cases are strict on both axes: the same top (or left) coordinate never overlaps
  check "overlap_layer_soa: equal top coordinates do not overlap (Java)"
    (!AbstractRadiusExtensionCompaction.overlapLayerSoa (fa #[0.0, 10.0]) (fa #[0.0, 0.0]) (fa #[20.0, 20.0]) (fa #[20.0, 20.0]) 0.0)
  check "overlap_layer_soa: separate boxes"
    (!AbstractRadiusExtensionCompaction.overlapLayerSoa (fa #[0.0, 50.0]) (fa #[0.0, 0.0]) (fa #[20.0, 20.0]) (fa #[20.0, 20.0]) 0.0)
  check "overlap_layer_soa: spacing makes boxes overlap"
    (AbstractRadiusExtensionCompaction.overlapLayerSoa (fa #[0.0, 25.0]) (fa #[0.0, 3.0]) (fa #[20.0, 20.0]) (fa #[20.0, 20.0]) 10.0)
  check "overlap_layer_soa: a single node never overlaps"
    (!AbstractRadiusExtensionCompaction.overlapLayerSoa (fa #[0.0]) (fa #[0.0]) (fa #[20.0]) (fa #[20.0]) 5.0)
  -- expanding a node by a step of 2 along the line from the origin
  let (xs, ys, changed) :=
    AbstractRadiusExtensionCompaction.contractLayerSoa 0.0 0.0 (fa #[10.0]) (fa #[0.0]) (fa #[20.0]) (fa #[20.0]) 2.0 false
  checkFloat "contract_layer_soa expanding x" (xs.get! 0) (20.0 + 40.0 / Float.sqrt 500.0 - 10.0)
  checkFloat "contract_layer_soa expanding y" (ys.get! 0) (10.0 + 20.0 / Float.sqrt 500.0 - 10.0)
  check "contract_layer_soa reports the change" changed
  let (xs, ys, _) :=
    AbstractRadiusExtensionCompaction.contractLayerSoa 0.0 0.0 (fa #[10.0]) (fa #[0.0]) (fa #[20.0]) (fa #[20.0]) 2.0 true
  checkFloat "contract_layer_soa contracting x" (xs.get! 0) (20.0 - 40.0 / Float.sqrt 500.0 - 10.0)
  checkFloat "contract_layer_soa contracting y" (ys.get! 0) (10.0 - 20.0 / Float.sqrt 500.0 - 10.0)
  -- zero step: the layer stays (modulo rounding), like the derived Default of elk-rs
  let (xs, _, changed) :=
    AbstractRadiusExtensionCompaction.contractLayerSoa 0.0 0.0 (fa #[10.0]) (fa #[0.0]) (fa #[20.0]) (fa #[20.0]) 0.0 false
  checkFloat "contract_layer_soa with step 0 keeps the layer" (xs.get! 0) 10.0
  check "contract_layer_soa with step 0 reports no change" (!changed)
  check "default compaction step is Java's 1" (({} : AbstractRadiusExtensionCompaction).compactionStep == 1)
  -- polar comparison uses the POSITION property
  let (g, parent) := ElkGraphUtil.createGraph
  let (g, a) := g.createNode (some parent)
  let (g, b) := g.createNode (some parent)
  let g := g.setNodeProp a CoreOptions.POSITION ⟨1.0, 0.0⟩
  let g := g.setNodeProp b CoreOptions.POSITION ⟨0.0, 1.0⟩
  let (o, _) ← runRadial (RadialUtil.comparePolar a b 0.0 0.0) g
  check "compare_polar a < b" (o == .lt)
  let (o, _) ← runRadial (RadialUtil.comparePolar b a 0.0 0.0) g
  check "compare_polar b > a" (o == .gt)
  let (o, _) ← runRadial (RadialUtil.comparePolar a a 0.0 0.0) g
  check "compare_polar a == a" (o == .eq)

/-- Next state of the 64-bit LCG of the differential tests. -/
private def lcgNext (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- A float in `[lo, hi)` and the next state. -/
private def lcgFloat (s : UInt64) (lo hi : Float) : Float × UInt64 :=
  let s := lcgNext s
  (lo + (hi - lo) * (s >>> 11).toFloat / (2 ^ 53 : Nat).toFloat, s)

/-- The overlap removal loop of a layer before the unboxed rewrite (`RadiusExtensionOverlapRemoval.extend`
up to agent PR): `while overlapLayerSoa: contractLayerSoa(…, step, false)` with the pass guard and
the no-change stop. -/
private def referenceExpand (rootCx rootCy step spacing : Float) (maxIterations : Nat)
    (xs ys ws hs : FloatArray) : FloatArray × FloatArray := Id.run do
  let mut xs := xs
  let mut ys := ys
  let mut iterations := 0
  while AbstractRadiusExtensionCompaction.overlapLayerSoa xs ys ws hs spacing do
    if iterations >= maxIterations then break
    let (nx, ny, changed) :=
      AbstractRadiusExtensionCompaction.contractLayerSoa rootCx rootCy xs ys ws hs step false
    xs := nx
    ys := ny
    iterations := iterations + 1
    if !changed then break
  return (xs, ys)

/-- Bitwise equality of two float arrays. -/
private def sameFloats (a b : FloatArray) : Bool :=
  a.size == b.size && (List.range a.size).all fun i => (a.get! i).toBits == (b.get! i).toBits

/-- `expandLoop` (unboxed layer loop of the overlap removal) and `overlapBoundsGrouped` against the
reference functions on random layers: nodes around the root at random angles and radii (clusters
that need many passes), random sizes and spacings, steps 0, 1 and 2.5, the pass guard, nodes on the
root centre (`NaN`), equal coordinates and `±0`. -/
def overlapRemovalDifferentialTests : Suite := suite "radial.overlapRemoval.differential" do
  let mut s : UInt64 := 0x5DEECE66D
  let mut same := 0
  let mut sameOverlap := 0
  let mut overlapCases := 0
  let count := 300
  for k in [0:count] do
    let (nf, s1) := lcgFloat s 1.0 13.0
    s := s1
    let n := nf.toUInt64.toNat
    let (cx, s1) := lcgFloat s (-50.0) 50.0
    let (cy, s2) := lcgFloat s1 (-50.0) 50.0
    let (spacing, s3) := lcgFloat s2 0.0 20.0
    s := s3
    let spacing := if k % 7 == 0 then 0.0 else spacing
    let step : Float := if k % 11 == 0 then 0.0 else if k % 5 == 0 then 2.5 else 1.0
    let maxIterations := if k % 3 == 0 then 50 else 3000
    let mut xs : Array Float := #[]
    let mut ys : Array Float := #[]
    let mut ws : Array Float := #[]
    let mut hs : Array Float := #[]
    for i in [0:n] do
      let (angle, s1) := lcgFloat s 0.0 (if k % 4 == 0 then 0.3 else 6.3)
      let (radius, s2) := lcgFloat s1 0.0 60.0
      let (w, s3) := lcgFloat s2 1.0 40.0
      let (h, s4) := lcgFloat s3 1.0 30.0
      s := s4
      -- special cases: a node centred on the root, a copy of the previous node, a zero corner
      let (x, y) :=
        if k % 13 == 0 && i == 0 then (cx - w / 2.0, cy - h / 2.0)
        else if k % 17 == 0 && i > 0 then (xs[i - 1]!, ys[i - 1]!)
        else if k % 19 == 0 && i == 0 then (-0.0, 0.0)
        else (cx + radius * Float.cos angle - w / 2.0, cy + radius * Float.sin angle - h / 2.0)
      xs := xs.push x
      ys := ys.push y
      ws := ws.push w
      hs := hs.push h
    let (rx, ry) := referenceExpand cx cy step spacing maxIterations ⟨xs⟩ ⟨ys⟩ ⟨ws⟩ ⟨hs⟩
    let layer := AbstractRadiusExtensionCompaction.LayerSoa.mk' ⟨xs⟩ ⟨ys⟩ ⟨ws⟩ ⟨hs⟩ spacing
    let (fx, fy) := AbstractRadiusExtensionCompaction.expandLoop cx cy step maxIterations layer
      n.toUSize 0 0
    if sameFloats rx fx && sameFloats ry fy then same := same + 1
    else report s!"overlap removal differential: layer {k}" false
    -- the grouped overlap test on all ordered pairs of the input layer
    for i in [0:n] do
      for j in [0:n] do
        overlapCases := overlapCases + 1
        let h := spacing / 2.0
        let a := AbstractRadiusExtensionCompaction.overlapBounds (xs[i]! - h) (ys[i]! - h)
          (ws[i]! + spacing) (hs[i]! + spacing) (xs[j]! - h) (ys[j]! - h) (ws[j]! + spacing) (hs[j]! + spacing)
        let b := AbstractRadiusExtensionCompaction.overlapBoundsGrouped (xs[i]! - h) (ys[i]! - h)
          (ws[i]! + spacing) (hs[i]! + spacing) (xs[j]! - h) (ys[j]! - h) (ws[j]! + spacing) (hs[j]! + spacing)
        if a == b then sameOverlap := sameOverlap + 1
  checkEq "overlap removal differential: final layers bitwise equal" same count
  checkEq "overlapBoundsGrouped equals overlapBounds" sameOverlap overlapCases
  -- NaN bounds and touching edges
  let nan : Float := 0.0 / 0.0
  check "overlapBoundsGrouped: NaN never overlaps"
    (!AbstractRadiusExtensionCompaction.overlapBoundsGrouped nan 0.0 10.0 10.0 5.0 5.0 10.0 10.0
      && !AbstractRadiusExtensionCompaction.overlapBounds nan 0.0 10.0 10.0 5.0 5.0 10.0 10.0)
  check "sameBits: ±0 differ, equal NaNs agree"
    (!AbstractRadiusExtensionCompaction.sameBits 0.0 (-0.0) && AbstractRadiusExtensionCompaction.sameBits nan nan
      && AbstractRadiusExtensionCompaction.sameBits 1.5 1.5 && !AbstractRadiusExtensionCompaction.sameBits 1.5 2.5)

/-- The sorters. -/
def sorterTests : Suite := suite "radial.sorters" do
  let (g, parent) := ElkGraphUtil.createGraph
  let (g, n0) := g.createNode (some parent)
  let (g, n1) := g.createNode (some parent)
  let (g, n2) := g.createNode (some parent)
  let (g, n3) := g.createNode (some parent)
  -- IDSorter: stable sort by ORDER_ID (default 0)
  let g := g.setNodeProp n0 RadialOptions.ORDER_ID 2
  let g := g.setNodeProp n2 RadialOptions.ORDER_ID 1
  let g := g.setNodeProp n3 RadialOptions.ORDER_ID 2
  let (sorted, _) ← runRadial (IDSorter.sorter.sort #[n0, n1, n2, n3]) g
  checkEqR "id sorter is stable" (idsOf sorted) #[n1.idx, n2.idx, n0.idx, n3.idx]
  let (sorted, _) ← runRadial (IDSorter.sorter.sortForParent #[n0, n1, n2, n3] n0 n0 true) g
  checkEqR "id sorter sort_for_parent" (idsOf sorted) #[n1.idx, n2.idx, n0.idx, n3.idx]
  -- polar sort_with_offset on the POSITION properties
  let g := g.setNodeProp n0 CoreOptions.POSITION ⟨1.0, 0.0⟩
  let g := g.setNodeProp n1 CoreOptions.POSITION ⟨-1.0, 0.0⟩
  let g := g.setNodeProp n2 CoreOptions.POSITION ⟨0.0, 1.0⟩
  let g := g.setNodeProp n3 CoreOptions.POSITION ⟨0.0, -1.0⟩
  let (sorted, _) ← runRadial (PolarCoordinateSorter.sortWithOffset #[n0, n1, n2, n3] 0.0) g
  checkEqR "polar sort offset 0" (idsOf sorted) #[n0.idx, n2.idx, n1.idx, n3.idx]
  let (sorted, _) ← runRadial (PolarCoordinateSorter.sortWithOffset #[n0, n1, n2, n3] Float.pi) g
  checkEqR "polar sort offset PI" (idsOf sorted) #[n3.idx, n0.idx, n2.idx, n1.idx]
  -- sort_for_parent: root level uses offset 0
  let p ← PolarCoordinateSorter.create
  let (sorted, _) ← runRadial (p.sortForParent #[n0, n1, n2, n3] n0 n0 true) g
  checkEqR "polar sort_for_parent at the root level" (idsOf sorted) #[n0.idx, n2.idx, n1.idx, n3.idx]
  let (empty, _) ← runRadial (p.sort #[]) g
  check "polar sort of nothing" empty.isEmpty
  -- node_arc of a node at the bottom (center (0, 20)) is PI / 2
  let g := g.modifyNode n0 fun x => { x with x := -10.0, y := 10.0, width := 20.0, height := 20.0 }
  let (arc, _) ← runRadial (PolarCoordinateSorter.nodeArc n0) g
  checkFloat "node arc" arc (Float.pi / 2.0)
  -- strategy factories
  check "SortingStrategy none has no sorter" ((← SortingStrategy.none.create).isNone)
  check "SortingStrategy polarCoordinate has a sorter" ((← SortingStrategy.polarCoordinate.create).isSome)
  check "SortingStrategy id has a sorter" ((← SortingStrategy.id.create).isSome)

/-! ### Algorithm assembly -/

private def processorNames (props : List (ElkGraph → NodeId → ElkGraph)) : IO (Array String) := do
  let (g, parent, _) := buildTree #[0]
  let g := props.foldl (fun g f => f g parent) g
  let (algorithm, _) ← runRadial (RadialLayoutProvider.assembleAlgorithm parent) g
  return algorithm.map (·.name)

/-- The processor chain selected by the options. -/
def assemblyTests : Suite := suite "radial.assembly" do
  checkEqR "default chain" (← processorNames [])
    #["EadesRadial", "RadiusExtensionOverlapRemoval", "CalculateGraphSize", "StraightLineEdgeRouter"]
  checkEqR "all options" (← processorNames [
      fun g n => g.setNodeProp n RadialOptions.COMPACTOR CompactionStrategy.wedgeCompaction,
      fun g n => g.setNodeProp n RadialOptions.ROTATE true,
      fun g n => g.setNodeProp n RadialOptions.ROTATION_OUTGOING_EDGE_ANGLES true])
    #["EadesRadial", "RadiusExtensionOverlapRemoval", "GeneralCompactor", "GeneralRotator",
      "CalculateGraphSize", "StraightLineEdgeRouter", "EdgeAngleCalculator"]
  checkEqR "compactor NONE adds no compaction" (← processorNames [
      fun g n => g.setNodeProp n RadialOptions.COMPACTOR CompactionStrategy.none])
    #["EadesRadial", "RadiusExtensionOverlapRemoval", "CalculateGraphSize", "StraightLineEdgeRouter"]
  check "IntermediateProcessorStrategy order"
    ((ElkEnum.values : Array IntermediateProcessorStrategy).map ElkEnum.javaName ==
      #["OVERLAP_REMOVAL", "COMPACTION", "ROTATION", "GRAPH_SIZE_CALCULATION", "OUTGOING_EDGE_ANGLES"])
  check "RadialLayoutPhases order"
    ((ElkEnum.values : Array RadialLayoutPhases).map ElkEnum.javaName == #["P1_NODE_PLACEMENT", "P2_EDGE_ROUTING"])
  checkThrows "compaction strategy NONE has no implementation" do
    let (g, _, _) := buildTree #[0]
    let _ ← runRadial (createCompactor CompactionStrategy.none) g
    pure ()
  -- the same chain through `layout`: typed enum options work without parsers
  let (g, parent, nodes) := buildTree #[0, 0, 0, 1, 1, 2]
  let g := g.setNodeProp parent RadialOptions.COMPACTOR CompactionStrategy.radialCompaction
  let g := g.setNodeProp parent RadialOptions.SORTER SortingStrategy.id
  let g := g.setNodeProp parent RadialOptions.OPTIMIZATION_CRITERIA RadialTranslationStrategy.edgeLength
  let g ← layoutDirect g parent
  let r := g.node nodes[0]!
  check "typed enum options: root is placed inside the graph"
    (r.x >= 0.0 && r.y >= 0.0 && r.x + r.width <= (g.node parent).width && r.y + r.height <= (g.node parent).height)
  check "typed enum options: RADIUS is set to the largest node diagonal"
    (match (g.node parent).props.get RadialOptions.RADIUS with
      | some r => (r - Float.sqrt 1800.0).abs < 1e-9
      | none => false)
  -- the root is stored in the side table of the radial state, so a second layout works
  let g ← layoutDirect g parent
  check "layout twice" ((g.node parent).width > 0.0)

/-- Layout errors. -/
def errorTests : Suite := suite "radial.errors" do
  let cycle := "{\"id\":\"root\",\"layoutOptions\":{\"algorithm\":\"org.eclipse.elk.radial\"},\"children\":[{\"id\":\"a\",\"width\":10,\"height\":10},{\"id\":\"b\",\"width\":10,\"height\":10}],\"edges\":[{\"id\":\"e0\",\"sources\":[\"a\"],\"targets\":[\"b\"]},{\"id\":\"e1\",\"sources\":[\"b\"],\"targets\":[\"a\"]}]}"
  match ← Elk.Api.layoutJson cycle "{}" with
  | .error e =>
    check "cycle: not a tree" (e.endsWith "The given graph is not a tree!")
    -- ELK Java throws IllegalArgumentException here (elk-rs: UnsupportedConfigurationException); the JSON
    -- API reports it like Java's `Throwable.toString()`
    check "cycle: IllegalArgumentException" (e == "java.lang.IllegalArgumentException: The given graph is not a tree!")
  | .ok _ => report "cycle: error expected" false
  let empty := "{\"id\":\"root\",\"layoutOptions\":{\"algorithm\":\"org.eclipse.elk.radial\"},\"children\":[]}"
  -- a graph without children is not laid out by the engine, so there is no error (elk-rs)
  match ← Elk.Api.layoutJson empty "{}" with
  | .error e => report "no children: no error expected" false e
  | .ok out => check "no children: empty layout" (out.contains '0')

/-! ### Fixtures -/

/-- Fixture input names (`<name>.json` without `.expected.json`), sorted. -/
private def fixtureNames (dir : System.FilePath) : IO (Array String) := do
  let entries ← System.FilePath.readDir dir
  let names := entries.filterMap fun e =>
    if e.fileName.endsWith ".json" && !e.fileName.endsWith ".expected.json" then
      some (e.fileName.dropEnd ".json".length).toString
    else none
  return stableSort names (fun a b => compare a b)

private def checkFixtures (dir : System.FilePath) (minimum : Nat) : TestM Unit := do
  let names ← fixtureNames dir
  check s!"fixtures found in {dir}" (names.size >= minimum)
  for name in names do
    let input ← IO.FS.readFile (dir / s!"{name}.json")
    let result ← Elk.Api.layoutJson input "{}" (lenient := false) (pretty := true) (sortKeys := true)
    -- `<name>.error`: ELK Java rejects the input with the exception text in the file
    if ← (dir / s!"{name}.error").pathExists then
      let expectedError := (← IO.FS.readFile (dir / s!"{name}.error")).trimAscii.toString
      match result with
      | .error e => checkEq s!"{name}: fails with the ELK Java exception" (javaExceptionText e) expectedError
      | .ok _ => report s!"{name}: fails with the ELK Java exception" false "layout succeeded"
    else
      let expected ← IO.FS.readFile (dir / s!"{name}.expected.json")
      match result with
      | .error e => report s!"{name}: layout" false e
      | .ok actual => checkJson s!"{name}: matches oracle" actual expected (tol := ELK_RS_FIXTURE_TOL)

/-- `radial.fixtures`: `Elk.Api.layoutJson` reproduces the stock elk-rs output byte-for-byte. -/
def fixtureTests : Suite := suite "radial.fixtures" do
  LayoutMetaDataService.ensureInitialized
  checkFixtures "tests/fixtures/radial" 20

/-- Runs `action` with the Java-like enum option parsers of the radial options installed, then
restores the registry. -/
def withEnumParsers {α : Type} (action : IO α) : IO α := do
  let snapshot ← LayoutMetaDataService.getInstance
  LayoutMetaDataService.registerLayoutMetaDataProvider RadialMetaDataProvider.enumParserProvider
  try action finally LayoutMetaDataService.instanceRef.set snapshot

/-- `radial.fixtures.enum`: with the enum parsers installed, the output equals the elk-rs output
of a build whose provider registers the same parsers. -/
def enumFixtureTests : Suite := suite "radial.fixtures.enum" do
  LayoutMetaDataService.ensureInitialized
  let st ← get
  let (_, st') ← withEnumParsers ((checkFixtures "tests/fixtures/radial/enum" 20).run st)
  set st'

def suites : Array Suite :=
  #[metadataTests, centerOnRootTests, utilTests, compactionHelperTests, overlapRemovalDifferentialTests,
    sorterTests, assemblyTests, errorTests, fixtureTests, enumFixtureTests]

end Tests.Radial
