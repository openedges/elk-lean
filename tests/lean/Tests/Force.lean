import Tests.Framework
import Tests.JsonCompare
import Elk.Api
import Elk.Alg.Force
/-!
# Tests of the force and stress layouts (`org.eclipse.elk.alg.force`)

* `force.import`: ports of `force_import_test.rs` (import, `ComponentsProcessor.split`);
* `force.meta`: the option and algorithm metadata of `ForceMetaDataProvider`/`StressMetaDataProvider`;
* `force.formulas`: the force formulas of the models, `wiggle`, shortest paths of the stress layout;
* `force.layout`: layouts selected through directly stored properties (the Eades model and the stress
  `DIMENSION` cannot be selected from JSON, see `ForceMetaDataProvider`), determinism, errors;
* `force.fixtures`: every `tests/fixtures/force/<name>.json` is laid out with `Elk.Api.layoutJson` and
  must equal the elk-rs oracle output `<name>.expected.json` byte for byte. If the environment
  variable `ELK_FORCE_DUMP_DIR` is set, the actual outputs are also written there as
  `<name>.json` (for `scripts/compare_model_parity_layouts.py`).

`Elk.Api` links this plugin only through its import of `Elk.Alg.Force`; the suite imports the plugin
directly, so the providers and the metadata are registered in the test binary either way.
-/
namespace Tests.Force

open Tests Elk Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Data
open Elk.Alg.Force Elk.Alg.Force.Graph Elk.Alg.Force.Model Elk.Alg.Force.Options Elk.Alg.Force.Stress

/-! ### Helpers -/

/-- Substring test. -/
private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- `force_import_test.rs::create_elk_graph`: a root with three nodes and two labelled edges
`n1 -> n2` ("test") and `n1 -> n3` ("test2"). -/
private def addImportGraph (g : ElkGraph) (root : NodeId) : ElkGraph × Array NodeId := Id.run do
  let (g, n1) := g.createNode (some root)
  let (g, n2) := g.createNode (some root)
  let (g, n3) := g.createNode (some root)
  let (g, e1) := ElkGraphUtil.createSimpleEdge g (.node n1) (.node n2)
  let (g, _) := g.createLabel (some (.edge e1)) "test"
  let (g, e2) := ElkGraphUtil.createSimpleEdge g (.node n1) (.node n3)
  let (g, _) := g.createLabel (some (.edge e2)) "test2"
  return (g, #[n1, n2, n3])

/-- Imports the graph below `root` into an `FGraph`. -/
private def importFGraph (g : ElkGraph) (root : NodeId) : IO FGraph := do
  LayoutMetaDataService.ensureInitialized
  let (fg, _) ← ElkM.run (ElkGraphImporter.importGraph root) g
  return fg

/-- Lays out the graph with the engine; returns the final graph. -/
private def layoutGraph (g : ElkGraph) (root : NodeId) : IO ElkGraph := do
  Elk.Api.ensureInitialized
  let (_, g) ← ElkM.run (RecursiveGraphLayoutEngine.layout root ProgressMonitor.null) g
  return g

/-- The rounded `(x, y)` strings of the children of `root` (deterministic comparison key). -/
private def positions (g : ElkGraph) (root : NodeId) : Array (Float × Float) :=
  (g.node root).children.map fun c => ((g.node c).x, (g.node c).y)

/-- Exact equality of two position lists. -/
private def samePositions (a b : Array (Float × Float)) : Bool :=
  a.size == b.size && (a.zip b).all fun ((x1, y1), (x2, y2)) => x1 == x2 && y1 == y2

/-- A chain `n0 - n1 - ... - n(k-1)` of 30x30 nodes below a root that runs `algorithm` with `seed`. -/
private def chainGraph (algorithm : String) (k : Nat) (seed : Int) : ElkGraph × NodeId × Array NodeId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root CoreOptions.ALGORITHM algorithm
  let g := g.setNodeProp root CoreOptions.RANDOM_SEED seed
  let mut g := g
  let mut ns : Array NodeId := #[]
  for _ in [0:k] do
    let (g', n) := g.createNode (some root)
    g := g'.modifyNode n (·.setSize ⟨30.0, 30.0⟩)
    ns := ns.push n
  for i in [0:k - 1] do
    let (g', _) := ElkGraphUtil.createSimpleEdge g (.node ns[i]!) (.node ns[i + 1]!)
    g := g'
  return (g, root, ns)

/-! ### Ports of `force_import_test.rs` -/

/-- `force_import_test.rs`. -/
def importTests : Suite := suite "force.import" do
  -- test_import
  let (g, root) := ElkGraphUtil.createGraph
  let (g, _) := addImportGraph g root
  let fg ← importFGraph g root
  checkEq "test_import: nodes" fg.nodes.size 3
  checkEq "test_import: edges" fg.edges.size 2
  checkEq "test_import: labels" fg.labels.size 2
  -- two components: the children and edges of two such graphs below one root
  let (g2, root2) := ElkGraphUtil.createGraph
  let (g2, _) := addImportGraph g2 root2
  let (g2, _) := addImportGraph g2 root2
  let fg2 ← importFGraph g2 root2
  -- test_separate_connected_components
  let graphs := ComponentsProcessor.split { fg2 with props := fg2.props.set ForceOptions.SEPARATE_CONNECTED_COMPONENTS true }
  checkEq "separate: 2 components" graphs.size 2
  for (comp, i) in graphs.zipIdx do
    checkEq s!"separate: component {i} nodes" comp.nodes.size 3
    checkEq s!"separate: component {i} edges" comp.edges.size 2
    checkEq s!"separate: component {i} labels" comp.labels.size 2
  -- test_do_not_separate_connected_components
  let graphs := ComponentsProcessor.split { fg2 with props := fg2.props.set ForceOptions.SEPARATE_CONNECTED_COMPONENTS false }
  checkEq "no separation: 1 component" graphs.size 1
  checkEq "no separation: nodes" graphs[0]!.nodes.size 6
  checkEq "no separation: edges" graphs[0]!.edges.size 4
  checkEq "no separation: labels" graphs[0]!.labels.size 4

/-! ### Import details -/

/-- Importer: sizes, centre positions, `PORT_CONSTRAINTS`, hyperedges, ignored edges. -/
def importerTests : Suite := suite "force.importer" do
  LayoutMetaDataService.ensureInitialized
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n1) := g.createNode (some root)
  let (g, n2) := g.createNode (some root)
  let (g, sub) := g.createNode (some n2)
  let g := g.modifyNode n1 fun n => { n with x := 10.0, y := 20.0, width := 40.0, height := 0.0 }
  let g := g.modifyNode n2 fun n => { n with x := 100.0, y := 5.0, width := 0.0, height := 30.0 }
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node n1) (.node n2)
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node n1) (.node n1)
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node n1) (.node sub)
  let (fg, g') ← ElkM.run (ElkGraphImporter.importGraph root) g
  checkEq "nodes" fg.nodes.size 2
  checkEq "edges: self loop and hierarchical edge are skipped" fg.edges.size 1
  let a := fg.arena
  checkFloat "centre x" (a.nodePosition[0]!).x 30.0
  checkFloat "centre y" (a.nodePosition[0]!).y 20.0
  checkFloat "size at least 1: width" (a.nodeSize[0]!).x 40.0
  checkFloat "size at least 1: height" (a.nodeSize[0]!).y 1.0
  checkFloat "size at least 1: width 2" (a.nodeSize[1]!).x 1.0
  check "origin of the graph" (fg.origin == some (Origin.elkNode root))
  check "origin of node 0" (a.nodeOrigin[0]! == some (Origin.elkNode n1))
  check "port constraints are FREE afterwards" (((g'.node n1).props.get CoreOptions.PORT_CONSTRAINTS) == some PortConstraints.free)
  -- hyperedge
  let (h, hroot) := ElkGraphUtil.createGraph
  let (h, a1) := h.createNode (some hroot)
  let (h, a2) := h.createNode (some hroot)
  let (h, a3) := h.createNode (some hroot)
  let (h, _) := ElkGraphUtil.createHyperedge h #[.node a1] #[.node a2, .node a3]
  try
    let _ ← ElkM.run (ElkGraphImporter.importGraph hroot) h
    report "hyperedge: rejected" false
  catch e =>
    check "hyperedge: message" (has (toString e) "UnsupportedGraphException: Graph must not contain hyperedges.")

/-! ### Metadata -/

private def isDouble (v : Option PropValue) (x : Float) : Bool :=
  match v with | some (.double y) => y == x | _ => false

private def isInt (v : Option PropValue) (x : Int) : Bool :=
  match v with | some (.int y) => y == x | _ => false

private def isBool (v : Option PropValue) (x : Bool) : Bool :=
  match v with | some (.bool y) => y == x | _ => false

/-- Looks up an option by id (reports a failure and returns a dummy if missing). -/
private def opt (id : String) : TestM LayoutOptionData := do
  match ← LayoutMetaDataService.getOptionData id with
  | some d => return d
  | none =>
    report s!"option {id} registered" false
    return { id }

/-- `force_meta_data_provider.rs` / `stress_meta_data_provider.rs`. -/
def metaTests : Suite := suite "force.meta" do
  Elk.Api.ensureInitialized
  let some force ← LayoutMetaDataService.getAlgorithmData "org.eclipse.elk.force"
    | report "algorithm force registered" false
  checkEq "force: name" force.name "ELK Force"
  checkEq "force: category" (force.categoryId.getD "") "org.eclipse.elk.force"
  checkEq "force: bundle" (force.definingBundleId.getD "") "org.eclipse.elk.alg.force"
  checkEq "force: preview" (force.previewImagePath.getD "") "images/force_layout.png"
  check "force: features" (force.supportedFeatures == EnumSet.of #[.multiEdges, .edgeLabels])
  check "force: description" (has force.description "Currently the original Eades model and the Fruchterman - Reingold model are supported.")
  checkEq "force: known options" force.knownOptionIds
    #[CoreOptions.PRIORITY.id, CoreOptions.SPACING_NODE_NODE.id, CoreOptions.SPACING_EDGE_LABEL.id,
      CoreOptions.ASPECT_RATIO.id, CoreOptions.RANDOM_SEED.id, CoreOptions.SEPARATE_CONNECTED_COMPONENTS.id,
      CoreOptions.PADDING.id, CoreOptions.INTERACTIVE.id, CoreOptions.PORT_CONSTRAINTS.id,
      CoreOptions.EDGE_LABELS_INLINE.id, CoreOptions.OMIT_NODE_MICRO_LAYOUT.id,
      CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE.id, CoreOptions.NODE_SIZE_OPTIONS.id,
      CoreOptions.NODE_SIZE_CONSTRAINTS.id, CoreOptions.NODE_LABELS_PLACEMENT.id,
      CoreOptions.PORT_LABELS_PLACEMENT.id, "org.eclipse.elk.force.model", "org.eclipse.elk.force.temperature",
      "org.eclipse.elk.force.iterations", "org.eclipse.elk.force.repulsion",
      "org.eclipse.elk.force.repulsivePower", CoreOptions.TOPDOWN_LAYOUT.id,
      CoreOptions.TOPDOWN_SCALE_FACTOR.id, CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH.id,
      CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO.id, CoreOptions.TOPDOWN_NODE_TYPE.id]
  check "force: PRIORITY default 1" (isInt (force.defaultValueRaw CoreOptions.PRIORITY.id) 1)
  check "force: SPACING_NODE_NODE default 80" (isDouble (force.defaultValueRaw CoreOptions.SPACING_NODE_NODE.id) 80.0)
  check "force: SPACING_EDGE_LABEL default 5" (isDouble (force.defaultValueRaw CoreOptions.SPACING_EDGE_LABEL.id) 5.0)
  check "force: ASPECT_RATIO default 1.6" (isDouble (force.defaultValueRaw CoreOptions.ASPECT_RATIO.id) 1.6)
  check "force: RANDOM_SEED default 1" (isInt (force.defaultValueRaw CoreOptions.RANDOM_SEED.id) 1)
  check "force: SEPARATE_CONNECTED_COMPONENTS default true" (isBool (force.defaultValueRaw CoreOptions.SEPARATE_CONNECTED_COMPONENTS.id) true)
  check "force: PADDING default 50" (force.defaultValue CoreOptions.PADDING == some (ElkPadding.ofAny 50.0))
  check "force: EDGE_LABELS_INLINE default false" (isBool (force.defaultValueRaw CoreOptions.EDGE_LABELS_INLINE.id) false)
  check "force: TOPDOWN_NODE_TYPE default" (force.defaultValue CoreOptions.TOPDOWN_NODE_TYPE == some TopdownNodeTypes.hierarchicalNode)
  let some stress ← LayoutMetaDataService.getAlgorithmData "org.eclipse.elk.stress"
    | report "algorithm stress registered" false
  checkEq "stress: name" stress.name "ELK Stress"
  checkEq "stress: category" (stress.categoryId.getD "") "org.eclipse.elk.force"
  checkEq "stress: preview" (stress.previewImagePath.getD "") "images/stress_layout.png"
  check "stress: no features" (stress.supportedFeatures == EnumSet.empty)
  checkEq "stress: known options" stress.knownOptionIds
    #[CoreOptions.INTERACTIVE.id, CoreOptions.EDGE_LABELS_INLINE.id, CoreOptions.NODE_SIZE_CONSTRAINTS.id,
      CoreOptions.NODE_SIZE_MINIMUM.id, CoreOptions.NODE_SIZE_OPTIONS.id, CoreOptions.NODE_LABELS_PLACEMENT.id,
      CoreOptions.OMIT_NODE_MICRO_LAYOUT.id, CoreOptions.PORT_LABELS_PLACEMENT.id,
      "org.eclipse.elk.stress.fixed", "org.eclipse.elk.stress.dimension", "org.eclipse.elk.stress.epsilon",
      "org.eclipse.elk.stress.iterationLimit", "org.eclipse.elk.stress.desiredEdgeLength"]
  check "stress: EDGE_LABELS_INLINE default true" (isBool (stress.defaultValueRaw CoreOptions.EDGE_LABELS_INLINE.id) true)
  -- the force category lists both algorithms
  let some cat ← LayoutMetaDataService.getCategoryData "org.eclipse.elk.force"
    | report "category force registered" false
  check "category lists force" (cat.layouters.contains "org.eclipse.elk.force")
  check "category lists stress" (cat.layouters.contains "org.eclipse.elk.stress")
  -- options
  let model ← opt "org.eclipse.elk.force.model"
  check "MODEL: enum" (model.type == .enum)
  check "MODEL: default FRUCHTERMAN_REINGOLD" (model.defaultValue.bind (PropCodec.dec : PropValue → Option ForceModelStrategy) == some .fruchtermanReingold)
  check "MODEL: parents" (model.targets == EnumSet.of #[.parents])
  checkEq "MODEL: name" model.name "Force Model"
  check "MODEL: no parser (Rust)" model.parser.isNone
  check "MODEL: no choices (Rust)" model.choices.isEmpty
  let iterations ← opt "org.eclipse.elk.force.iterations"
  check "ITERATIONS: int default 300" (iterations.type == .int && isInt iterations.defaultValue 300)
  check "ITERATIONS: lower bound 1" (match iterations.lowerBound with | some b => !b.isExclusive && isInt (some b.value) 1 | none => false)
  let rp ← opt "org.eclipse.elk.force.repulsivePower"
  check "REPULSIVE_POWER: edges, default 0, lower bound 0"
    (rp.targets == EnumSet.of #[.edges] && isInt rp.defaultValue 0
      && (match rp.lowerBound with | some b => !b.isExclusive && isInt (some b.value) 0 | none => false))
  let temp ← opt "org.eclipse.elk.force.temperature"
  check "TEMPERATURE: double 0.001, exclusive lower bound 0"
    (temp.type == .double && isDouble temp.defaultValue 0.001
      && (match temp.lowerBound with | some b => b.isExclusive && isDouble (some b.value) 0.0 | none => false))
  let rep ← opt "org.eclipse.elk.force.repulsion"
  check "REPULSION: double 5.0, exclusive lower bound 0"
    (rep.type == .double && isDouble rep.defaultValue 5.0
      && (match rep.lowerBound with | some b => b.isExclusive && isDouble (some b.value) 0.0 | none => false))
  let fixed ← opt "org.eclipse.elk.stress.fixed"
  check "FIXED: boolean, nodes, default false"
    (fixed.type == .boolean && fixed.targets == EnumSet.of #[.nodes] && isBool fixed.defaultValue false)
  let del ← opt "org.eclipse.elk.stress.desiredEdgeLength"
  check "DESIRED_EDGE_LENGTH: double 100, parents+edges"
    (del.type == .double && isDouble del.defaultValue 100.0 && del.targets == EnumSet.of #[.parents, .edges])
  let dim ← opt "org.eclipse.elk.stress.dimension"
  check "DIMENSION: enum default XY, no parser (Rust)"
    (dim.type == .enum && dim.defaultValue.bind (PropCodec.dec : PropValue → Option Dimension) == some .xy && dim.parser.isNone)
  let eps ← opt "org.eclipse.elk.stress.epsilon"
  check "EPSILON: double 0.001" (eps.type == .double && isDouble eps.defaultValue 0.001)
  let lim ← opt "org.eclipse.elk.stress.iterationLimit"
  check "ITERATION_LIMIT: int MAX_VALUE" (lim.type == .int && isInt lim.defaultValue 2147483647)
  -- Java names of the enums
  checkEq "ForceModelStrategy names" ((ElkEnum.values : Array ForceModelStrategy).map ElkEnum.javaName) #["EADES", "FRUCHTERMAN_REINGOLD"]
  checkEq "Dimension names" ((ElkEnum.values : Array Dimension).map ElkEnum.javaName) #["XY", "X", "Y"]

/-! ### Formulas -/

/-- The force formulas, `wiggle` and the shortest paths / weights of the stress layout. -/
def formulaTests : Suite := suite "force.formulas" do
  -- Eades
  checkFloat "Eades.repulsive(2, 5) = 1.25" (EadesModel.repulsive 2.0 5.0) 1.25
  checkFloat "Eades.repulsive(0, 5) = 500" (EadesModel.repulsive 0.0 5.0) 500.0
  checkFloat "Eades.attractive(160, 80) = ln 2" (EadesModel.attractive 160.0 80.0) (Float.log 2.0)
  checkFloat "Eades.attractive(0, 80) = -100" (EadesModel.attractive 0.0 80.0) (-100.0)
  -- Fruchterman-Reingold
  checkFloat "FR.repulsive(4, 2) = 1" (FruchtermanReingoldModel.repulsive 4.0 2.0) 1.0
  checkFloat "FR.repulsive(0, 2) = 400" (FruchtermanReingoldModel.repulsive 0.0 2.0) 400.0
  checkFloat "FR.attractive(4, 2) = 8" (FruchtermanReingoldModel.attractive 4.0 2.0) 8.0
  -- wiggle: x + (r * a - a / 2) with the draws of java.util.Random(1)
  let r := Random.ofInt 1
  let (dx, r1) := r.nextDouble
  let (dy, r2) := r1.nextDouble
  let (v, r3) := wiggle ⟨3.0, -4.0⟩ r 1.0
  check "wiggle x" (v.x == 3.0 + (dx * 1.0 - 1.0 / 2.0))
  check "wiggle y" (v.y == -4.0 + (dy * 1.0 - 1.0 / 2.0))
  check "wiggle advances the generator twice" (r3 == r2)
  -- stress: shortest paths of a chain with edge lengths 100 / 50
  LayoutMetaDataService.ensureInitialized
  let (chain, root, ns) := chainGraph "stress" 4 3
  let chain := chain.modifyEdge ⟨1⟩ fun e => { e with props := e.props.set StressOptions.DESIRED_EDGE_LENGTH 50.0 }
  let fg ← importFGraph chain root
  let m := StressMajorization.init fg
  checkEq "init: apsp size" m.apsp.size ns.size
  checkFloat "apsp 0-1" ((m.apsp[0]!).get! 1) 100.0
  checkFloat "apsp 0-2" ((m.apsp[0]!).get! 2) 150.0
  checkFloat "apsp 0-3" ((m.apsp[0]!).get! 3) 250.0
  checkFloat "apsp 3-1" ((m.apsp[3]!).get! 1) 150.0
  checkFloat "apsp diagonal" ((m.apsp[2]!).get! 2) 0.0
  checkFloat "weight 0-1 = 1/100^2" ((m.w[0]!).get! 1) 0.0001
  checkFloat "weight 0-3 = 1/250^2" ((m.w[0]!).get! 3) (1.0 / 62500.0)
  checkFloat "weight diagonal" ((m.w[1]!).get! 1) 0.0
  check "dimension default XY" (m.dim == .xy)
  checkFloat "epsilon default" m.epsilon 0.001
  checkEq "iteration limit default" m.iterationLimit 2147483647
  -- a disconnected graph has infinite distances and zero weights
  let (g2, root2) := ElkGraphUtil.createGraph
  let (g2, a) := g2.createNode (some root2)
  let (g2, b) := g2.createNode (some root2)
  let (g2, c) := g2.createNode (some root2)
  let (g2, _) := ElkGraphUtil.createSimpleEdge g2 (.node a) (.node b)
  let fg2 ← importFGraph g2 root2
  let m2 := StressMajorization.init fg2
  check "disconnected: infinite distance" (((m2.apsp[0]!).get! 2).isInf)
  checkFloat "disconnected: zero weight" ((m2.w[0]!).get! 2) 0.0
  let _ := c
  -- done criterion
  check "done: previous stress 0" (m.done 0 0.0 5.0)
  check "done: converged" (m.done 1 10.0 9.999999)
  check "done: not converged" (!m.done 1 10.0 5.0)
  check "done: iteration limit" ({ m with iterationLimit := 2 }.done 2 10.0 5.0)

/-! ### Layouts -/

/-- Eades model and stress dimension through stored properties, determinism and error cases. -/
def layoutTests : Suite := suite "force.layout" do
  -- determinism: the same seed gives bit-identical results, different seeds differ
  let (g, root, _) := chainGraph "org.eclipse.elk.force" 5 3
  let a ← layoutGraph g root
  let b ← layoutGraph g root
  check "force: same seed, same layout" (samePositions (positions a root) (positions b root))
  let (g4, root4, _) := chainGraph "org.eclipse.elk.force" 5 4
  let c ← layoutGraph g4 root4
  check "force: different seed, different layout" (!samePositions (positions a root) (positions c root))
  check "force: root has a size" ((a.node root).width > 0.0 && (a.node root).height > 0.0)
  checkFloat "force: padded bounding box starts at the padding"
    ((positions a root).foldl (fun m (x, _) => fmin m x) Float.maxValue) 12.0 1e-9
  -- Eades selected through the stored property
  let eadesGraph := g.setNodeProp root ForceOptions.MODEL ForceModelStrategy.eades
  let e1 ← layoutGraph eadesGraph root
  let e2 ← layoutGraph eadesGraph root
  check "eades: deterministic" (samePositions (positions e1 root) (positions e2 root))
  check "eades: differs from Fruchterman-Reingold" (!samePositions (positions e1 root) (positions a root))
  check "eades: finite coordinates" ((positions e1 root).all fun (x, y) => !x.isNaN && !x.isInf && !y.isNaN && !y.isInf)
  -- eades with repulsive power (bend points) and an edge label
  let (g5, root5, ns5) := chainGraph "org.eclipse.elk.force" 3 5
  let g5 := g5.setNodeProp root5 ForceOptions.MODEL ForceModelStrategy.eades
  let g5 := g5.modifyEdge ⟨0⟩ fun e => { e with props := e.props.set ForceOptions.REPULSIVE_POWER 2 }
  let (g5, _) := g5.createLabel (some (.edge ⟨0⟩)) "lbl"
  let g5' ← layoutGraph g5 root5
  let sec := (g5'.edge ⟨0⟩).sections
  checkEq "eades: edge with repulsive power has a section" sec.size 1
  checkEq "eades: two bend points" (g5'.edgeSection sec[0]!).bendPoints.size 2
  let _ := ns5
  -- stress dimension X keeps the y coordinates of the initial (interactive) layout
  let (g6, root6, ns6) := chainGraph "org.eclipse.elk.stress" 4 3
  let g6 := g6.setNodeProp root6 StressOptions.INTERACTIVE true
  let g6 := g6.setNodeProp root6 StressOptions.DIMENSION Dimension.x
  let g6 := (ns6.zipIdx).foldl (fun g (n, i) => g.modifyNode n fun x =>
    { x with x := 20.0 * i.toFloat, y := 7.0 * (i % 2).toFloat }) g6
  let ys0 := ns6.map fun n => (g6.node n).y
  let g6' ← layoutGraph g6 root6
  let ys1 := ns6.map fun n => (g6'.node n).y
  -- the final y coordinates are shifted by a constant (padding - minimum)
  let shift := ys1[0]! - ys0[0]!
  check "stress X: y coordinates only shifted" ((ys0.zip ys1).all fun (y0, y1) => (y1 - y0 - shift).abs < 1e-9)
  let xs1 := ns6.map fun n => (g6'.node n).x
  check "stress X: x coordinates changed" (xs1[1]! - xs1[0]! != 20.0)
  -- stress dimension Y keeps the x coordinates
  let g7 := g6.setNodeProp root6 StressOptions.DIMENSION Dimension.y
  let g7' ← layoutGraph g7 root6
  let xs7 := ns6.map fun n => (g7'.node n).x
  let xs0 := ns6.map fun n => (g6.node n).x
  let shiftX := xs7[0]! - xs0[0]!
  check "stress Y: x coordinates only shifted" ((xs0.zip xs7).all fun (x0, x1) => (x1 - x0 - shiftX).abs < 1e-9)
  -- a fixed node does not move relative to the other fixed node
  let g8 := g6.setNodeProp root6 StressOptions.DIMENSION Dimension.xy
  let g8 := g8.setNodeProp ns6[0]! StressOptions.FIXED true
  let g8 := g8.setNodeProp ns6[3]! StressOptions.FIXED true
  let g8' ← layoutGraph g8 root6
  let dxFixed := (g8'.node ns6[3]!).x - (g8'.node ns6[0]!).x
  let dyFixed := (g8'.node ns6[3]!).y - (g8'.node ns6[0]!).y
  checkFloat "stress fixed: dx of the fixed nodes" dxFixed 60.0 1e-9
  checkFloat "stress fixed: dy of the fixed nodes" dyFixed 7.0 1e-9
  -- hyperedges are rejected by both algorithms
  for algo in #["org.eclipse.elk.force", "org.eclipse.elk.stress"] do
    let (h, hroot) := ElkGraphUtil.createGraph
    let h := h.setNodeProp hroot CoreOptions.ALGORITHM algo
    let (h, a1) := h.createNode (some hroot)
    let (h, a2) := h.createNode (some hroot)
    let (h, a3) := h.createNode (some hroot)
    let (h, _) := ElkGraphUtil.createHyperedge h #[.node a1] #[.node a2, .node a3]
    try
      let _ ← layoutGraph h hroot
      report s!"{algo}: hyperedge rejected" false
    catch e =>
      check s!"{algo}: hyperedge rejected" (has (toString e) "UnsupportedGraphException")
  -- an empty graph is a no-op
  let (e, eroot) := ElkGraphUtil.createGraph
  let e := e.setNodeProp eroot CoreOptions.ALGORITHM "org.eclipse.elk.force"
  let e' ← layoutGraph e eroot
  checkFloat "empty graph: width unchanged" (e'.node eroot).width 0.0

/-! ### Fixtures -/

/-- Names of the `<name>.json` fixtures (without `.expected.json`), sorted. -/
private def fixtureNames (dir : System.FilePath) : IO (Array String) := do
  let entries ← dir.readDir
  let names := entries.filterMap fun e =>
    if e.fileName.endsWith ".json" && !e.fileName.endsWith ".expected.json" then
      some (e.fileName.dropEnd ".json".length).toString
    else none
  return names.qsort (fun a b => a < b)

/-- Directory of the fixtures (`lake test` runs in the project root). -/
private def fixtureDir : System.FilePath := "tests/fixtures/force"

/-- Runs every fixture of `dir`: `Elk.Api.layoutJson` must reproduce `<name>.expected.json`, or, for
fixtures with a `<name>.error.txt`, fail with exactly that message. -/
private def runFixtures (dir : System.FilePath) (dumpDir : Option String) : TestM Unit := do
  let names ← fixtureNames dir
  check "fixtures found" (names.size >= 20)
  for name in names do
    let input ← IO.FS.readFile (dir / s!"{name}.json")
    let expectedPath := dir / s!"{name}.expected.json"
    let errorPath := dir / s!"{name}.error.txt"
    let result ← Elk.Api.layoutJson input "{}" (lenient := false) (pretty := true) (sortKeys := true)
    if ← errorPath.pathExists then
      match result with
      | .ok _ => report s!"{name}: layout fails" false "expected an error"
      | .error e =>
        -- the exception class prefix is the core's business (the validation reports
        -- `GraphValidationException`, elk-rs wraps it): compare the message only
        let msg (t : String) : String := (t.dropWhile (· != ':')).drop 2 |>.toString
        checkEq s!"{name}: error message matches oracle" (msg e) (msg (← IO.FS.readFile errorPath))
    else if !(← expectedPath.pathExists) then
      report s!"{name}: expected output exists" false s!"missing {expectedPath}"
    else
      let expected ← IO.FS.readFile expectedPath
      match result with
      | .error e => report s!"{name}: layout" false e
      | .ok actual =>
        if let some d := dumpDir then
          IO.FS.createDirAll d
          IO.FS.writeFile (System.FilePath.mk d / s!"{name}.json") actual
        checkJson s!"{name}: matches oracle" actual expected (tol := ELK_RS_FIXTURE_TOL)

/-- `force.fixtures`: `Elk.Api.layoutJson` on every fixture must reproduce the oracle output. -/
def fixtureTests : Suite := suite "force.fixtures" do
  runFixtures fixtureDir (← IO.getEnv "ELK_FORCE_DUMP_DIR")

/-- Directory of the fixtures that need the enum options `MODEL` / `DIMENSION` to be parseable. -/
private def enumFixtureDir : System.FilePath := "tests/fixtures/force_enum"

/-- Strict enum parser (exact Java name, upper-cased), the parser the elk-rs harness installs. -/
private def strictEnumParser (α : Type) [ElkEnum α] : OptionParser :=
  fun s => (ElkEnum.ofJavaName? s.trimAscii.toString.toUpper : Option α).map PropCodec.enc

/-- `force.fixtures.enum`: the stock elk-rs registration of `elk.force.model` and `elk.stress.dimension`
has no parser, so the oracle runner ignores `EADES` / `X` / `Y`. The expected outputs of
`tests/fixtures/force_enum` were therefore produced by the same elk-rs code driven through a small
Rust harness that re-registers the two options with a parser. This suite does the same in Lean (it
swaps in parsers for the two options, runs the fixtures and restores the stock registration). -/
def enumFixtureTests : Suite := suite "force.fixtures.enum" do
  Elk.Api.ensureInitialized
  let some model ← LayoutMetaDataService.getOptionData ForceOptions.MODEL.id
    | report "MODEL registered" false
  let some dim ← LayoutMetaDataService.getOptionData StressOptions.DIMENSION.id
    | report "DIMENSION registered" false
  LayoutMetaDataService.modifyInstance fun s =>
    (s.registerLayoutOption { model with parser := some (strictEnumParser ForceModelStrategy) }).registerLayoutOption
      { dim with parser := some (strictEnumParser Dimension) }
  try
    runFixtures enumFixtureDir none
  finally
    LayoutMetaDataService.modifyInstance fun s => (s.registerLayoutOption model).registerLayoutOption dim

def suites : Array Tests.Suite :=
  #[importTests, importerTests, metaTests, formulaTests, layoutTests, fixtureTests, enumFixtureTests]

end Tests.Force
