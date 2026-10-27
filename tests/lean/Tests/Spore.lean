import Tests.Framework
import Tests.JsonCompare
import Elk.Api
import Elk.Alg.Spore
/-! Tests of `org.eclipse.elk.alg.spore` (SPOrE overlap removal and compaction).

* `spore.options` / `spore.meta`: option constants, metadata registration and provider registration;
* `spore.graph`, `spore.importer`, `spore.cost`, `spore.p2`, `spore.p3`, `spore.shrink`: unit tests
  of the graph, the importer, the cost functions, the spanning tree phases (`MinSTPhase`,
  `MaxSTPhase`; `MaxSTPhase` is not reachable through JSON, see `SporeMetaDataProvider`), the
  execution phases and `ShrinkTree`;
* `spore.provider`: the providers, including the elk-rs test `scanline_overlap_removal_test`;
* `spore.fixtures`: `tests/fixtures/spore/<name>.json` laid out through `Elk.Api.layoutJson` against
  the elk-rs oracle output `<name>.expected.json` (byte-exact). Fixtures whose elk-rs result is
  nondeterministic (it iterates a `HashSet<TEdge>`, see `NaiveMinST`) carry the other outcomes
  observed in 60 oracle runs as `<name>.alt<k>.json`; the Lean (insertion order) result must equal
  one of them. Set `SPORE_DUMP_DIR` to write the Lean outputs as `<name>.lean.json` there.

Not testable against elk-rs: `sporeCompaction` with `underlyingLayoutAlgorithm = sporeOverlap` (and
the converse) recurses forever in elk-rs and Java (the underlying option is read from the very
same graph again). -/
namespace Tests.Spore

open Tests Elk Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Data Elk.Core.Alg
open Elk.Alg.Common Elk.Alg.Common.Spore Elk.Alg.Spore Elk.Alg.Spore.Graph Elk.Alg.Spore.Options
open Elk.Alg.Spore.P2ProcessingOrder Elk.Alg.Spore.P3Execution

private def kv (x y : Float) : KVector := ⟨x, y⟩
private def rect (x y w h : Float) : ElkRectangle := ElkRectangle.ofValues x y w h
/-- A node centered in its rectangle (like the importer). -/
private def node (x y w h : Float) : Node := Node.new (kv (x + w / 2) (y + h / 2)) (rect x y w h)

/-- Runs a SPOrE action on a graph. -/
private def runS {α : Type} (x : SporeM α) (g : Graph) : IO (α × Graph) := SporeM.run x g

/-- A graph with the given vertices (index map built). -/
private def mkGraph (vertices : Array Node) (cost : SpanningTreeCostFunction := .centerDistance)
    (tree : TreeConstructionStrategy := .minimumSpanningTree) : Graph :=
  Graph.rebuildIndexMap { Graph.new cost tree .depthFirst with vertices }

/-! ### Options and metadata -/

def optionsSuite : Suite := suite "spore.options" do
  checkEq "overlap algorithm id" SporeOverlapRemovalOptions.ALGORITHM_ID "org.eclipse.elk.sporeOverlap"
  checkEq "compaction algorithm id" SporeCompactionOptions.ALGORITHM_ID "org.eclipse.elk.sporeCompaction"
  checkEq "underlying id" SporeCommonOptions.UNDERLYING_LAYOUT_ALGORITHM.id "org.eclipse.elk.underlyingLayoutAlgorithm"
  checkEq "structure id" SporeCommonOptions.STRUCTURE_EXTRACTION_STRATEGY.id
    "org.eclipse.elk.structure.structureExtractionStrategy"
  checkEq "tree construction id" SporeCommonOptions.PROCESSING_ORDER_TREE_CONSTRUCTION.id
    "org.eclipse.elk.processingOrder.treeConstruction"
  checkEq "cost function id" SporeCommonOptions.PROCESSING_ORDER_SPANNING_TREE_COST_FUNCTION.id
    "org.eclipse.elk.processingOrder.spanningTreeCostFunction"
  checkEq "preferred root id" SporeCommonOptions.PROCESSING_ORDER_PREFERRED_ROOT.id
    "org.eclipse.elk.processingOrder.preferredRoot"
  checkEq "root selection id" SporeCommonOptions.PROCESSING_ORDER_ROOT_SELECTION.id
    "org.eclipse.elk.processingOrder.rootSelection"
  checkEq "compaction strategy id" SporeCommonOptions.COMPACTION_COMPACTION_STRATEGY.id
    "org.eclipse.elk.compaction.compactionStrategy"
  checkEq "orthogonal id" SporeCommonOptions.COMPACTION_ORTHOGONAL.id "org.eclipse.elk.compaction.orthogonal"
  checkEq "max iterations id" SporeCommonOptions.OVERLAP_REMOVAL_MAX_ITERATIONS.id
    "org.eclipse.elk.overlapRemoval.maxIterations"
  checkEq "run scanline id" SporeCommonOptions.OVERLAP_REMOVAL_RUN_SCANLINE.id
    "org.eclipse.elk.overlapRemoval.runScanline"
  checkEq "underlying default" SporeCommonOptions.UNDERLYING_LAYOUT_ALGORITHM.default none
  checkEq "preferred root default" SporeCommonOptions.PROCESSING_ORDER_PREFERRED_ROOT.default none
  checkEqR "structure default" SporeCommonOptions.STRUCTURE_EXTRACTION_STRATEGY.default
    (some StructureExtractionStrategy.delaunayTriangulation)
  checkEqR "tree construction default" SporeCommonOptions.PROCESSING_ORDER_TREE_CONSTRUCTION.default
    (some TreeConstructionStrategy.minimumSpanningTree)
  checkEqR "cost function default" SporeCommonOptions.PROCESSING_ORDER_SPANNING_TREE_COST_FUNCTION.default
    (some SpanningTreeCostFunction.circleUnderlap)
  checkEqR "root selection default" SporeCommonOptions.PROCESSING_ORDER_ROOT_SELECTION.default
    (some RootSelection.centerNode)
  checkEqR "compaction strategy default" SporeCommonOptions.COMPACTION_COMPACTION_STRATEGY.default
    (some CompactionStrategy.depthFirst)
  checkEq "orthogonal default" SporeCommonOptions.COMPACTION_ORTHOGONAL.default (some false)
  checkEq "max iterations default" SporeCommonOptions.OVERLAP_REMOVAL_MAX_ITERATIONS.default (some 64)
  checkEq "run scanline default" SporeCommonOptions.OVERLAP_REMOVAL_RUN_SCANLINE.default (some true)
  -- aliases of the algorithm option classes
  checkEq "padding alias" SporeCompactionOptions.PADDING.id CoreOptions.PADDING.id
  checkEq "spacing alias" SporeOverlapRemovalOptions.SPACING_NODE_NODE.id CoreOptions.SPACING_NODE_NODE.id
  checkEq "debug alias" SporeOverlapRemovalOptions.DEBUG_MODE.id CoreOptions.DEBUG_MODE.id
  -- Java enum names / ordinals
  checkEq "cost function names"
    ((ElkEnum.values : Array SpanningTreeCostFunction).map ElkEnum.javaName)
    #["CENTER_DISTANCE", "CIRCLE_UNDERLAP", "RECTANGLE_UNDERLAP", "INVERTED_OVERLAP", "MINIMUM_ROOT_DISTANCE"]
  checkEq "tree construction names"
    ((ElkEnum.values : Array TreeConstructionStrategy).map ElkEnum.javaName)
    #["MINIMUM_SPANNING_TREE", "MAXIMUM_SPANNING_TREE"]
  checkEq "root selection names" ((ElkEnum.values : Array RootSelection).map ElkEnum.javaName) #["FIXED", "CENTER_NODE"]
  checkEq "structure names" ((ElkEnum.values : Array StructureExtractionStrategy).map ElkEnum.javaName)
    #["DELAUNAY_TRIANGULATION"]
  checkEq "compaction names" ((ElkEnum.values : Array CompactionStrategy).map ElkEnum.javaName) #["DEPTH_FIRST"]
  checkEq "overlap removal names" ((ElkEnum.values : Array OverlapRemovalStrategy).map ElkEnum.javaName) #["GROW_TREE"]
  checkEq "phase count" (ElkEnum.count (α := SPOrEPhases)) 3
  checkEq "phase ordinals" ((ElkEnum.values : Array SPOrEPhases).map ElkEnum.ordinal) #[0, 1, 2]

/-- `value` is a stored `bool` default. -/
private def isBool (v : Option PropValue) (b : Bool) : Bool :=
  match v with
  | some (.bool x) => x == b
  | _ => false

/-- `value` is a stored `int` default. -/
private def isInt (v : Option PropValue) (i : Int) : Bool :=
  match v with
  | some (.int x) => x == i
  | _ => false

/-- Looks up an option by id; reports a failure (and returns a dummy) if missing. -/
private def opt (id : String) : TestM LayoutOptionData := do
  match ← LayoutMetaDataService.getOptionData id with
  | some d => return d
  | none =>
    report s!"option {id} registered" false
    return { id }

def metaSuite : Suite := suite "spore.meta" do
  Elk.Api.ensureInitialized
  let overlap ← LayoutMetaDataService.getAlgorithmData SporeOverlapRemovalOptions.ALGORITHM_ID
  let compaction ← LayoutMetaDataService.getAlgorithmData SporeCompactionOptions.ALGORITHM_ID
  match overlap with
  | none => report "overlap algorithm registered" false "missing"
  | some a =>
    checkEq "overlap name" a.name "ELK SPOrE Overlap Removal"
    checkEq "overlap bundle" a.definingBundleId (some "org.eclipse.elk.alg.spore")
    checkEq "overlap preview" a.previewImagePath (some "images/overlap-removal.png")
    checkEq "overlap category" a.categoryId none
    checkEq "overlap known options"
      a.knownOptionIds
      #["org.eclipse.elk.underlyingLayoutAlgorithm", "org.eclipse.elk.padding", "org.eclipse.elk.spacing.nodeNode",
        "org.eclipse.elk.structure.structureExtractionStrategy", "org.eclipse.elk.overlapRemoval.maxIterations",
        "org.eclipse.elk.overlapRemoval.runScanline", "org.eclipse.elk.debugMode"]
    checkEq "overlap padding default" (a.defaultValue CoreOptions.PADDING) (some (ElkPadding.ofAny 8.0))
    checkEq "overlap spacing default" (a.defaultValue CoreOptions.SPACING_NODE_NODE) (some 8.0)
    checkEq "overlap debug default" (a.defaultValue CoreOptions.DEBUG_MODE) (some false)
  match compaction with
  | none => report "compaction algorithm registered" false "missing"
  | some a =>
    checkEq "compaction name" a.name "ELK SPOrE Compaction"
    checkEq "compaction preview" a.previewImagePath (some "images/compaction-example.png")
    checkEq "compaction known options"
      a.knownOptionIds
      #["org.eclipse.elk.underlyingLayoutAlgorithm", "org.eclipse.elk.processingOrder.treeConstruction",
        "org.eclipse.elk.processingOrder.spanningTreeCostFunction", "org.eclipse.elk.processingOrder.preferredRoot",
        "org.eclipse.elk.processingOrder.rootSelection", "org.eclipse.elk.padding", "org.eclipse.elk.spacing.nodeNode",
        "org.eclipse.elk.structure.structureExtractionStrategy", "org.eclipse.elk.compaction.compactionStrategy",
        "org.eclipse.elk.compaction.orthogonal", "org.eclipse.elk.debugMode"]
    checkEq "compaction padding default" (a.defaultValue CoreOptions.PADDING) (some (ElkPadding.ofAny 8.0))
  -- the ten registered options
  let u ← opt "org.eclipse.elk.underlyingLayoutAlgorithm"
  checkEqR "underlying type" u.type LayoutOptionType.string
  checkEq "underlying name" u.name "Underlying Layout Algorithm"
  checkEqR "underlying visibility" u.visibility LayoutOptionVisibility.visible
  checkEq "underlying group" u.group ""
  check "underlying has no default" u.defaultValue.isNone
  check "underlying targets" (u.targets.contains .parents && !u.targets.contains .nodes)
  let s ← opt "org.eclipse.elk.structure.structureExtractionStrategy"
  checkEqR "structure type" s.type LayoutOptionType.enum
  checkEqR "structure visibility" s.visibility LayoutOptionVisibility.advanced
  checkEq "structure group" s.group "structure"
  -- Rust: enum options of this plugin have neither choices nor a parser
  check "structure has no parser" s.parser.isNone
  check "structure cannot be parsed" (!s.canParseValue)
  check "structure no choices" s.choices.isEmpty
  let t ← opt "org.eclipse.elk.processingOrder.treeConstruction"
  check "tree construction string value is not parsed" (t.parseValue "MAXIMUM_SPANNING_TREE").isNone
  checkEq "tree construction name" t.name "Tree Construction Strategy"
  checkEqR "tree construction default" (t.defaultValue.bind PropCodec.dec) (some TreeConstructionStrategy.minimumSpanningTree)
  let c ← opt "org.eclipse.elk.processingOrder.spanningTreeCostFunction"
  checkEqR "cost function visibility" c.visibility LayoutOptionVisibility.visible
  checkEq "cost function name" c.name "Cost Function for Spanning Tree"
  let r ← opt "org.eclipse.elk.processingOrder.preferredRoot"
  checkEq "preferred root name" r.name "Root node for spanning tree construction"
  checkEqR "preferred root type" r.type LayoutOptionType.string
  let o ← opt "org.eclipse.elk.compaction.orthogonal"
  checkEqR "orthogonal type" o.type LayoutOptionType.boolean
  check "orthogonal default" (isBool o.defaultValue false)
  checkEq "orthogonal group" o.group "compaction"
  let m ← opt "org.eclipse.elk.overlapRemoval.maxIterations"
  checkEqR "max iterations type" m.type LayoutOptionType.int
  check "max iterations default" (isInt m.defaultValue 64)
  checkEq "max iterations name" m.name "Upper limit for iterations of overlap removal"
  checkEq "max iterations description" m.description ""
  check "max iterations parses" ((m.parseValue "5").isSome)
  let l ← opt "org.eclipse.elk.overlapRemoval.runScanline"
  checkEq "run scanline name" l.name "Whether to run a supplementary scanline overlap check."
  check "run scanline default" (isBool l.defaultValue true)
  checkEqR "run scanline visibility" l.visibility LayoutOptionVisibility.advanced
  -- layout providers
  check "overlap provider registered" (← LayoutProvider.isRegistered SporeOverlapRemovalOptions.ALGORITHM_ID)
  check "compaction provider registered" (← LayoutProvider.isRegistered SporeCompactionOptions.ALGORITHM_ID)
  -- the metadata provider on a fresh registry
  let reg := SporeMetaDataProvider.metaDataProvider.apply {}
  checkEq "provider algorithms" reg.algorithms.size 2
  checkEq "provider options" reg.options.size 10
  checkEq "provider option supports" reg.optionSupport.size 18
  checkEq "provider dependencies" reg.dependencies.size 0

/-! ### Graph, cost functions, phases -/

def graphSuite : Suite := suite "spore.graph" do
  let vs := #[node 0 0 10 10, node 20 0 10 10, node 40 0 10 10]
  let g := mkGraph vs
  checkEq "index of first" (g.nodeIndexMap.get? (kv 5 5)) (some 0)
  checkEq "index of third" (g.nodeIndexMap.get? (kv 45 5)) (some 2)
  check "nodeForVertex" ((g.nodeForVertex (kv 25 5)).map (·.rect.x) == some 20.0)
  check "nodeForVertex unknown" (g.nodeForVertex (kv 1 1)).isNone
  check "no preferred root" g.preferredRoot.isNone
  let g2 := { g with preferredRootIndex := some 1 }
  check "preferred root" ((g2.preferredRoot.map (·.rect.x)) == some 20.0)
  checkEq "preferred root out of range" ({ g with preferredRootIndex := some 7 }).preferredRoot.isNone true
  -- sync_vertices_from_tree: copies vertex and rect (looked up by originalVertex)
  let moved := (vs[1]!).translate (kv 7 3)
  let tree : Tree Node := { node := vs[0]!, children := #[Tree.new moved] }
  let synced := { g with tree := some tree }.syncVerticesFromTree
  check "sync moved vertex" (synced.vertices[1]!.vertex == kv 32 8)
  check "sync moved rect" (synced.vertices[1]!.rect == rect 27 3 10 10)
  check "sync keeps original vertex" (synced.vertices[1]!.originalVertex == kv 25 5)
  check "sync leaves nodes that are not in the tree" (synced.vertices[2]!.vertex == kv 45 5)
  check "sync without tree" ((g.syncVerticesFromTree).vertices[1]!.vertex == kv 25 5)
  -- properties
  let p := g.setProperty InternalProperties.OVERLAPS_EXISTED false
  checkEq "property set" (p.getProperty InternalProperties.OVERLAPS_EXISTED) (some false)
  checkEq "property default" (g.getProperty InternalProperties.OVERLAPS_EXISTED) (some true)
  checkEq "debug default" (g.getProperty InternalProperties.DEBUG_SVG) (some false)
  -- duplicated original vertices: the later vertex wins in the index map
  let dup := mkGraph #[node 0 0 10 10, node 0 0 20 20]
  checkEq "duplicate original vertex" (dup.nodeIndexMap.get? (kv 5 5)) (some 0)

def costSuite : Suite := suite "spore.cost" do
  let n1 := node 0 0 10 10
  let n2 := node 20 0 10 10
  let edge := TEdge.new n1.originalVertex n2.originalVertex
  let cost (f : SpanningTreeCostFunction) (root : Option Nat := none) (vs : Array Node := #[n1, n2]) (e : TEdge := edge) :=
    GraphCostFunction.new { mkGraph vs f with preferredRootIndex := root } e
  checkFloat "CENTER_DISTANCE" (cost .centerDistance) 20.0
  -- distance of the centers minus the distances of the centers to the rectangle positions (top left)
  checkFloat "CIRCLE_UNDERLAP" (cost .circleUnderlap) (20.0 - Float.sqrt 50.0 - Float.sqrt 50.0)
  checkFloat "RECTANGLE_UNDERLAP" (cost .rectangleUnderlap) 10.0
  checkFloat "INVERTED_OVERLAP separated" (cost .invertedOverlap) 10.0
  checkFloat "MINIMUM_ROOT_DISTANCE without root" (cost .minimumRootDistance) 20.0
  checkFloat "MINIMUM_ROOT_DISTANCE root 0" (cost .minimumRootDistance (root := some 0)) 0.0
  checkFloat "MINIMUM_ROOT_DISTANCE root 1" (cost .minimumRootDistance (root := some 1)) 0.0
  -- overlapping rectangles: -(overlap - 1) * center distance
  let n3 := node 5 0 10 10
  let e3 := TEdge.new n1.originalVertex n3.originalVertex
  checkFloat "INVERTED_OVERLAP overlapping" (cost .invertedOverlap (vs := #[n1, n3]) (e := e3)) (-5.0)
  -- unknown vertices fall back to the center distance
  let unknown := TEdge.new (kv 5 5) (kv 5 105)
  checkFloat "CIRCLE_UNDERLAP unknown" (cost .circleUnderlap (e := unknown)) 100.0
  checkFloat "RECTANGLE_UNDERLAP unknown" (cost .rectangleUnderlap (e := unknown)) 100.0
  checkFloat "INVERTED_OVERLAP unknown" (cost .invertedOverlap (e := unknown)) 100.0
  checkFloat "inverted" (InvertedCostFunction.new (GraphCostFunction.new (mkGraph #[n1, n2])) edge) (-20.0)

/-- Preorder `vertex.x` values of the spanning tree of a graph. -/
private def treeXs (g : Graph) : Array Float :=
  match g.tree with
  | some t => t.preorder.map (·.vertex.x)
  | none => #[]

def spanningTreeSuite : Suite := suite "spore.p2" do
  let vs := #[node (-1) (-1) 2 2, node 9 (-1) 2 2, node 19 (-1) 2 2, node 29 (-1) 2 2]
  let p (i : Nat) := (vs[i]!).originalVertex
  let edges := #[TEdge.new (p 0) (p 1), TEdge.new (p 0) (p 2), TEdge.new (p 0) (p 3),
    TEdge.new (p 1) (p 2), TEdge.new (p 1) (p 3), TEdge.new (p 2) (p 3)]
  let g := { mkGraph vs with tEdges := some edges, preferredRootIndex := some 0 }
  let (_, mn) ← runS (MinSTPhase.process () ProgressMonitor.null) g
  checkEq "MinST chain" (treeXs mn) #[0.0, 10.0, 20.0, 30.0]
  let (_, mx) ← runS (MaxSTPhase.process () ProgressMonitor.null) g
  checkEq "MaxST star" (treeXs mx) #[0.0, 30.0, 10.0, 20.0]
  -- another root: vertex 2
  let (_, mn2) ← runS (MinSTPhase.process () ProgressMonitor.null) { g with preferredRootIndex := some 2 }
  checkEq "MinST root 2" (treeXs mn2) #[20.0, 10.0, 0.0, 30.0]
  -- without a preferred root the first vertex is the root
  let (_, mn3) ← runS (MinSTPhase.process () ProgressMonitor.null) { g with preferredRootIndex := none }
  checkEq "MinST default root" (treeXs mn3) #[0.0, 10.0, 20.0, 30.0]
  -- without edges the graph is untouched, without vertices too
  let (_, none1) ← runS (MinSTPhase.process () ProgressMonitor.null) { g with tEdges := none }
  check "MinST without edges" none1.tree.isNone
  let (_, none2) ← runS (MinSTPhase.process () ProgressMonitor.null) (mkGraph #[])
  check "MinST without vertices" none2.tree.isNone
  let (_, none3) ← runS (MaxSTPhase.process () ProgressMonitor.null) (mkGraph #[])
  check "MaxST without vertices" none3.tree.isNone
  -- Delaunay triangulation phase: collinear points give a connected edge set; the edges are added to
  -- the existing ones
  let (_, del) ← runS (P1Structure.DelaunayTriangulationPhase.process () ProgressMonitor.null) (mkGraph vs)
  check "Delaunay edges" ((del.tEdges.map (·.size)).getD 0 >= 3)
  let pre := #[TEdge.new (p 0) (p 3)]
  let (_, del2) ← runS (P1Structure.DelaunayTriangulationPhase.process () ProgressMonitor.null)
    { mkGraph vs with tEdges := some pre }
  check "Delaunay keeps existing edges first" ((del2.tEdges.bind (·[0]?)).map (· == pre[0]!) == some true)
  check "Delaunay extends existing edges" ((del2.tEdges.map (·.size)).getD 0 >= (del.tEdges.map (·.size)).getD 0)
  -- phase factories
  let tc := TreeConstructionStrategy.maximumSpanningTree.factory
  checkEq "factory key" tc.key (some ("TreeConstructionStrategy", 1))
  let phase ← tc.create
  checkEq "factory phase name" phase.name "MaxSTPhase"
  checkEq "min factory phase name" (← TreeConstructionStrategy.minimumSpanningTree.factory.create).name "MinSTPhase"
  checkEq "structure factory phase name"
    (← StructureExtractionStrategy.delaunayTriangulation.factory.create).name "DelaunayTriangulationPhase"
  checkEq "compaction factory phase name" (← CompactionStrategy.depthFirst.factory.create).name "ShrinkTreeCompactionPhase"
  checkEq "overlap factory phase name" (← OverlapRemovalStrategy.growTree.factory.create).name "GrowTreePhase"

def executionSuite : Suite := suite "spore.p3" do
  -- two overlapping nodes: the child moves along the center line until the rectangles touch
  let a := node 0 0 20 20
  let b := node 10 0 20 20
  let g := { mkGraph #[a, b] with tree := some { node := a, children := #[Tree.new b] } }
  let (_, grown) ← runS (GrowTreePhase.process () ProgressMonitor.null) g
  match grown.tree with
  | none => report "grow tree: tree" false "missing"
  | some t =>
    check "grow tree: root unchanged" (t.node.rect == a.rect)
    let c := t.children[0]!.node
    check "grow tree: child touches the root" (c.rect == rect 20 0 20 20)
    check "grow tree: child vertex" (c.vertex == kv 30 10)
    check "grow tree: child original vertex" (c.originalVertex == kv 20 10)
  checkEq "grow tree: overlaps existed" (grown.getProperty InternalProperties.OVERLAPS_EXISTED) (some true)
  -- separate nodes: no overlap, nothing moves
  let far := node 100 0 20 20
  let g2 := { mkGraph #[a, far] with tree := some { node := a, children := #[Tree.new far] } }
  let (_, grown2) ← runS (GrowTreePhase.process () ProgressMonitor.null) g2
  checkEq "grow tree: no overlap" (grown2.getProperty InternalProperties.OVERLAPS_EXISTED) (some false)
  check "grow tree: far node stays" ((grown2.tree.map (·.children[0]!.node.rect)) == some far.rect)
  -- a grandchild is first translated by the displacement of its parent
  let c := node 20 0 20 20
  let tree3 : Tree Node := { node := a, children := #[{ node := b, children := #[Tree.new c] }] }
  let (_, grown3) ← runS (GrowTreePhase.process () ProgressMonitor.null) { mkGraph #[a, b, c] with tree := some tree3 }
  match grown3.tree with
  | none => report "grow tree chain: tree" false "missing"
  | some t =>
    let child := t.children[0]!
    check "grow tree chain: child" (child.node.rect == rect 20 0 20 20)
    -- the grandchild follows its parent by +10 (translated to x = 30) and then overlaps it by
    -- 10: it is moved along the center line until it touches the parent
    check "grow tree chain: grandchild touches" (child.children[0]!.node.rect.x == 40.0)
  -- no tree: nothing happens and the property is not set
  let (_, untouched) ← runS (GrowTreePhase.process () ProgressMonitor.null) (mkGraph #[a])
  check "grow tree without tree" (untouched.props.get? InternalProperties.OVERLAPS_EXISTED).isNone
  -- compaction of a far child
  let g4 := { mkGraph #[a, far] with tree := some { node := a, children := #[Tree.new far] } }
  let (_, compacted) ← runS (ShrinkTreeCompactionPhase.process () ProgressMonitor.null) g4
  check "compaction: child moves to the parent" ((compacted.tree.map (·.children[0]!.node.rect.x)) == some 20.0)
  let (_, nothing) ← runS (ShrinkTreeCompactionPhase.process () ProgressMonitor.null) (mkGraph #[a])
  check "compaction without tree" nothing.tree.isNone

/-! ### Importer, ShrinkTree, providers -/

/-- A root with children `(x, y, w, h)`; the root options are set by `f`. -/
private def mkElk (children : Array (Float × Float × Float × Float))
    (f : ElkGraph → NodeId → ElkGraph := fun g _ => g) : ElkGraph × NodeId × Array NodeId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let mut g := g
  let mut ids : Array NodeId := #[]
  for (x, y, w, h) in children do
    let (g', n) := g.createNode (some root)
    g := g'.modifyNode n fun nd => { nd with x := x, y := y, width := w, height := h }
    ids := ids.push n
  g := g.modifyNode root fun nd => { nd with width := 500.0, height := 500.0 }
  return (f g root, root, ids)

def importerSuite : Suite := suite "spore.importer" do
  Elk.Api.ensureInitialized
  let (g, root, ids) := mkElk #[(0.0, 0.0, 10.0, 10.0), (100.0, 0.0, 20.0, 40.0), (200.0, 100.0, 10.0, 10.0)]
    fun g root => g.setNodeProp root CoreOptions.SPACING_NODE_NODE 10.0
  let importer ← ElkGraphImporter.new
  let (graph, _) ← ElkM.run (importer.importGraph root) g
  checkEq "vertex count" graph.vertices.size 3
  check "vertex centers" (graph.vertices.map (·.originalVertex) == #[kv 5 5, kv 110 20, kv 205 105])
  -- rect = bounds enlarged by spacing.nodeNode / 2 on every side
  check "rect" (graph.vertices[0]!.rect == rect (-5) (-5) 20 20)
  check "rect 2" (graph.vertices[1]!.rect == rect 95 (-5) 30 50)
  check "orthogonal default" (!graph.orthogonalCompaction)
  checkEqR "default cost function" graph.costFunction SpanningTreeCostFunction.circleUnderlap
  checkEqR "default tree construction" graph.treeConstructionStrategy TreeConstructionStrategy.minimumSpanningTree
  checkEq "debug svg" (graph.getProperty InternalProperties.DEBUG_SVG) (some false)
  -- CENTER_NODE (default): the root center is (250, 250); the closest vertex is the third one
  checkEq "center node root" graph.preferredRootIndex (some 2)
  checkEq "index map" (graph.nodeForVertex (kv 110 20)).isSome true
  -- FIXED without a preferred root: the first vertex
  let (gf, rootf, _) := mkElk #[(0.0, 0.0, 10.0, 10.0), (100.0, 0.0, 20.0, 40.0)] fun g root =>
    g.setNodeProp root SporeCompactionOptions.PROCESSING_ORDER_ROOT_SELECTION RootSelection.fixed
  let (graphf, _) ← ElkM.run ((← ElkGraphImporter.new).importGraph rootf) gf
  checkEq "fixed without id" graphf.preferredRootIndex (some 0)
  -- FIXED with a preferred root id
  let (gi, rooti, idsi) := mkElk #[(0.0, 0.0, 10.0, 10.0), (100.0, 0.0, 20.0, 40.0), (300.0, 0.0, 10.0, 10.0)]
    fun g root =>
      (g.setNodeProp root SporeCompactionOptions.PROCESSING_ORDER_ROOT_SELECTION RootSelection.fixed).setNodeProp root
        SporeCompactionOptions.PROCESSING_ORDER_PREFERRED_ROOT "second"
  let gi := gi.modifyNode idsi[1]! fun n => { n with identifier := some "second" }
  let (graphi, _) ← ElkM.run ((← ElkGraphImporter.new).importGraph rooti) gi
  checkEq "fixed with id" graphi.preferredRootIndex (some 1)
  -- FIXED with an unknown id: no preferred root
  let (gu, rootu, _) := mkElk #[(0.0, 0.0, 10.0, 10.0)] fun g root =>
    (g.setNodeProp root SporeCompactionOptions.PROCESSING_ORDER_ROOT_SELECTION RootSelection.fixed).setNodeProp root
      SporeCompactionOptions.PROCESSING_ORDER_PREFERRED_ROOT "nobody"
  let (graphu, _) ← ElkM.run ((← ElkGraphImporter.new).importGraph rootu) gu
  checkEq "fixed with unknown id" graphu.preferredRootIndex none
  -- identical centers are wiggled apart (Random(0), amount 0.001)
  let (gd, rootd, _) := mkElk #[(10.0, 10.0, 20.0, 20.0), (10.0, 10.0, 20.0, 20.0), (10.0, 10.0, 20.0, 20.0)]
  let (graphd, _) ← ElkM.run ((← ElkGraphImporter.new).importGraph rootd) gd
  let centers := graphd.vertices.map (·.originalVertex)
  check "wiggle: first stays" (centers[0]! == kv 20 20)
  check "wiggle: distinct" (centers[1]! != centers[0]! && centers[2]! != centers[1]! && centers[2]! != centers[0]!)
  check "wiggle: small" (centers.all fun c => (c.x - 20.0).abs <= 0.002 && (c.y - 20.0).abs <= 0.002)
  -- no children: an empty graph without a preferred root
  let (ge, roote, _) := mkElk #[]
  let (graphe, _) ← ElkM.run ((← ElkGraphImporter.new).importGraph roote) ge
  check "empty graph" (graphe.vertices.isEmpty && graphe.preferredRootIndex.isNone)
  -- update_graph: original vertices move to the rect centers, edges and tree are cleared
  let imp ← ElkGraphImporter.new
  let (graph2, _) ← ElkM.run (imp.importGraph root) g
  let moved := { graph2 with
    vertices := graph2.vertices.set! 0 { (graph2.vertices[0]!).translate (kv 4 6) with originalVertex := kv 5 5 },
    tEdges := some #[TEdge.new (kv 1 1) (kv 2 2)], tree := some (Tree.new graph2.vertices[0]!) }
  let updated ← imp.updateGraph moved
  check "update: edges cleared" updated.tEdges.isNone
  check "update: tree cleared" updated.tree.isNone
  check "update: original vertex is the rect center" (updated.vertices[0]!.originalVertex == kv 9 11)
  check "update: untouched vertex" (updated.vertices[1]!.originalVertex == updated.vertices[1]!.rect.center)
  checkEq "update: index map" (updated.nodeIndexMap.get? (kv 9 11)) (some 0)
  -- apply_positions: sets locations, resizes the root and routes the edges
  let _ := ids
  let (g3, root3, ids3) := mkElk #[(0.0, 0.0, 10.0, 10.0), (100.0, 0.0, 10.0, 10.0)] fun g root =>
    (g.setNodeProp root SporeCompactionOptions.PADDING (ElkPadding.ofAny 5.0)).setNodeProp root
      SporeCompactionOptions.SPACING_NODE_NODE 0.0
  let (g3, e) := ElkGraphUtil.createSimpleEdge g3 (.node ids3[0]!) (.node ids3[1]!)
  let imp3 ← ElkGraphImporter.new
  let (_, g3) ← ElkM.run (do
    let graph ← imp3.importGraph root3
    let shifted := { graph with vertices := graph.vertices.set! 1 ((graph.vertices[1]!).translate (kv (-50) 20)) }
    imp3.applyPositions shifted) g3
  checkFloat "apply: node 0 x" (g3.node ids3[0]!).x 5.0
  checkFloat "apply: node 0 y" (g3.node ids3[0]!).y 5.0
  checkFloat "apply: node 1 x" (g3.node ids3[1]!).x 55.0
  checkFloat "apply: node 1 y" (g3.node ids3[1]!).y 25.0
  checkFloat "apply: root width" (g3.node root3).width 70.0
  checkFloat "apply: root height" (g3.node root3).height 40.0
  match (g3.edge e).sections[0]? with
  | none => report "apply: edge section" false "missing"
  | some s =>
    let sec := g3.edgeSection s
    -- centers (10,10) and (60,30): the direction (50,20) is clipped to the 10x10 rectangle (scale 0.1),
    -- the start becomes (15,12); the way back (-45,-18) is clipped the same way: the end is (55,28)
    checkFloat "apply: edge start x" sec.startX 15.0
    checkFloat "apply: edge start y" sec.startY 12.0
    checkFloat "apply: edge end x" sec.endX 55.0
    checkFloat "apply: edge end y" sec.endY 28.0

def shrinkSuite : Suite := suite "spore.shrink" do
  let a := node 0 0 20 20
  let far := node 200 0 20 20
  let g := { mkGraph #[a, far] .centerDistance with preferredRootIndex := some 0 }
  let st ← ShrinkTree.new
  let out ← st.shrink g ProgressMonitor.null
  checkFloat "shrink: far node moved next to the root" out.vertices[1]!.rect.x 20.0
  checkFloat "shrink: root stays" out.vertices[0]!.rect.x 0.0
  checkFloat "shrink: vertex follows" out.vertices[1]!.vertex.x 30.0
  -- a single vertex is not processed (but synchronized: no tree)
  let single := { mkGraph #[a] with preferredRootIndex := some 0 }
  let out1 ← st.shrink single ProgressMonitor.null
  check "single vertex unchanged" (out1.vertices[0]!.rect == a.rect && out1.tree.isNone)
  -- the same assembler can be used again (processors are rebuilt)
  let out2 ← st.shrink g ProgressMonitor.null
  checkFloat "shrink twice" out2.vertices[1]!.rect.x 20.0
  -- orthogonal compaction moves along one axis only
  let diag := node 200 200 20 20
  let go := { mkGraph #[a, diag] .centerDistance with preferredRootIndex := some 0, orthogonalCompaction := true }
  let outo ← st.shrink go ProgressMonitor.null
  check "orthogonal: moves along an axis"
    ((outo.vertices[1]!.rect.x == 200.0) != (outo.vertices[1]!.rect.y == 200.0))
  -- canceled monitor: returns at once (no sync)
  let canceled ← ProgressMonitor.basic
  canceled.cancel
  let outc ← st.shrink g canceled
  check "canceled: no synchronization" (outc.vertices[1]!.rect.x == 200.0)

/-- `scanline_overlap_removal_test.rs` `build_graph`. -/
private def scanlineGraph (runScanline : Bool) : ElkGraph × NodeId × Array NodeId :=
  mkElk #[(0.0, 30.0, 160.0, 20.0), (150.0, 40.0, 160.0, 20.0), (150.0, 0.0, 20.0, 20.0), (150.0, 70.0, 20.0, 20.0)]
    fun g root => g.setNodeProp root SporeOverlapRemovalOptions.OVERLAP_REMOVAL_RUN_SCANLINE runScanline

/-- `has_overlaps`: some pair of nodes overlaps (negative shortest distance). -/
private def hasOverlaps (g : ElkGraph) (root : NodeId) : Bool := Id.run do
  let nodes := (g.node root).children.map fun n =>
    let nd := g.node n
    rect nd.x nd.y nd.width nd.height
  for i in [0:nodes.size] do
    for j in [i + 1:nodes.size] do
      if (nodes[i]!).intersects nodes[j]! && ElkMath.shortestDistance nodes[i]! nodes[j]! < 0.0 then
        return true
  return false

def providerSuite : Suite := suite "spore.provider" do
  Elk.Api.ensureInitialized
  -- scanline_overlap_removal_test (with the scanline check)
  for runScanline in [true, false] do
    let (g, root, _) := scanlineGraph runScanline
    check s!"overlapping before (scanline {runScanline})" (hasOverlaps g root)
    let (_, g) ← ElkM.run (OverlapRemovalLayoutProvider.layout root (← ProgressMonitor.basic)) g
    check s!"scanline_overlap_removal_test: no overlaps after (scanline {runScanline})" (!hasOverlaps g root)
  -- the importer sees overlapping nodes
  let (g, root, _) := scanlineGraph true
  let (graph, _) ← ElkM.run ((← ElkGraphImporter.new).importGraph root) g
  let edges := (ScanlineOverlapCheck.new OverlapRemovalLayoutProvider.overlapHandler).sweep graph.vertices #[]
  check "scanline_overlap_removal_test: overlap edges found" (!edges.isEmpty)
  -- no iterations: nothing moves but the graph is placed
  let (g0, root0, ids0) := mkElk #[(0.0, 0.0, 20.0, 20.0), (5.0, 5.0, 20.0, 20.0)] fun g root =>
    g.setNodeProp root SporeOverlapRemovalOptions.OVERLAP_REMOVAL_MAX_ITERATIONS 0
  let (_, g0) ← ElkM.run (OverlapRemovalLayoutProvider.layout root0 ProgressMonitor.null) g0
  check "max iterations 0: still overlapping" (hasOverlaps g0 root0)
  check "max iterations 0: root options set"
    ((g0.node root0).props.get SporeCompactionOptions.PROCESSING_ORDER_TREE_CONSTRUCTION ==
      some TreeConstructionStrategy.minimumSpanningTree)
  check "max iterations 0: spanning tree cost function" ((g0.node root0).props.get?
    SporeCompactionOptions.PROCESSING_ORDER_SPANNING_TREE_COST_FUNCTION == some SpanningTreeCostFunction.invertedOverlap)
  let _ := ids0
  -- no children
  let (ge, roote, _) := mkElk #[]
  let (_, ge) ← ElkM.run (OverlapRemovalLayoutProvider.layout roote ProgressMonitor.null) ge
  checkFloat "no children: size unchanged" (ge.node roote).width 500.0
  let (_, ge) ← ElkM.run (ShrinkTreeLayoutProvider.layout roote ProgressMonitor.null) ge
  checkFloat "no children (compaction): size unchanged" (ge.node roote).width 500.0
  -- compaction through the provider; underlying algorithm "fixed" keeps the positions
  let (gc, rootc, idsc) := mkElk #[(0.0, 0.0, 20.0, 20.0), (200.0, 0.0, 20.0, 20.0)] fun g root =>
    ((g.setNodeProp root SporeCompactionOptions.UNDERLYING_LAYOUT_ALGORITHM "fixed").setNodeProp root
      SporeCompactionOptions.SPACING_NODE_NODE 0.0).setNodeProp root SporeCompactionOptions.PADDING (ElkPadding.ofAny 0.0)
  let (_, gc) ← ElkM.run (ShrinkTreeLayoutProvider.layout rootc (← ProgressMonitor.basic)) gc
  checkFloat "compaction: node 0" (gc.node idsc[0]!).x 0.0
  checkFloat "compaction: node 1" (gc.node idsc[1]!).x 20.0
  checkFloat "compaction: root width" (gc.node rootc).width 40.0
  checkFloat "compaction: root height" (gc.node rootc).height 20.0
  -- unknown / blank underlying algorithms are ignored
  for u in ["no.such.algorithm", "  "] do
    let (gu, rootu, idsu) := mkElk #[(0.0, 0.0, 20.0, 20.0), (200.0, 0.0, 20.0, 20.0)] fun g root =>
      ((g.setNodeProp root SporeCompactionOptions.UNDERLYING_LAYOUT_ALGORITHM u).setNodeProp root
        SporeCompactionOptions.SPACING_NODE_NODE 0.0).setNodeProp root SporeCompactionOptions.PADDING (ElkPadding.ofAny 0.0)
    let (_, gu) ← ElkM.run (ShrinkTreeLayoutProvider.layout rootu ProgressMonitor.null) gu
    checkFloat s!"underlying '{u}' ignored" (gu.node idsu[1]!).x 20.0
  -- through the engine
  let (gr, rootr, idsr) := mkElk #[(0.0, 0.0, 20.0, 20.0), (5.0, 5.0, 20.0, 20.0)] fun g root =>
    g.setNodeProp root CoreOptions.ALGORITHM SporeOverlapRemovalOptions.ALGORITHM_ID
  let (_, gr) ← ElkM.run (RecursiveGraphLayoutEngine.layout rootr ProgressMonitor.null) gr
  let _ := idsr
  check "engine: overlap removal" (!hasOverlaps gr rootr)

/-! ### Fixtures: elk-rs oracle output -/

/-- Fixture input names (`<name>.json` without the `.expected.json`/`.alt<k>.json` files), sorted. -/
private def fixtureNames (dir : System.FilePath) : IO (Array String) := do
  let entries ← System.FilePath.readDir dir
  let names := entries.filterMap fun e =>
    let f := e.fileName
    if f.endsWith ".json" && !f.endsWith ".expected.json" && ((f.splitOn ".alt").length == 1) then
      some (f.dropEnd ".json".length).toString
    else none
  return names.qsort (fun a b => a < b)

/-- Directory of the fixtures (`lake test` runs in the project root); `SPORE_FIXTURE_DIR` overrides it
(for ad-hoc oracle batteries). -/
private def defaultFixtureDir : System.FilePath := "tests/fixtures/spore"

/-- The alternative oracle outcomes `<name>.alt<k>.json` of a nondeterministic fixture. -/
private def alternatives (fixtureDir : System.FilePath) (name : String) : IO (Array String) := do
  let mut out := #[]
  for k in [1:64] do
    let p := fixtureDir / s!"{name}.alt{k}.json"
    if ← p.pathExists then out := out.push (← IO.FS.readFile p)
  return out

/-- `spore.fixtures`: `Elk.Api.layoutJson` on every `tests/fixtures/spore/<name>.json` must reproduce
`<name>.expected.json` (the elk-rs oracle output) byte-for-byte, or one of the `<name>.alt<k>.json`
outcomes of the nondeterministic fixtures. -/
def fixtureTests : Suite := suite "spore.fixtures" do
  let override ← IO.getEnv "SPORE_FIXTURE_DIR"
  let fixtureDir : System.FilePath := match override with
    | some d => System.FilePath.mk d
    | none => defaultFixtureDir
  let names ← fixtureNames fixtureDir
  check "fixtures found" (names.size >= (if override.isSome then 1 else 50))
  let dump ← IO.getEnv "SPORE_DUMP_DIR"
  for name in names do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    let expectedPath := fixtureDir / s!"{name}.expected.json"
    if !(← expectedPath.pathExists) then
      report s!"{name}: expected output exists" false s!"missing {expectedPath}"
    else
      let expected ← IO.FS.readFile expectedPath
      match ← Elk.Api.layoutJson input "{}" (lenient := false) (pretty := true) (sortKeys := true) with
      | .error e => report s!"{name}: layout" false e
      | .ok actual =>
        if let some dir := dump then
          IO.FS.createDirAll dir
          IO.FS.writeFile (System.FilePath.mk dir / s!"{name}.lean.json") actual
        let alts ← alternatives fixtureDir name
        if alts.isEmpty then
          checkJson s!"{name}: matches oracle" actual expected (tol := ELK_RS_FIXTURE_TOL)
        else
          check s!"{name}: matches one of the {alts.size + 1} oracle outcomes"
            ((#[expected] ++ alts).any (jsonEquivalent actual · ELK_RS_FIXTURE_TOL))

def suites : Array Tests.Suite :=
  #[optionsSuite, metaSuite, graphSuite, costSuite, spanningTreeSuite, executionSuite, importerSuite,
    shrinkSuite, providerSuite, fixtureTests]

end Tests.Spore
