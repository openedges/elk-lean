import Tests.Framework
import Elk.Api
import Elk.Alg.MrTree
/-!
# Tests of the tree layout foundation (`org.eclipse.elk.alg.mrtree`)

* `mrtree.meta`: the option and algorithm metadata of `MrTreeMetaDataProvider` (elk-rs
  `mrtree_meta_data_provider.rs`);
* `mrtree.graph`: the `TArena` relation methods (`TEdge::new`, `set_source`, `remove_outgoing` and the
  `direct_children` cache, `add_child`, `Display`);
* `mrtree.import`: `ElkGraphImporter.importGraph`/`applyLayout` on a JSON graph;
* `mrtree.components`: `ComponentsProcessor.split`/`pack`;
* `mrtree.intermediate`: every intermediate processor on hand-built tree graphs;
* `mrtree.treeutil`: `TreeUtil` and `InteractiveMrTreeGraphVisitor`.

The expected values are derived by hand from the Rust sources ("hand: …"); the elk-rs crate has no
unit tests for these parts (its only test, `mrtree_graph_size_test.rs`, needs the full layout).
-/
namespace Tests.MrTree

open Tests Elk Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Data
open Elk.Alg.MrTree Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options Elk.Alg.MrTree.Intermediate

/-! ### Helpers -/

/-- Substring test. -/
private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

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

/-- A node in graph `g` with id, top-left position and size. -/
private def mkNode (a : TArena) (g : TGraphId) (id : Int) (x y w h : Float) (label : Option String := none) :
    TArena × TNodeId :=
  let (a, n) := a.createNode id (some g) label
  (a.modifyNode n fun t => { t with position := ⟨x, y⟩, size := ⟨w, h⟩ }, n)

/-- An edge `s -> t` appended to the edges of graph `g`. -/
private def mkEdge (a : TArena) (g : TGraphId) (s t : TNodeId) : TArena × TEdgeId :=
  let (a, e) := a.createEdge s t
  (a.modifyGraph g fun x => { x with edges := x.edges.push e }, e)

/-- Sets `TREE_LEVEL`. -/
private def setLevel (a : TArena) (n : TNodeId) (l : Int) : TArena :=
  a.modifyNode n fun t => { t with props := t.props.set MrTreeOptions.TREE_LEVEL l }

/-- `TREE_LEVEL` of a node. -/
private def levelOf (a : TArena) (n : TNodeId) : Int :=
  ((a.node n).props.get MrTreeOptions.TREE_LEVEL).getD 0

/-- The tree `r -> a, r -> b, a -> c, a -> d` (ids 0..4, in this node order) with distinct sizes:
r 10x20, a 30x5, b 8x40, c 1x1, d 2x3. -/
private def tree : TArena × TGraphId × Array TNodeId := Id.run do
  let (a, g) := ({} : TArena).createGraph
  let (a, r) := mkNode a g 0 0 0 10 20
  let (a, na) := mkNode a g 1 0 0 30 5
  let (a, nb) := mkNode a g 2 0 0 8 40
  let (a, nc) := mkNode a g 3 0 0 1 1
  let (a, nd) := mkNode a g 4 0 0 2 3
  let (a, _) := mkEdge a g r na
  let (a, _) := mkEdge a g r nb
  let (a, _) := mkEdge a g na nc
  let (a, _) := mkEdge a g na nd
  return (a, g, #[r, na, nb, nc, nd])

/-- Runs a processor on graph `g`. -/
private def runProc (p : TreeProcessor) (a : TArena) (g : TGraphId) : IO TArena := do
  let ((), a) ← MrTreeM.run (p.process g ProgressMonitor.null) a
  return a

/-! ### Metadata -/

/-- `mrtree_meta_data_provider.rs`. -/
def metaTests : Suite := suite "mrtree.meta" do
  Elk.Api.ensureInitialized
  let some mr ← LayoutMetaDataService.getAlgorithmData "org.eclipse.elk.mrtree"
    | report "algorithm mrtree registered" false
  checkEq "name" mr.name "ELK Mr. Tree"
  checkEq "category" (mr.categoryId.getD "") "org.eclipse.elk.tree"
  checkEq "bundle" (mr.definingBundleId.getD "") "org.eclipse.elk.alg.mrtree"
  checkEq "preview" (mr.previewImagePath.getD "") "images/mrtree_layout.png"
  check "features: DISCONNECTED" (mr.supportedFeatures == EnumSet.of #[.disconnected])
  check "description" (has mr.description "I pity the fool who doesn't use Mr. Tree Layout.")
  checkEq "known options (Rust register_supports order)" mr.knownOptionIds
    #[CoreOptions.PADDING.id, CoreOptions.SPACING_NODE_NODE.id, CoreOptions.SPACING_EDGE_NODE.id,
      CoreOptions.ASPECT_RATIO.id, CoreOptions.PRIORITY.id, CoreOptions.SEPARATE_CONNECTED_COMPONENTS.id,
      CoreOptions.DEBUG_MODE.id, CoreOptions.DIRECTION.id, CoreOptions.INTERACTIVE.id,
      CoreOptions.INTERACTIVE_LAYOUT.id, CoreOptions.NODE_SIZE_CONSTRAINTS.id,
      CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE.id, CoreOptions.NODE_SIZE_MINIMUM.id,
      CoreOptions.NODE_SIZE_OPTIONS.id, CoreOptions.NODE_LABELS_PLACEMENT.id,
      CoreOptions.OMIT_NODE_MICRO_LAYOUT.id, CoreOptions.PORT_LABELS_PLACEMENT.id,
      CoreOptions.TOPDOWN_LAYOUT.id, CoreOptions.TOPDOWN_SCALE_FACTOR.id,
      CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH.id, CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO.id,
      CoreOptions.TOPDOWN_NODE_TYPE.id, "org.eclipse.elk.mrtree.weighting",
      "org.eclipse.elk.mrtree.searchOrder", "org.eclipse.elk.mrtree.edgeRoutingMode",
      "org.eclipse.elk.mrtree.positionConstraint", "org.eclipse.elk.mrtree.treeLevel",
      "org.eclipse.elk.mrtree.compaction", "org.eclipse.elk.mrtree.edgeEndTextureLength"]
  check "PADDING default 20" (mr.defaultValue CoreOptions.PADDING == some (ElkPadding.ofAny 20.0))
  check "SPACING_NODE_NODE default 20" (isDouble (mr.defaultValueRaw CoreOptions.SPACING_NODE_NODE.id) 20.0)
  check "SPACING_EDGE_NODE default 3" (isDouble (mr.defaultValueRaw CoreOptions.SPACING_EDGE_NODE.id) 3.0)
  check "ASPECT_RATIO default 1.6" (isDouble (mr.defaultValueRaw CoreOptions.ASPECT_RATIO.id) 1.6)
  check "PRIORITY default 1" (isInt (mr.defaultValueRaw CoreOptions.PRIORITY.id) 1)
  check "SEPARATE_CONNECTED_COMPONENTS default true"
    (isBool (mr.defaultValueRaw CoreOptions.SEPARATE_CONNECTED_COMPONENTS.id) true)
  check "DIRECTION default UNDEFINED" (mr.defaultValue CoreOptions.DIRECTION == some Direction.undefined)
  check "TOPDOWN_NODE_TYPE default" (mr.defaultValue CoreOptions.TOPDOWN_NODE_TYPE == some TopdownNodeTypes.hierarchicalNode)
  check "DEBUG_MODE no algorithm default" (mr.defaultValueRaw CoreOptions.DEBUG_MODE.id).isNone
  let some cat ← LayoutMetaDataService.getCategoryData "org.eclipse.elk.tree"
    | report "category tree registered" false
  check "category tree lists mrtree" (cat.layouters.contains "org.eclipse.elk.mrtree")
  let bySuffix ← LayoutMetaDataService.getAlgorithmDataBySuffix "mrtree"
  checkEq "suffix mrtree" (bySuffix.map (·.id)) (some "org.eclipse.elk.mrtree")
  let compaction ← opt "org.eclipse.elk.mrtree.compaction"
  check "COMPACTION: boolean, parents, default false"
    (compaction.type == .boolean && compaction.targets == EnumSet.of #[.parents] && isBool compaction.defaultValue false)
  checkEq "COMPACTION: name" compaction.name "Compaction"
  let texture ← opt "org.eclipse.elk.mrtree.edgeEndTextureLength"
  check "EDGE_END_TEXTURE_LENGTH: double 7, inclusive lower bound 0"
    (texture.type == .double && isDouble texture.defaultValue 7.0
      && (match texture.lowerBound with | some b => !b.isExclusive && isDouble (some b.value) 0.0 | none => false))
  let level ← opt "org.eclipse.elk.mrtree.treeLevel"
  check "TREE_LEVEL: int, nodes, default 0, lower bound 0"
    (level.type == .int && level.targets == EnumSet.of #[.nodes] && isInt level.defaultValue 0
      && (match level.lowerBound with | some b => !b.isExclusive && isInt (some b.value) 0 | none => false))
  let pc ← opt "org.eclipse.elk.mrtree.positionConstraint"
  check "POSITION_CONSTRAINT: int, nodes, default -1, no bound"
    (pc.type == .int && pc.targets == EnumSet.of #[.nodes] && isInt pc.defaultValue (-1) && pc.lowerBound.isNone)
  let w ← opt "org.eclipse.elk.mrtree.weighting"
  check "WEIGHTING: enum, default MODEL_ORDER"
    (w.type == .enum && w.defaultValue.bind (PropCodec.dec : PropValue → Option OrderWeighting) == some .modelOrder)
  check "WEIGHTING: no parser, no choices (Rust)" (w.parser.isNone && w.choices.isEmpty)
  let erm ← opt "org.eclipse.elk.mrtree.edgeRoutingMode"
  check "EDGE_ROUTING_MODE: default AVOID_OVERLAP"
    (erm.defaultValue.bind (PropCodec.dec : PropValue → Option EdgeRoutingMode) == some .avoidOverlap)
  let so ← opt "org.eclipse.elk.mrtree.searchOrder"
  check "SEARCH_ORDER: default DFS" (so.defaultValue.bind (PropCodec.dec : PropValue → Option TreeifyingOrder) == some .dfs)
  let gp ← opt "org.eclipse.elk.mrtree.graphProperties"
  check "GRAPH_PROPERTIES: object, advanced, empty set"
    (gp.type == .object && gp.visibility == .advanced
      && (match gp.defaultValue with | some (.enumSet b) => b == 0 | _ => false))
  -- enumerations (Java constant names and ordinals)
  checkEq "TreeLayoutPhases names" ((ElkEnum.values : Array TreeLayoutPhases).map ElkEnum.javaName)
    #["P1_TREEIFICATION", "P2_NODE_ORDERING", "P3_NODE_PLACEMENT", "P4_EDGE_ROUTING"]
  checkEq "IntermediateProcessorStrategy names"
    ((ElkEnum.values : Array IntermediateProcessorStrategy).map ElkEnum.javaName)
    #["ROOT_PROC", "FAN_PROC", "LEVEL_PROC", "NEIGHBORS_PROC", "LEVEL_HEIGHT", "DIRECTION_PROC",
      "NODE_POSITION_PROC", "COMPACTION_PROC", "LEVEL_COORDS", "GRAPH_BOUNDS_PROC", "DETREEIFYING_PROC"]
  checkEq "processor names"
    ((ElkEnum.values : Array IntermediateProcessorStrategy).map fun s => (IntermediateProcessorStrategy.create s).name)
    #["RootProcessor", "FanProcessor", "LevelProcessor", "NeighborsProcessor", "LevelHeightProcessor",
      "DirectionProcessor", "NodePositionProcessor", "CompactionProcessor", "LevelCoordinatesProcessor",
      "GraphBoundsProcessor", "Untreeifyer"]
  checkEq "OrderWeighting names" ((ElkEnum.values : Array OrderWeighting).map ElkEnum.javaName)
    #["MODEL_ORDER", "DESCENDANTS", "FAN", "CONSTRAINT"]
  checkEq "EdgeRoutingMode names" ((ElkEnum.values : Array EdgeRoutingMode).map ElkEnum.javaName)
    #["NONE", "MIDDLE_TO_MIDDLE", "AVOID_OVERLAP"]

/-! ### Graph model -/

/-- `t_edge.rs`/`t_node.rs` relation semantics. -/
def graphTests : Suite := suite "mrtree.graph" do
  let (a, g) := ({} : TArena).createGraph
  let (a, s) := mkNode a g 0 0 0 1 1 (some "s")
  let (a, x) := mkNode a g 1 0 0 1 1 (some "")
  let (a, y) := mkNode a g 2 0 0 1 1
  checkEq "nodes appended to the graph" (a.graph g).nodes #[s, x, y]
  let (a, e1) := a.createEdge s x
  let (a, e2) := a.createEdge s y
  let (a, e3) := a.createEdge s x
  checkEq "edges not added to the graph" (a.graph g).edges.size 0
  checkEq "outgoing" (a.node s).outgoingEdges #[e1, e2, e3]
  checkEq "children cache" (a.children s) #[x, y, x]
  checkEq "incoming of x" (a.node x).incomingEdges #[e1, e3]
  checkEq "parent of x" (a.parent x) (some s)
  checkEq "parent of s" (a.parent s) none
  -- hand: remove_outgoing(e3) drops the *first* x of the cache, so the cache order differs from Java
  let a := a.removeOutgoing s e3
  checkEq "remove_outgoing: outgoing" (a.node s).outgoingEdges #[e1, e2]
  checkEq "remove_outgoing: cache [y, x] (Rust)" (a.children s) #[y, x]
  let a := a.replaceOutgoingEdges s #[e2, e1]
  checkEq "replace_outgoing_edges rebuilds the cache" (a.children s) #[y, x]
  -- add_outgoing ignores duplicates
  let a := a.addOutgoing s e1
  checkEq "add_outgoing duplicate ignored" (a.node s).outgoingEdges #[e2, e1]
  -- set_source moves the edge
  let a := a.setEdgeSource e2 (some x)
  checkEq "set_source: old source" (a.node s).outgoingEdges #[e1]
  checkEq "set_source: old cache" (a.children s) #[x]
  checkEq "set_source: new source" (a.children x) #[y]
  let a := a.setEdgeTarget e2 (some s)
  checkEq "set_target: new incoming" (a.node s).incomingEdges #[e2]
  checkEq "set_target: old incoming" (a.node y).incomingEdges #[]
  -- add_child
  let (a, e4) := a.addChild y s
  check "add_child: DUMMY edge" (a.edge e4).internal.dummy
  checkEq "add_child: edge in the node's graph" (a.graph g).edges #[e4]
  -- labels and Display
  let (a, l) := a.createLabel e1 "lbl"
  checkEq "label appended" (a.edge e1).labels #[l]
  checkEq "node display with label" (a.nodeToString s) "n_s"
  checkEq "node display empty label" (a.nodeToString x) "n_1"
  checkEq "node display no label" (a.nodeToString y) "n_2"
  checkEq "edge display" (a.edgeToString e1) "n_s->n_1"
  checkEq "label display" (a.labelToString l) "l_lbl"
  let (a, l2) := a.createLabel e1 ""
  checkEq "empty label display" (a.labelToString l2) "l[n_s->n_1]"

/-! ### Importer -/

private def importJson : String := "{\"id\":\"root\",\"layoutOptions\":{\"org.eclipse.elk.direction\":\"RIGHT\"},
  \"children\":[
    {\"id\":\"n1\",\"x\":10,\"y\":20,\"width\":30,\"height\":40,\"labels\":[{\"text\":\"A\"}]},
    {\"id\":\"n2\",\"width\":0,\"height\":0,\"layoutOptions\":{\"org.eclipse.elk.priority\":\"5\"}},
    {\"id\":\"n3\",\"x\":100,\"y\":0,\"width\":10,\"height\":10}],
  \"edges\":[
    {\"id\":\"e1\",\"sources\":[\"n1\"],\"targets\":[\"n2\"]},
    {\"id\":\"e2\",\"sources\":[\"n1\"],\"targets\":[\"n3\"]},
    {\"id\":\"e3\",\"sources\":[\"n3\"],\"targets\":[\"n3\"]},
    {\"id\":\"e4\",\"sources\":[\"n2\"],\"targets\":[\"n1\",\"n3\"]},
    {\"id\":\"e5\",\"sources\":[\"n3\"],\"targets\":[\"n1\"]}]}"

/-- The `ElkGraph` edge with the given identifier. -/
private def elkEdgeById (g : ElkGraph) (ident : String) : Option EdgeId :=
  (Array.range g.edges.size).findSome? fun i =>
    if (g.edges[i]!).identifier == some ident then some ⟨i⟩ else none

/-- `elk_graph_importer.rs`. -/
def importTests : Suite := suite "mrtree.import" do
  Elk.Api.ensureInitialized
  let doc ← match Elk.Json.parse importJson (lenient := true) with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"parse failed: {e.message}")
  let (root, _, g) ← Elk.Json.importGraph doc
  let ((a, tg), g) ← ElkM.run (ElkGraphImporter.importGraph root) g
  let graph := a.graph tg
  checkEq "nodes" graph.nodes.size 3
  checkEq "edges (self loop and hyperedge skipped)" graph.edges.size 3
  check "graph origin" (match graph.internal.origin with | some (.elkNode n) => n == root | _ => false)
  check "graph props copied (DIRECTION)" ((graph.props.get MrTreeOptions.DIRECTION) == some Direction.right)
  let ns := graph.nodes
  checkEq "node ids" (ns.map fun n => (a.node n).id) #[0, 1, 2]
  checkEq "node labels" (ns.map fun n => (a.node n).label.getD "?") #["A", "", ""]
  let n1 := a.node ns[0]!
  checkFloat "n1 centre x" n1.position.x 25.0
  checkFloat "n1 centre y" n1.position.y 40.0
  checkFloat "n1 width" n1.size.x 30.0
  let n2 := a.node ns[1]!
  check "n2 size at least 1x1" (n2.size.x == 1.0 && n2.size.y == 1.0)
  checkEq "n2 props copied (PRIORITY)" (n2.props.get MrTreeOptions.PRIORITY) (some 5)
  checkFloat "n3 centre x" (a.node ns[2]!).position.x 105.0
  let es := graph.edges
  checkEq "edge sources" (es.map fun e => (a.edge e).source) #[some ns[0]!, some ns[0]!, some ns[2]!]
  checkEq "edge targets" (es.map fun e => (a.edge e).target) #[some ns[1]!, some ns[2]!, some ns[0]!]
  check "edge origin e1" (match (a.edge es[0]!).internal.origin with
    | some (.elkEdge e) => elkEdgeById g "e1" == some e | _ => false)
  checkEq "n1 children" (a.children ns[0]!) #[ns[1]!, ns[2]!]
  checkEq "n1 parent (n3 via e5)" (a.parent ns[0]!) (some ns[2]!)
  -- apply_layout: hand-set top-left positions
  let a := a.modifyNode ns[0]! fun n => { n with position := ⟨0.0, 0.0⟩ }
  let a := a.modifyNode ns[1]! fun n => { n with position := ⟨40.0, 0.0⟩, props := n.props.set MrTreeOptions.TREE_LEVEL 3 }
  let a := a.modifyNode ns[2]! fun n => { n with position := ⟨0.0, 50.0⟩ }
  let a := a.modifyEdge es[0]! fun e => { e with bendPoints := #[⟨1, 1⟩, ⟨2, 2⟩, ⟨3, 3⟩] }
  let ((), g) ← ElkM.run (ElkGraphImporter.applyLayout a tg) g
  let kids := (g.node root).children
  check "ELK n2 position" ((g.node kids[1]!).x == 40.0 && (g.node kids[1]!).y == 0.0)
  checkEq "ELK n2 TREE_LEVEL copied back" ((g.node kids[1]!).props.get MrTreeOptions.TREE_LEVEL) (some 3)
  let some e1 := elkEdgeById g "e1" | report "e1 found" false
  let some s1 := (g.edge e1).sections[0]? | report "e1 section created" false
  let sec1 := g.edgeSection s1
  check "e1 section from bend points" (sec1.startX == 1.0 && sec1.startY == 1.0 && sec1.endX == 3.0
    && sec1.endY == 3.0 && sec1.bendPoints.size == 1)
  let some e2 := elkEdgeById g "e2" | report "e2 found" false
  let sec2 := g.edgeSection (g.edge e2).sections[0]!
  -- hand: centre of n1 = (0 + 30/2, 0 + 40/2), centre of n3 = (0 + 10/2, 50 + 10/2)
  check "e2 section centre to centre" (sec2.startX == 15.0 && sec2.startY == 20.0 && sec2.endX == 5.0
    && sec2.endY == 55.0 && sec2.bendPoints.isEmpty)
  -- hand: box min (-15, -20), max (40.5, 55); default padding 12
  checkFloat "CHILD_AREA_WIDTH" (((g.node root).props.get CoreOptions.CHILD_AREA_WIDTH).getD 0.0) 55.5
  checkFloat "CHILD_AREA_HEIGHT" (((g.node root).props.get CoreOptions.CHILD_AREA_HEIGHT).getD 0.0) 75.0
  checkFloat "root width" (g.node root).width 79.5
  checkFloat "root height" (g.node root).height 99.0

/-! ### Components -/

/-- `components_processor.rs`. -/
def componentsTests : Suite := suite "mrtree.components" do
  -- split: n0 - n1, n3 -> n2, n4 isolated
  let (a, g) := ({} : TArena).createGraph
  let a := a.modifyGraph g fun x =>
    { x with props := x.props.set MrTreeOptions.DIRECTION Direction.up, internal.origin := some (.elkNode ⟨7⟩) }
  let (a, n0) := mkNode a g 0 0 0 1 1
  let (a, n1) := mkNode a g 1 0 0 1 1
  let (a, n2) := mkNode a g 2 0 0 1 1
  let (a, n3) := mkNode a g 3 0 0 1 1
  let (a, n4) := mkNode a g 4 0 0 1 1
  let (a, e01) := mkEdge a g n0 n1
  let (a, e32) := mkEdge a g n3 n2
  let (comps, a) ← MrTreeM.run (ComponentsProcessor.split g) a
  checkEq "split: three components" comps.size 3
  checkEq "split: component nodes (BFS order)" (comps.map fun c => (a.graph c).nodes) #[#[n0, n1], #[n2, n3], #[n4]]
  checkEq "split: component edges" (comps.map fun c => (a.graph c).edges) #[#[e01], #[e32], #[]]
  checkEq "split: renumbered ids" (#[n0, n1, n2, n3, n4].map fun n => (a.node n).id) #[0, 1, 0, 1, 0]
  check "split: properties copied" (comps.all fun c =>
    (a.graph c).props.get MrTreeOptions.DIRECTION == some Direction.up
      && (match (a.graph c).internal.origin with | some (.elkNode n) => n == ⟨7⟩ | _ => false))
  let a2 := a.modifyGraph g fun x => { x with props := x.props.set MrTreeOptions.SEPARATE_CONNECTED_COMPONENTS false }
  let (comps2, _) ← MrTreeM.run (ComponentsProcessor.split g) a2
  checkEq "split: not separated" comps2 #[g]
  -- pack: component A (a1, a2, edge with a bend point), component B (b1, priority 2)
  let props : PropertyMap := ((({} : PropertyMap).set MrTreeOptions.SPACING_NODE_NODE 10.0).set
    MrTreeOptions.ASPECT_RATIO 1.6).set MrTreeOptions.PADDING ⟨3.0, 0.0, 0.0, 4.0⟩
  let (p, ga) := ({} : TArena).createGraph
  let (p, gb) := p.createGraph
  let p := (p.modifyGraph ga fun x => { x with props }).modifyGraph gb fun x => { x with props }
  let (p, a1) := mkNode p ga 0 0 0 10 10
  let (p, a2n) := mkNode p ga 1 20 0 10 10
  let (p, ea) := mkEdge p ga a1 a2n
  let p := p.modifyEdge ea fun e => { e with bendPoints := #[⟨15.0, 5.0⟩] }
  let (p, b1) := mkNode p gb 0 5 5 20 20
  let p := p.modifyNode b1 fun n => { n with props := n.props.set MrTreeOptions.PRIORITY 2 }
  let (result, p) ← MrTreeM.run (ComponentsProcessor.pack #[ga, gb]) p
  let r := p.graph result
  -- hand: B first (priority 2), row width max(30, sqrt(700) * 1.6) = 42.33; B moved by (-10, -10);
  -- A starts a new row at y = 20 + 10 and is moved by (0, 30); bounds (-5, -5); padding moves (9, 8)
  checkEq "pack: node order" r.nodes #[b1, a1, a2n]
  checkEq "pack: edges" r.edges #[ea]
  check "pack: b1" ((p.node b1).position == ⟨4.0, 3.0⟩)
  check "pack: a1" ((p.node a1).position == ⟨9.0, 38.0⟩)
  check "pack: a2" ((p.node a2n).position == ⟨29.0, 38.0⟩)
  check "pack: bend point" ((p.edge ea).bendPoints == #[⟨24.0, 43.0⟩])
  checkEq "pack: priority of B" ((p.graph gb).props.get MrTreeOptions.PRIORITY) (some 2)
  checkEq "pack: priority of A (sum)" ((p.graph ga).props.get MrTreeOptions.PRIORITY) (some 0)
  checkEq "pack: result takes B's properties" (r.props.get MrTreeOptions.PRIORITY) (some 2)
  check "pack: bounds of the result" (r.internal.graphXmin == -5.0 && r.internal.graphYmin == -5.0
    && r.internal.graphXmax == 30.0 && r.internal.graphYmax == 40.0)
  check "pack: BB_UPLEFT reset" (r.internal.bbUpleft == some ⟨0.0, 0.0⟩)
  check "pack: BB_LOWRIGHT of A" ((p.graph ga).internal.bbLowright == some ⟨30.0, 10.0⟩)
  -- single component: only normalised (hand: offset (4 - 10, 3 - 20))
  let (q, gs) := ({} : TArena).createGraph
  let q := q.modifyGraph gs fun x =>
    { x with props, internal.graphXmin := 10.0, internal.graphYmin := 20.0 }
  let (q, s1) := mkNode q gs 0 10 20 5 5
  let (single, q) ← MrTreeM.run (ComponentsProcessor.pack #[gs]) q
  checkEq "pack single: same graph" single gs
  check "pack single: normalised" ((q.node s1).position == ⟨4.0, 3.0⟩)
  let (empty, q) ← MrTreeM.run (ComponentsProcessor.pack #[]) q
  check "pack empty: new empty graph" ((q.graph empty).nodes.isEmpty && empty != gs)

/-! ### Intermediate processors -/

/-- Root, fan, level, neighbors and level height processors. -/
def treeProcessorTests : Suite := suite "mrtree.intermediate.tree" do
  let (a, g, ns) := tree
  let a ← runProc RootProcessor.processor a g
  checkEq "root: only r" (ns.map fun n => (a.node n).internal.root) #[true, false, false, false, false]
  checkEq "root: no node added" (a.graph g).nodes.size 5
  -- several roots: SUPER_ROOT
  let (m, gm) := ({} : TArena).createGraph
  let (m, r1) := mkNode m gm 0 0 0 1 1
  let (m, r2) := mkNode m gm 1 0 0 1 1
  let m ← runProc RootProcessor.processor m gm
  checkEq "super root: node added" (m.graph gm).nodes.size 3
  let sr := (m.graph gm).nodes[2]!
  check "super root: label, id, ROOT, DUMMY" ((m.node sr).label == some "SUPER_ROOT" && (m.node sr).id == 0
    && (m.node sr).internal.root && (m.node sr).internal.dummy)
  check "super root: former roots cleared" (!(m.node r1).internal.root && !(m.node r2).internal.root)
  checkEq "super root: children" (m.children sr) #[r1, r2]
  check "super root: dummy edges in the graph" ((m.graph gm).edges.size == 2
    && (m.graph gm).edges.all fun e => (m.edge e).internal.dummy)
  -- hand: LEVEL keyed by id: SUPER_ROOT and r1 share id 0, r1 (level 1) is written last
  let m ← runProc LevelProcessor.processor m gm
  checkEq "level: id collision (Rust)" (#[r1, r2, sr].map (levelOf m ·)) #[1, 1, 1]
  let (e, ge) := ({} : TArena).createGraph
  let e ← runProc RootProcessor.processor e ge
  check "dummy root" ((e.graph ge).nodes.size == 1 && ((e.node (e.graph ge).nodes[0]!).label == some "DUMMY_ROOT")
    && (e.node (e.graph ge).nodes[0]!).internal.dummy)
  -- fan: hand-derived ids 0 / 00 01 / 000 001
  let a ← runProc FanProcessor.processor a g
  checkEq "fan: ids" (ns.map fun n => (a.node n).internal.idString) #["0", "00", "01", "000", "001"]
  checkEq "fan: FAN" (ns.map fun n => (a.node n).internal.fan) #[2, 2, 0, 0, 0]
  checkEq "fan: DESCENDANTS" (ns.map fun n => (a.node n).internal.descendants) #[5, 3, 1, 1, 1]
  checkEq "fan: formatRight" (FanProcessor.formatRight 7 3) "007"
  -- level
  let a ← runProc LevelProcessor.processor a g
  checkEq "level: TREE_LEVEL" (ns.map (levelOf a ·)) #[0, 1, 1, 2, 2]
  -- neighbors
  let a ← runProc NeighborsProcessor.processor a g
  let r := ns[0]!
  let na := ns[1]!
  let nb := ns[2]!
  let nc := ns[3]!
  let nd := ns[4]!
  check "neighbors: a/b" ((a.node na).internal.rightNeighbor == some nb && (a.node nb).internal.leftNeighbor == some na)
  check "neighbors: a/b siblings" ((a.node na).internal.rightSibling == some nb && (a.node nb).internal.leftSibling == some na)
  check "neighbors: c/d siblings" ((a.node nc).internal.rightSibling == some nd && (a.node nd).internal.leftSibling == some nc)
  check "neighbors: root has none" ((a.node r).internal.leftNeighbor.isNone && (a.node r).internal.rightNeighbor.isNone)
  -- cousins: r -> x, r -> y, x -> u, y -> v
  let (c, gc) := ({} : TArena).createGraph
  let (c, cr) := mkNode c gc 0 0 0 1 1
  let (c, cx) := mkNode c gc 1 0 0 1 1
  let (c, cy) := mkNode c gc 2 0 0 1 1
  let (c, cu) := mkNode c gc 3 0 0 1 1
  let (c, cv) := mkNode c gc 4 0 0 1 1
  let (c, _) := mkEdge c gc cr cx
  let (c, _) := mkEdge c gc cr cy
  let (c, _) := mkEdge c gc cx cu
  let (c, _) := mkEdge c gc cy cv
  let c ← runProc RootProcessor.processor c gc
  let c ← runProc NeighborsProcessor.processor c gc
  check "neighbors: cousins are neighbors" ((c.node cu).internal.rightNeighbor == some cv)
  check "neighbors: cousins are not siblings" ((c.node cu).internal.rightSibling.isNone && (c.node cv).internal.leftSibling.isNone)
  -- level height: hand: heights 20 / max(5, 40) / max(1, 3); widths 10 / 30 / 2
  let a ← runProc LevelHeightProcessor.processor a g
  checkEq "level height: vertical" (ns.map fun n => (a.node n).internal.levelHeight) #[20.0, 40.0, 40.0, 3.0, 3.0]
  let a := a.modifyGraph g fun x => { x with props := x.props.set MrTreeOptions.DIRECTION Direction.right }
  let a ← runProc LevelHeightProcessor.processor a g
  checkEq "level height: horizontal" (ns.map fun n => (a.node n).internal.levelHeight) #[10.0, 30.0, 30.0, 2.0, 2.0]

/-- Direction, node position, graph bounds, level coordinates, untreeifyer and compaction. -/
def placementProcessorTests : Suite := suite "mrtree.intermediate.placement" do
  -- direction
  let dir (d : Direction) : IO (Int × Int) := do
    let (a, g) := ({} : TArena).createGraph
    let a := a.modifyGraph g fun x => { x with props := x.props.set MrTreeOptions.DIRECTION d }
    let (a, n) := mkNode a g 0 0 0 1 1
    let a := a.modifyNode n fun t => { t with internal.xcoor := 3, internal.ycoor := 5 }
    let a ← runProc DirectionProcessor.processor a g
    return ((a.node n).internal.xcoor, (a.node n).internal.ycoor)
  checkEq "direction: UP" (← dir .up) (3, -5)
  checkEq "direction: RIGHT" (← dir .right) (5, 3)
  checkEq "direction: LEFT" (← dir .left) (-5, 3)
  checkEq "direction: DOWN" (← dir .down) (3, 5)
  checkEq "direction: UNDEFINED" (← dir .undefined) (3, 5)
  -- node position: hand: (XCOOR, YCOOR) - size / 2; an unreachable node is only shifted
  let (a, g, ns) := tree
  let (a, orphan) := mkNode a g 9 100 100 4 4
  let (a, _) := a.createEdge orphan orphan
  let a ← runProc RootProcessor.processor a g
  let coords : Array (Int × Int) := #[(10, 0), (0, 30), (20, 30), (-5, 60), (5, 60)]
  let a := (Array.range 5).foldl (init := a) fun a i =>
    a.modifyNode ns[i]! fun n => { n with internal.xcoor := coords[i]!.1, internal.ycoor := coords[i]!.2 }
  let a ← runProc NodePositionProcessor.processor a g
  check "node position: root" ((a.node ns[0]!).position == ⟨5.0, -10.0⟩)
  check "node position: a" ((a.node ns[1]!).position == ⟨-15.0, 27.5⟩)
  check "node position: d" ((a.node ns[4]!).position == ⟨4.0, 58.5⟩)
  check "node position: unreachable node only shifted" ((a.node orphan).position == ⟨98.0, 98.0⟩)
  -- graph bounds
  let (b, gb) := ({} : TArena).createGraph
  let (b, _) := mkNode b gb 0 0 0 10 20
  let (b, _) := mkNode b gb 1 30 (-5) 5 5
  let b ← runProc GraphBoundsProcessor.processor b gb
  let bi := (b.graph gb).internal
  check "graph bounds" (bi.graphXmin == 0.0 && bi.graphYmin == -5.0 && bi.graphXmax == 35.0 && bi.graphYmax == 20.0)
  let (b, ge) := b.createGraph
  let b ← runProc GraphBoundsProcessor.processor b ge
  check "graph bounds: empty graph keeps the start values"
    ((b.graph ge).internal.graphXmin == Float.maxValue && (b.graph ge).internal.graphXmax == Float.minValue)
  -- level coordinates: hand: vertical L0 0..10, L1 min(30, 25)..max(50, 29); horizontal L1 5..24
  let lc (d : Option Direction) : IO (Array (Float × Float)) := do
    let (a, g) := ({} : TArena).createGraph
    let a := match d with
      | some d => a.modifyGraph g fun x => { x with props := x.props.set MrTreeOptions.DIRECTION d }
      | none => a
    let (a, m1) := mkNode a g 0 0 0 10 10
    let (a, m2) := mkNode a g 1 5 30 10 20
    let (a, m3) := mkNode a g 2 20 25 4 4
    let a := setLevel (setLevel a m2 1) m3 1
    let a ← runProc LevelCoordinatesProcessor.processor a g
    return #[m1, m2, m3].map fun n => ((a.node n).internal.levelMin, (a.node n).internal.levelMax)
  checkEq "level coords: vertical (default UNDEFINED)" (← lc none) #[(0.0, 10.0), (25.0, 50.0), (25.0, 50.0)]
  checkEq "level coords: horizontal" (← lc (some .right)) #[(0.0, 10.0), (5.0, 24.0), (5.0, 24.0)]
  -- untreeifyer
  let (u, gu) := ({} : TArena).createGraph
  let (u, us) := mkNode u gu 0 0 0 1 1
  let (u, ut) := mkNode u gu 1 0 0 1 1
  let (u, ue) := mkEdge u gu us ut
  let u := (u.removeOutgoing us ue).removeIncoming ut ue
  check "untreeifyer: edge removed" ((u.node us).outgoingEdges.isEmpty && (u.children us).isEmpty)
  let u := u.modifyGraph gu fun x => { x with internal.removableEdges := #[ue] }
  let u ← runProc Untreeifyer.processor u gu
  check "untreeifyer: edge restored" ((u.node us).outgoingEdges == #[ue] && (u.node ut).incomingEdges == #[ue]
    && u.children us == #[ut])
  -- compaction: r (0,0) -> a (0,100) [level 1], r -> b (50,200) [level 2], 10x10 nodes, spacing 10
  let comp (mode : Option EdgeRoutingMode) (enabled : Bool) : IO (TArena × Array TNodeId) := do
    let (a, g) := ({} : TArena).createGraph
    let a := a.modifyGraph g fun x =>
      let ps := (x.props.set MrTreeOptions.COMPACTION enabled).set MrTreeOptions.SPACING_NODE_NODE 10.0
      { x with props := match mode with | some m => ps.set MrTreeOptions.EDGE_ROUTING_MODE m | none => ps }
    let (a, r) := mkNode a g 0 0 0 10 10
    let (a, na) := mkNode a g 1 0 100 10 10
    let (a, nb) := mkNode a g 2 50 200 10 10
    let (a, _) := mkEdge a g r na
    let (a, _) := mkEdge a g r nb
    let a := setLevel (setLevel a na 1) nb 2
    let a ← runProc RootProcessor.processor a g
    let a ← runProc CompactionProcessor.processor a g
    return (a, #[r, na, nb])
  let (cn, cns) ← comp (some .none) true
  -- hand: sweep gives a the constraint r; a and b move to r.y + 10 + 10
  checkEq "compaction: constraints of a" (cn.node cns[1]!).internal.compactConstraints #[cns[0]!]
  checkEq "compaction: no constraints of b" (cn.node cns[2]!).internal.compactConstraints #[]
  check "compaction (NONE): a" ((cn.node cns[1]!).position == ⟨0.0, 20.0⟩)
  check "compaction (NONE): b" ((cn.node cns[2]!).position == ⟨50.0, 20.0⟩)
  -- hand: AVOID_OVERLAP: no level contains 20..30, the first level from index 1 starting at >= 20 is 1
  let (ca, cas) ← comp none true
  check "compaction (AVOID_OVERLAP): a snaps to level 1" ((ca.node cas[1]!).position == ⟨0.0, 100.0⟩
    && !(ca.node cas[1]!).internal.compactLevelAscension)
  check "compaction (AVOID_OVERLAP): b ascends to level 1" ((ca.node cas[2]!).position == ⟨50.0, 100.0⟩
    && (ca.node cas[2]!).internal.compactLevelAscension && levelOf ca cas[2]! == 1)
  let (cd, cds) ← comp none false
  check "compaction disabled" ((cd.node cds[2]!).position == ⟨50.0, 200.0⟩)
  -- lowest dependent node
  let (d, gd) := ({} : TArena).createGraph
  let (d, dp) := mkNode d gd 0 0 0 5 5
  let (d, dq) := mkNode d gd 1 0 10 5 5
  let (d, dn) := mkNode d gd 2 0 30 5 5
  let d := d.modifyNode dn fun n => { n with internal.compactConstraints := #[dp, dq] }
  checkEq "lowest dependent: DOWN" (CompactionProcessor.getLowestDependentNode d dn .down) (some dq)
  checkEq "lowest dependent: UP" (CompactionProcessor.getLowestDependentNode d dn .up) (some dp)

/-! ### TreeUtil and the interactive visitor -/

/-- `tree_util.rs`, `interactive_mrtree_graph_visitor.rs`. -/
def treeUtilTests : Suite := suite "mrtree.treeutil" do
  let (a, g, ns) := tree
  let a ← runProc RootProcessor.processor a g
  let r := ns[0]!
  checkEq "get_root" (TreeUtil.getRoot a g) (some r)
  checkEq "depth" (TreeUtil.depth a r) 3
  checkEq "root_distance" (TreeUtil.rootDistance a ns[3]! r) 2
  checkEq "get_subtree (post-order)" (TreeUtil.getSubtree a r) #[ns[3]!, ns[4]!, ns[1]!, ns[2]!, r]
  let (a, _) := mkEdge a g r ns[1]!
  checkEq "get_children deduplicates" (TreeUtil.getChildren a r) #[ns[1]!, ns[2]!]
  checkEq "get_left_most(depth 3)" (TreeUtil.getLeftMost a #[r] 3) (some ns[3]!)
  checkEq "get_left_most(depth -1)" (TreeUtil.getLeftMost a #[r] (-1)) (some ns[3]!)
  -- hand: (0,0) towards (10,5) in a 4x4 box: scale min(2/10, 2/5) = 0.2
  check "to_node_border" (TreeUtil.toNodeBorder ⟨0, 0⟩ ⟨10, 5⟩ ⟨4, 4⟩ == ⟨2.0, 1.0⟩)
  checkEq "get_unique_long(1, 2)" (TreeUtil.getUniqueLong 1 2) 4294967298
  checkEq "get_unique_long(-1, -1)" (TreeUtil.getUniqueLong (-1) (-1)) 18446744073709551615
  checkEq "turn_right / turn_left" (TreeUtil.turnRight .left, TreeUtil.turnLeft .left) (Direction.up, Direction.down)
  check "direction vector UP" (TreeUtil.getDirectionVector .up == ⟨0.0, -1.0⟩)
  checkEq "get_direction: property default UNDEFINED wins" (TreeUtil.getDirection a g) Direction.undefined
  -- lowest parent: the parent whose centre is lowest (direction DOWN)
  let (p, gp) := ({} : TArena).createGraph
  let (p, p1) := mkNode p gp 0 0 0 10 10
  let (p, p2) := mkNode p gp 1 0 50 10 10
  let (p, child) := mkNode p gp 2 0 100 10 10
  let (p, e1) := mkEdge p gp p1 child
  let (p, e2) := mkEdge p gp p2 child
  checkEq "get_lowest_parent DOWN" (TreeUtil.getLowestParent p child .down) (some p2)
  checkEq "get_lowest_parent UP" (TreeUtil.getLowestParent p child .up) (some p1)
  let p := setLevel p p2 1
  -- hand: p1 and child are both on level 0, only e2 crosses levels
  checkEq "get_all_incoming_edges" (TreeUtil.getAllIncomingEdges p child gp) #[e2]
  let p := setLevel p p1 1
  let p := p.modifyNode p2 fun n => { n with position := ⟨-5.0, 50.0⟩ }
  checkEq "get_all_incoming_edges sorted by source x" (TreeUtil.getAllIncomingEdges p child gp) #[e2, e1]
  check "is_cycle_inducing (edge against UNDEFINED = down)" (!TreeUtil.isCycleInducing p e1 gp)
  -- interactive visitor
  let (eg, root) := ElkGraphUtil.createGraph
  let eg := eg.setNodeProp root CoreOptions.ALGORITHM "mrtree"
  let (eg, _) := eg.createNode (some root)
  let ((), eg) ← ElkM.run (InteractiveMrTreeGraphVisitor.visitor.visit (.node root)) eg
  check "interactive visitor: mrtree with children"
    ((eg.node root).props.get CoreOptions.INTERACTIVE == some true
      && (eg.node root).props.get MrTreeOptions.WEIGHTING == some OrderWeighting.constraint)
  let (eg2, root2) := ElkGraphUtil.createGraph
  let eg2 := eg2.setNodeProp root2 CoreOptions.ALGORITHM "org.eclipse.elk.layered"
  let (eg2, _) := eg2.createNode (some root2)
  let ((), eg2) ← ElkM.run (InteractiveMrTreeGraphVisitor.setInteractiveOptions root2) eg2
  check "interactive visitor: other algorithm untouched" ((eg2.node root2).props.get? CoreOptions.INTERACTIVE).isNone

def suites : Array Tests.Suite :=
  #[metaTests, graphTests, importTests, componentsTests, treeProcessorTests, placementProcessorTests,
    treeUtilTests]

end Tests.MrTree
