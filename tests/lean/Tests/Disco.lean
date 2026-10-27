import Tests.Framework
import Elk.Api
import Elk.Alg.Disco
/-!
# Tests for `org.eclipse.elk.alg.disco`

* `disco.meta` — port of elk-rs `plugins/org.eclipse.elk.alg.disco/tests/disco_metadata_test.rs`
  (algorithm entry, strategy option, hidden debug options) plus the option supports, the group
  names and the registered provider;
* `disco.graph` / `disco.polyomino` / `disco.transform` — unit tests of the model and of the
  helper functions (extension offsets, contours, low resolution size, cell size, component
  splitting, element import);
* `disco.engine` — layouts through `RecursiveGraphLayoutEngine` (sub layout algorithm, component
  spacing, aspect ratio, external ports);
* `disco.fixtures` — every `tests/fixtures/disco/<name>.json` laid out by `Elk.Api.layoutJson`
  must reproduce `<name>.expected.json` (output of the elk-rs oracle) within `1e-6`.

The oracle (elk-rs `eb586b6d`) panics for every DisCo layout (`Couldn't clone property
'org.eclipse.elk.polyomino.lowLevelSort'`: nobody registers the polyomino enum types with
`ElkReflect`), so the expected files were produced with a build of the oracle in which
`DisCoMetaDataProvider::init_reflect` additionally registers the three polyomino enums; the
layout code is unchanged. See `tests/fixtures/disco/README.md`.
-/
namespace Tests.Disco

open Tests Elk Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Data Elk.Core.Options
open Elk.Alg.Disco Elk.Alg.Disco.Graph Elk.Alg.Disco.Options Elk.Alg.Disco.Structures
open Elk.Alg.Disco.Transform Elk.Alg.Common.Polyomino.Structures

/-! ### Helpers -/

private def isDouble (v : Option PropValue) (x : Float) : Bool :=
  match v with | some (.double y) => y == x | _ => false

private def vec (x y : Float) : KVector := KVector.mk' x y

private def vecEq (a b : KVector) (eps : Float := 1e-9) : Bool :=
  (a.x - b.x).abs <= eps && (a.y - b.y).abs <= eps

/-- Layout of a graph given as an arena with `RecursiveGraphLayoutEngine`. -/
private def layoutRoot (g : ElkGraph) (root : NodeId) : IO ElkGraph := do
  Elk.Api.ensureInitialized
  let (_, g) ← ElkM.run (RecursiveGraphLayoutEngine.layout root ProgressMonitor.null) g
  return g

/-- Root with the disco algorithm and the given children sizes; returns the graph, the root and
the child ids. -/
private def discoGraph (sizes : Array (Float × Float)) : ElkGraph × NodeId × Array NodeId :=
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root CoreOptions.ALGORITHM DisCoOptions.ALGORITHM_ID
  sizes.foldl (fun (g, root, ids) (w, h) =>
    let (g, n) := g.createNode (some root)
    (g.modifyNode n (·.setSize ⟨w, h⟩), root, ids.push n)) (g, root, #[])

/-! ### `disco_metadata_test.rs` -/

def metaTests : Suite := suite "disco.meta" do
  Elk.Api.ensureInitialized
  -- disco_algorithm_registered
  let some algo ← LayoutMetaDataService.getAlgorithmData DisCoOptions.ALGORITHM_ID
    | report "disco algorithm registered" false "missing"
  checkEq "algorithm name" algo.name "ELK DisCo"
  checkEq "algorithm id" algo.id "org.eclipse.elk.disco"
  checkEq "defining bundle" algo.definingBundleId (some "org.eclipse.elk.alg.disco")
  checkEq "preview image" algo.previewImagePath (some "images/disco_layout.png")
  check "no category" algo.categoryId.isNone
  check "no features" (algo.supportedFeatures == EnumSet.empty)
  -- compaction_strategy_metadata
  let some strategy ← LayoutMetaDataService.getOptionData DisCoOptions.COMPONENT_COMPACTION_STRATEGY.id
    | report "strategy option registered" false "missing"
  checkEq "strategy group" strategy.group "componentCompaction"
  check "strategy targets parents" (strategy.targets == EnumSet.of #[.parents])
  check "strategy visible" (strategy.visibility == .visible)
  check "strategy type enum" (strategy.type == .enum)
  check "strategy default POLYOMINO"
    ((strategy.defaultValue.bind PropCodec.dec : Option CompactionStrategy) == some .polyomino)
  check "strategy has no parser" strategy.parser.isNone
  check "strategy has no choices" strategy.choices.isEmpty
  -- the component layout algorithm option
  let some layoutAlgorithm ← LayoutMetaDataService.getOptionData
      DisCoOptions.COMPONENT_COMPACTION_COMPONENT_LAYOUT_ALGORITHM.id
    | report "layout algorithm option registered" false "missing"
  checkEq "layout algorithm group" layoutAlgorithm.group "componentCompaction"
  check "layout algorithm type string" (layoutAlgorithm.type == .string)
  check "layout algorithm no default" layoutAlgorithm.defaultValue.isNone
  check "layout algorithm visible" (layoutAlgorithm.visibility == .visible)
  checkEq "layout algorithm name" layoutAlgorithm.name "Connected Components Layout Algorithm"
  -- debug_options_hidden
  let some graphOption ← LayoutMetaDataService.getOptionData DisCoOptions.DEBUG_DISCO_GRAPH.id
    | report "debug graph option registered" false "missing"
  checkEq "debug graph group" graphOption.group "debug"
  check "debug graph hidden" (graphOption.visibility == .hidden)
  check "debug graph object" (graphOption.type == .object)
  checkEq "debug graph name" graphOption.name "DCGraph"
  let some polyOption ← LayoutMetaDataService.getOptionData DisCoOptions.DEBUG_DISCO_POLYS.id
    | report "debug polys option registered" false "missing"
  checkEq "debug polys group" polyOption.group "debug"
  check "debug polys hidden" (polyOption.visibility == .hidden)
  checkEq "debug polys name" polyOption.name "List of Polyominoes"
  -- option supports (algorithm specific defaults); polyomino options are not registered, so
  -- their supports are dropped
  check "knows componentComponent spacing" (algo.knowsOption CoreOptions.SPACING_COMPONENT_COMPONENT.id)
  check "spacing default 20" (isDouble (algo.defaultValueRaw CoreOptions.SPACING_COMPONENT_COMPONENT.id) 20.0)
  check "thickness default 1" (isDouble (algo.defaultValueRaw CoreOptions.EDGE_THICKNESS.id) 1.0)
  check "aspect ratio default 1" (isDouble (algo.defaultValueRaw CoreOptions.ASPECT_RATIO.id) 1.0)
  check "padding default 0"
    (match algo.defaultValue CoreOptions.PADDING with
      | some p => p.top == 0.0 && p.left == 0.0 && p.bottom == 0.0 && p.right == 0.0
      | none => false)
  check "strategy known" (algo.knowsOption DisCoOptions.COMPONENT_COMPACTION_STRATEGY.id)
  check "layout algorithm option known"
    (algo.knowsOption DisCoOptions.COMPONENT_COMPACTION_COMPONENT_LAYOUT_ALGORITHM.id)
  check "debug options known" (algo.knowsOption DisCoOptions.DEBUG_DISCO_GRAPH.id
    && algo.knowsOption DisCoOptions.DEBUG_DISCO_POLYS.id)
  -- the provider description lists all supports in the Rust order
  let r := DisCoMetaDataProvider.metaDataProvider.apply {}
  checkEq "registry algorithms" r.algorithms.size 1
  checkEq "registry options" r.options.size 4
  checkEq "registry supports" r.optionSupport.size 12
  checkEqR "support order"
    (r.optionSupport.map (·.2.1))
    #["org.eclipse.elk.spacing.componentComponent", "org.eclipse.elk.edge.thickness",
      "org.eclipse.elk.aspectRatio", "org.eclipse.elk.padding", "org.eclipse.elk.polyomino.lowLevelSort",
      "org.eclipse.elk.polyomino.highLevelSort", "org.eclipse.elk.polyomino.traversalStrategy",
      "org.eclipse.elk.polyomino.fill", "org.eclipse.elk.disco.componentCompaction.strategy",
      "org.eclipse.elk.disco.componentCompaction.componentLayoutAlgorithm",
      "org.eclipse.elk.disco.debug.discoGraph", "org.eclipse.elk.disco.debug.discoPolys"]
  -- the layout provider is registered
  check "provider registered" (← LayoutProvider.isRegistered DisCoOptions.ALGORITHM_ID)

/-! ### Model -/

def graphTests : Suite := suite "disco.graph" do
  -- DCDirection
  check "north not horizontal" (!DCDirection.north.isHorizontal)
  check "east horizontal" DCDirection.east.isHorizontal
  check "south not horizontal" (!DCDirection.south.isHorizontal)
  check "west horizontal" DCDirection.west.isHorizontal
  checkEq "DCDirection java name" (ElkEnum.javaName DCDirection.south) "SOUTH"
  -- DCExtension: offset = -parentBounds.position + middle, shifted by half the width
  let bounds := ElkRectangle.ofValues 10.0 20.0 30.0 40.0
  let horizontal := DCExtension.new bounds .east (vec 15.0 25.0) 6.0
  check "horizontal extension offset" (vecEq horizontal.offset (vec 5.0 2.0))
  check "horizontal extension width" (horizontal.width == 6.0)
  let vertical := DCExtension.new bounds .north (vec 15.0 25.0) 6.0
  check "vertical extension offset" (vecEq vertical.offset (vec 2.0 5.0))
  -- DCElement: bounds of the polygon
  let e := DCElement.new #[vec 1.0 2.0, vec 1.0 8.0, vec 6.0 8.0, vec 6.0 2.0]
  check "element bounds" (e.bounds == ElkRectangle.ofValues 1.0 2.0 5.0 6.0)
  checkEqR "element coords" e.coords #[1.0, 2.0, 1.0, 8.0, 6.0, 8.0, 6.0, 2.0]
  check "intersects crossing rect" (e.intersects (ElkRectangle.ofValues 4.0 4.0 10.0 10.0))
  check "contained in big rect" (e.intersects (ElkRectangle.ofValues 0.0 0.0 20.0 20.0))
  check "disjoint rect" (!e.intersects (ElkRectangle.ofValues 10.0 10.0 2.0 2.0))
  let empty := DCElement.new #[]
  check "empty element bounds infinite" (empty.bounds.x == Float.posInf && empty.bounds.width == Float.negInf)
  -- DCGraph: components, offsets, bounding rectangles with extensions
  let e1 := DCElement.new #[vec 0.0 0.0, vec 0.0 10.0, vec 10.0 10.0, vec 10.0 0.0]
  let e2 := DCElement.new #[vec 20.0 5.0, vec 20.0 25.0, vec 30.0 25.0, vec 30.0 5.0]
  let e3 := (DCElement.new #[vec 100.0 100.0, vec 100.0 110.0, vec 110.0 110.0, vec 110.0 100.0]).addExtension
    (DCExtension.new (ElkRectangle.ofValues 100.0 100.0 10.0 10.0) .west (vec 100.0 105.0) 40.0)
  let g := DCGraph.new #[e1, e2, e3] #[#[⟨0⟩, ⟨1⟩], #[⟨2⟩]] 5.0
  checkEq "component count" g.components.size 2
  check "inset" (g.inset == 5.0)
  check "component of element" (g.elements[1]!.component == some ⟨0⟩)
  check "component 0 dimensions" (vecEq (g.componentDimensions ⟨0⟩) (vec 30.0 25.0))
  check "component 0 min corner" (vecEq (g.componentMinCorner ⟨0⟩) (vec 0.0 0.0))
  -- the west extension widens the y range: [85, 125] instead of [100, 110]
  check "component 1 dimensions with extension" (vecEq (g.componentDimensions ⟨1⟩) (vec 10.0 40.0))
  check "component 1 min corner with extension" (vecEq (g.componentMinCorner ⟨1⟩) (vec 100.0 85.0))
  let g := g.setComponentOffset ⟨0⟩ (vec 7.0 3.0)
  check "offset" (vecEq (g.componentOffset ⟨0⟩) (vec 7.0 3.0))
  check "min corner includes offset" (vecEq (g.componentMinCorner ⟨0⟩) (vec 7.0 3.0))
  check "element offset" (vecEq (g.elementOffset ⟨1⟩) (vec 7.0 3.0))
  checkEq "initial component id" (g.componentId ⟨0⟩) (-1)
  checkEq "component id" ((g.setComponentId ⟨1⟩ 4).componentId ⟨1⟩) 4
  -- a rectangle that crosses the border of an element intersects; one strictly inside does not
  check "component intersects" (g.componentIntersects ⟨0⟩ (ElkRectangle.ofValues 28.0 8.0 5.0 2.0))
  check "rectangle inside an element does not intersect"
    (!g.componentIntersects ⟨0⟩ (ElkRectangle.ofValues 22.0 8.0 2.0 2.0))

/-! ### Polyomino -/

def polyominoTests : Suite := suite "disco.polyomino" do
  checkEq "low res dimension exact" (DCPolyomino.computeLowResDimension 30.0 10.0) 3
  checkEq "low res dimension rounds up" (DCPolyomino.computeLowResDimension 31.0 10.0) 4
  checkEq "low res dimension zero" (DCPolyomino.computeLowResDimension 0.0 10.0) 0
  checkEq "low res dimension 0/0" (DCPolyomino.computeLowResDimension 0.0 0.0) 0
  checkEq "low res dimension negative" (DCPolyomino.computeLowResDimension (-5.0) 10.0) 0
  -- a 20x10 rectangle with 12x12 cells: 2x1 cells (offset (2, 1)), both crossed by the border
  let e := DCElement.new #[vec 0.0 0.0, vec 0.0 10.0, vec 20.0 10.0, vec 20.0 0.0]
  let g := DCGraph.new #[e] #[#[⟨0⟩]] 0.0
  match DCPolyomino.new g ⟨0⟩ 12.0 12.0 with
  | .error err => report "polyomino built" false err
  | .ok p =>
    checkEq "polyomino width" p.pWidth 2
    checkEq "polyomino height" p.pHeight 1
    check "cell (0,0) blocked" (PolyominoLike.isBlocked p 0 0)
    check "cell (1,0) blocked" (PolyominoLike.isBlocked p 1 0)
    check "offset" (vecEq (DCPolyomino.getOffset g p) (vec 2.0 1.0))
    check "min corner on canvas" (vecEq (DCPolyomino.getMinCornerOnCanvas g p) (vec (-2.0) (-1.0)))
    check "no extensions" (PolyominoLike.polyominoExtensions p).isEmpty
    checkEq "poly id" (DCPolyomino.getId g p) (-1)
  -- 15x15 with 10x10 cells: 2x2 cells, centred (offset = -0.5 * (15 - 20) = 2.5)
  let e := DCElement.new #[vec 0.0 0.0, vec 0.0 15.0, vec 15.0 15.0, vec 15.0 0.0]
  let g := DCGraph.new #[e] #[#[⟨0⟩]] 0.0
  match DCPolyomino.new g ⟨0⟩ 10.0 10.0 with
  | .error err => report "polyomino 2x2 built" false err
  | .ok p =>
    checkEq "2x2 width" p.pWidth 2
    check "2x2 offset" (vecEq (DCPolyomino.getOffset g p) (vec 2.5 2.5))
    check "all four cells blocked"
      (PolyominoLike.isBlocked p 0 0 && PolyominoLike.isBlocked p 1 0
        && PolyominoLike.isBlocked p 0 1 && PolyominoLike.isBlocked p 1 1)
  -- an element with an east extension adds an extension and weakly blocks the area to the border
  let ext := DCExtension.new (ElkRectangle.ofValues 0.0 0.0 10.0 10.0) .east (vec 10.0 5.0) 8.0
  let e := (DCElement.new #[vec 0.0 0.0, vec 0.0 10.0, vec 10.0 10.0, vec 10.0 0.0]).addExtension ext
  let e2 := DCElement.new #[vec 40.0 0.0, vec 40.0 10.0, vec 50.0 10.0, vec 50.0 0.0]
  let g := DCGraph.new #[e, e2] #[#[⟨0⟩, ⟨1⟩]] 0.0
  match DCPolyomino.new g ⟨0⟩ 12.0 12.0 with
  | .error err => report "polyomino with extension built" false err
  | .ok p =>
    checkEq "extension width" p.pWidth 5
    checkEqR "one east extension (offset 0, width 0)" (PolyominoLike.polyominoExtensions p) #[(.east, 0, 0)]
    check "cell (0,0) blocked" (PolyominoLike.isBlocked p 0 0)
    check "cell (1,0) blocked" (PolyominoLike.isBlocked p 1 0)
    check "cell (2,0) weakly blocked by the extension" (PolyominoLike.isWeaklyBlocked p 2 0)
    check "cell (3,0) blocked by the second element" (PolyominoLike.isBlocked p 3 0)
  -- cell size of the compactor: one 10x10 component, upper bound 100
  let e := DCElement.new #[vec 0.0 0.0, vec 0.0 10.0, vec 10.0 10.0, vec 10.0 0.0]
  let g := DCGraph.new #[e] #[#[⟨0⟩]] 0.0
  let size := DisCoPolyominoCompactor.new.computeCellSize g
  -- (sqrt(4*100*1*100 - 4*100 + 20^2) + 20) / (2 * 99)
  let expected := (Float.sqrt (4.0 * 100.0 * 1.0 * 100.0 - 4.0 * 100.0 + 20.0 * 20.0) + 20.0) / (2.0 * 99.0)
  checkFloat "cell size" size expected
  let empty := DCGraph.new #[] #[] 0.0
  check "cell size of an empty graph" ((DisCoPolyominoCompactor.new.computeCellSize empty) == 0.0)

/-! ### Transformation -/

/-- Adds a simple edge between two nodes of the root. -/
private def addEdge (g : ElkGraph) (s t : NodeId) : ElkGraph × EdgeId :=
  ElkGraphUtil.createSimpleEdge g (.node s) (.node t)

def transformTests : Suite := suite "disco.transform" do
  -- components: a-b, c, d-e (a,b connected, e-d connected in the other direction)
  let (g, root, ids) := discoGraph #[(10.0, 10.0), (10.0, 10.0), (10.0, 10.0), (10.0, 10.0), (10.0, 10.0)]
  let (g, _) := addEdge g ids[0]! ids[1]!
  let (g, _) := addEdge g ids[4]! ids[3]!
  let (cs, _) ← ElkM.run (ElkGraphComponentsProcessor.split root) g
  checkEqR "components in DFS order" (cs.map (·.map (·.idx))) #[#[1, 2], #[3], #[4, 5]]
  -- self loops and edges between the same pair do not duplicate nodes
  let (g, e0) := addEdge g ids[2]! ids[2]!
  let (g, _) := addEdge g ids[2]! ids[0]!
  let (cs, _) ← ElkM.run (ElkGraphComponentsProcessor.split root) g
  checkEqR "components with self loop and extra edge (incoming edges first)" (cs.map (·.map (·.idx))) #[#[1, 3, 2], #[4, 5]]
  let _ := e0
  -- an edge with two targets is not simple
  let (g2, hyper) := ElkGraphUtil.createHyperedge g #[.node ids[0]!] #[.node ids[1]!, .node ids[3]!]
  let _ := hyper
  let failed ← (do
    let _ ← ElkM.run (ElkGraphComponentsProcessor.split root) g2
    pure false) <|> pure true
  check "hyperedge is rejected" failed
  -- port-connected components: two nodes attached to the same parent port belong together
  let (g, root, ids) := discoGraph #[(10.0, 10.0), (10.0, 10.0), (10.0, 10.0)]
  let (g, port) := g.createPort (some root)
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.port port) (.node ids[0]!)
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node ids[1]!) (.port port)
  let (cs, _) ← ElkM.run (ElkGraphComponentsProcessor.split root) g
  checkEqR "nodes at the same parent port are one component" (cs.map (·.map (·.idx))) #[#[1, 2], #[3]]
  -- contour of a straight segment: a rectangle of the given width
  let c := ElkGraphTransformer.getContour #[vec 0.0 0.0, vec 10.0 0.0] 4.0
  checkEq "contour size" c.size 4
  let xs := c.map (·.x)
  let ys := c.map (·.y)
  check "contour x range" (xs.all (fun x => (x - 0.0).abs < 1e-9 || (x - 10.0).abs < 1e-9))
  check "contour y range" (ys.all (fun y => (y - 2.0).abs < 1e-9 || (y + 2.0).abs < 1e-9))
  check "contour has all corners"
    (c.any (fun p => vecEq p (vec 0.0 2.0)) && c.any (fun p => vecEq p (vec 0.0 (-2.0)))
      && c.any (fun p => vecEq p (vec 10.0 2.0)) && c.any (fun p => vecEq p (vec 10.0 (-2.0))))
  check "contour of a single point is empty" (ElkGraphTransformer.getContour #[vec 0.0 0.0] 4.0).isEmpty
  -- a right angle: the inner corners are merged into one intersection point
  let corner := ElkGraphTransformer.getContour #[vec 0.0 0.0, vec 10.0 0.0, vec 10.0 10.0] 2.0
  checkEq "right-angle contour size" corner.size 6
  -- import: shape count and enlargement by the component spacing
  let (g, root, ids) := discoGraph #[(30.0, 20.0)]
  let g := g.modifyNode ids[0]! fun n => { n with x := 5.0, y := 7.0 }
  let ((graph, st), _) ← ElkM.run (StateRefT'.run
    ((ElkGraphTransformer.toIGraphTransformer 10.0).importGraph root) ({} : ElkGraphTransformer)) g
  checkEq "one component" graph.components.size 1
  checkEq "one element" graph.elements.size 1
  check "inset is half the spacing" (graph.inset == 5.0)
  check "element bounds enlarged by the spacing"
    (graph.elements[0]!.bounds == ElkRectangle.ofValues 0.0 2.0 40.0 30.0)
  check "parent coords" ((graph.elements[0]!.parentCoords).map (vecEq · (vec 5.0 7.0)) == some true)
  checkEq "mapping has the node" st.elementMapping.size 1

/-! ### Layouts through the engine -/

private def nodeOf (g : ElkGraph) (n : NodeId) : ElkNode := g.node n

def engineTests : Suite := suite "disco.engine" do
  -- the engine does not run a provider for a graph without children
  let (g, root, _) := discoGraph #[]
  let g ← layoutRoot g root
  check "empty graph: engine leaves the size" ((nodeOf g root).width == 0.0 && (nodeOf g root).height == 0.0)
  -- the provider itself on an empty graph: the dimensions are the (default) padding only
  let (g, root, _) := discoGraph #[]
  let (_, g) ← ElkM.run (DisCoLayoutProvider.layout root ProgressMonitor.null) g
  checkFloat "empty graph: width is the padding" (nodeOf g root).width 24.0
  checkFloat "empty graph: height is the padding" (nodeOf g root).height 24.0
  -- a single node moves to the padding corner (plus half the component spacing)
  let (g, root, ids) := discoGraph #[(30.0, 20.0)]
  let g := g.setNodeProp root CoreOptions.PADDING (ElkPadding.ofAny 5.0)
  let g ← layoutRoot g root
  let n := nodeOf g ids[0]!
  check "single node near the origin" (n.x >= 0.0 && n.y >= 0.0 && n.x < 30.0 && n.y < 30.0)
  check "parent covers the node" ((nodeOf g root).width >= n.x + 30.0 && (nodeOf g root).height >= n.y + 20.0)
  -- two components never overlap
  let (g, root, ids) := discoGraph #[(30.0, 20.0), (30.0, 20.0), (25.0, 60.0)]
  let g ← layoutRoot g root
  let rects := ids.map fun i => let n := nodeOf g i; ElkRectangle.ofValues n.x n.y n.width n.height
  check "components do not overlap"
    (!(rects[0]!.intersects rects[1]!) && !(rects[0]!.intersects rects[2]!) && !(rects[1]!.intersects rects[2]!))
  -- an unknown component layout algorithm id is ignored
  let (g, root, ids) := discoGraph #[(30.0, 20.0), (30.0, 20.0)]
  let g := g.setNodeProp root DisCoOptions.COMPONENT_COMPACTION_COMPONENT_LAYOUT_ALGORITHM "no.such.algorithm"
  let g ← layoutRoot g root
  check "unknown sub algorithm ignored" ((nodeOf g root).width > 0.0 && ids.size == 2)
  -- a blank algorithm id is ignored
  let (g, root, _) := discoGraph #[(30.0, 20.0), (30.0, 20.0)]
  let g := g.setNodeProp root DisCoOptions.COMPONENT_COMPACTION_COMPONENT_LAYOUT_ALGORITHM "   "
  let g ← layoutRoot g root
  check "blank sub algorithm ignored" ((nodeOf g root).width > 0.0)
  -- the `fixed` sub layout keeps the given positions inside a component
  let (g, root, ids) := discoGraph #[(10.0, 10.0), (10.0, 10.0)]
  let g := g.setNodeProp root DisCoOptions.COMPONENT_COMPACTION_COMPONENT_LAYOUT_ALGORITHM "fixed"
  let g := g.modifyNode ids[0]! fun n => { n with props := n.props.set FixedLayouterOptions.POSITION (vec 0.0 0.0) }
  let g := g.modifyNode ids[1]! fun n => { n with props := n.props.set FixedLayouterOptions.POSITION (vec 100.0 0.0) }
  let (g, _) := ElkGraphUtil.createSimpleEdge g (.node ids[0]!) (.node ids[1]!)
  let g ← layoutRoot g root
  check "connected nodes keep their distance"
    (((nodeOf g ids[1]!).x - (nodeOf g ids[0]!).x - 100.0).abs < 1e-9
      && ((nodeOf g ids[1]!).y - (nodeOf g ids[0]!).y).abs < 1e-9)
  -- external edges: a port of the layout graph connected to a node makes the port snap to the edge
  let (g, root, ids) := discoGraph #[(40.0, 40.0)]
  let g := g.modifyNode root fun n => { n with width := 100.0, height := 100.0 }
  let g := g.modifyNode ids[0]! fun n => { n with x := 30.0, y := 30.0 }
  let (g, port) := g.createPort (some root)
  let g := g.modifyPort port fun p => { p with x := 0.0, y := 45.0, width := 6.0, height := 6.0 }
  let (g, edge) := ElkGraphUtil.createSimpleEdge g (.port port) (.node ids[0]!)
  let (g, sec) := ElkGraphUtil.firstEdgeSection g edge false false
  let g := g.modifySection sec fun s => { s with startX := 0.0, startY := 48.0, endX := 30.0, endY := 50.0 }
  let g ← layoutRoot g root
  let s := g.edgeSection sec
  check "external edge start on the west border" (s.startX == 0.0)
  check "external edge ends at the node"
    (((nodeOf g ids[0]!).x - s.endX).abs < 1e-9)
  check "port centred on the first edge point"
    (((g.port port).y - (s.startY - 3.0)).abs < 1e-9)

/-! ### Oracle fixtures -/

private def fixtureDir : System.FilePath := "tests/fixtures/disco"

/-- Names of the fixtures (`<name>.json` without `.expected.json`), sorted. -/
private def fixtureNames : IO (Array String) := do
  let entries ← System.FilePath.readDir fixtureDir
  let names := entries.filterMap fun e =>
    if e.fileName.endsWith ".json" && !e.fileName.endsWith ".expected.json" then
      some (e.fileName.dropEnd ".json".length).toString
    else none
  return stableSort names (fun a b => compare a b)

/-- First differences of two JSON values; numbers are compared with an absolute tolerance, objects
by key (order is irrelevant), arrays element by element. -/
private partial def jsonDiff (eps : Float) (path : String) (expected actual : Elk.Json.Value) :
    Array String :=
  match expected, actual with
  | .num a, .num b =>
    if (a.toFloat - b.toFloat).abs <= eps then #[]
    else #[s!"{path}: expected {a.render}, got {b.render}"]
  | .obj ekvs, .obj akvs => Id.run do
    let mut diffs : Array String := #[]
    for (k, ev) in ekvs do
      match akvs.find? (·.1 == k) with
      | some (_, av) => diffs := diffs ++ jsonDiff eps s!"{path}/{k}" ev av
      | none => diffs := diffs.push s!"{path}/{k}: missing"
    for (k, _) in akvs do
      if !ekvs.any (·.1 == k) then diffs := diffs.push s!"{path}/{k}: unexpected"
    return diffs
  | .arr es, .arr as => Id.run do
    if es.size != as.size then
      return #[s!"{path}: array length {es.size} expected, got {as.size}"]
    let mut diffs : Array String := #[]
    for i in [0:es.size] do
      diffs := diffs ++ jsonDiff eps s!"{path}/{i}" es[i]! as[i]!
    return diffs
  | .str a, .str b => if a == b then #[] else #[s!"{path}: expected \"{a}\", got \"{b}\""]
  | .bool a, .bool b => if a == b then #[] else #[s!"{path}: expected {a}, got {b}"]
  | .null, .null => #[]
  | _, _ => #[s!"{path}: different kinds of value"]

/-- `disco.fixtures`: layouts of `tests/fixtures/disco/<name>.json` against the oracle output
within `1e-6` (`compare_model_parity_layouts.py` tolerance). -/
def fixtureTests : Suite := suite "disco.fixtures" do
  let names ← fixtureNames
  check "fixtures found" (names.size >= 10)
  for name in names do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    let expectedPath := fixtureDir / s!"{name}.expected.json"
    let errorPath := fixtureDir / s!"{name}.expected.error"
    if ← errorPath.pathExists then
      -- the oracle panics (grid index out of bounds); the layout must fail with the same message
      let expectedError := (← IO.FS.readFile errorPath).trimAscii.toString
      match ← Elk.Api.layoutJson input "{}" (lenient := false) (pretty := true) (sortKeys := true) with
      | .error e => report s!"{name}: fails like the oracle" ((e.splitOn expectedError).length > 1) e
      | .ok _ => report s!"{name}: fails like the oracle" false "layout succeeded"
    else if !(← expectedPath.pathExists) then
      report s!"{name}: expected output exists" false s!"missing {expectedPath}"
    else
      let expectedText ← IO.FS.readFile expectedPath
      match ← Elk.Api.layoutJson input "{}" (lenient := false) (pretty := true) (sortKeys := true) with
      | .error e => report s!"{name}: layout" false e
      | .ok actualText =>
        match Elk.Json.parseString expectedText, Elk.Json.parseString actualText with
        | .ok expected, .ok actual =>
          let diffs := jsonDiff 1e-6 "" expected actual
          report s!"{name}: matches oracle" diffs.isEmpty
            (", ".intercalate (diffs.extract 0 5).toList)
        | _, _ => report s!"{name}: output parses" false "invalid JSON"

def suites : Array Tests.Suite :=
  #[metaTests, graphTests, polyominoTests, transformTests, engineTests, fixtureTests]

end Tests.Disco
