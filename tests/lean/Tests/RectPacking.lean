import Tests.Framework
import Elk.Api
import Elk.Alg.RectPacking
/-!
# Tests for `org.eclipse.elk.alg.rectpacking`

Ports of all elk-rs tests of the plugin (`rectpacking_metadata_test.rs`,
`rectpacking_compaction_test.rs`, `padding_test.rs`, `issue_583_test.rs`), unit tests of the
block/row/stack structures, the drawing data, the width approximation (filters, calculations,
`AreaApproximation`, both approximators), the intermediate processors, the packing and
whitespace elimination phases and the provider. Expected values are derived by hand from the Rust
code ("hand: …" comments) unless they come from the elk-rs tests or the oracle.

Two fixture suites compare `Elk.Api.layoutJson` byte-for-byte with the elk-rs oracle
(`model_parity_layout_runner`, commit eb586b6d):
* `rectpacking.fixtures` (`tests/fixtures/rectpacking/<name>.json` / `<name>.expected.json`): the
  stock oracle, which registers the four enum options without a value parser (their strings are
  ignored by the oracle and the port); includes the corpus models
  `interactiveRectpacking_hierarchy` / `_oneBigNode` (`corpus_*`);
* `rectpacking.fixtures.enum` (`tests/fixtures/rectpacking/enum`): an oracle build whose rectangle
  packing metadata provider additionally registers the enum choices and parsers (the only change
  to elk-rs), so every strategy is reachable from JSON; the suite installs `enumParserProvider`.
  Inputs without an expected file are models on which elk-rs panics (`NONE` packing followed by a
  whitespace eliminator); the port must report an error.
`ELK_RECTPACKING_FIXTURES` / `ELK_RECTPACKING_FIXTURES_ENUM` point the suites to other directories
(large parity runs).
-/
namespace Tests.RectPacking

open Tests Elk Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Data
open Elk.Core.Alg
open Elk.Alg.RectPacking Elk.Alg.RectPacking.Options Elk.Alg.RectPacking.Util
open Elk.Alg.RectPacking.Intermediate Elk.Alg.RectPacking.P1WidthApproximation
open Elk.Alg.RectPacking.P2Packing Elk.Alg.RectPacking.P3WhitespaceElimination

/-! ### Helpers -/

/-- A root with children of the given sizes. -/
private def mkGraph (sizes : Array (Float × Float)) : ElkGraph × NodeId × Array NodeId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let mut g := g
  let mut kids : Array NodeId := #[]
  for (w, h) in sizes do
    let (g', k) := g.createNode (some root)
    g := g'.modifyNode k fun n => { n with width := w, height := h }
    kids := kids.push k
  return (g, root, kids)

/-- Runs a `RectPackingM` computation on a graph with an empty arena. -/
private def runRP {α : Type} (g : ElkGraph) (x : RectPackingM α) : IO (α × RectPackingArena × ElkGraph) := do
  let ((a, arena), g) ← ElkM.run (RectPackingM.run x) g
  return (a, arena, g)

private def runElk {α : Type} (g : ElkGraph) (x : ElkM α) : IO (α × ElkGraph) := ElkM.run x g

private def checkPos (name : String) (g : ElkGraph) (n : NodeId) (x y : Float) : TestM Unit := do
  checkFloat s!"{name} x" (g.node n).x x
  checkFloat s!"{name} y" (g.node n).y y

private def checkShape (name : String) (g : ElkGraph) (n : NodeId) (x y w h : Float) : TestM Unit := do
  checkPos name g n x y
  checkFloat s!"{name} width" (g.node n).width w
  checkFloat s!"{name} height" (g.node n).height h

private def dd (w h : Float) (opt : DrawingDataDescriptor) (ar : Float := 1.3) (nx ny : Float := 0.0) :
    DrawingData :=
  DrawingData.withCoordinates ar w h opt nx ny

/-! ### `rectpacking_metadata_test.rs` and the provider registration -/

def metadataTests : Suite := suite "rectpacking.metadata" do
  LayoutMetaDataService.ensureInitialized
  -- width_approximation_defaults
  match ← LayoutMetaDataService.getOptionData RectPackingOptions.WIDTH_APPROXIMATION_STRATEGY.id with
  | none => report "width approximation option registered" false
  | some o =>
    checkEq "width approximation group" o.group "widthApproximation"
    check "width approximation targets parents" (o.targets.contains .parents)
    check "width approximation default GREEDY"
      ((o.defaultValue.bind PropCodec.dec : Option WidthApproximationStrategy) == some .greedy)
    checkEq "width approximation type" o.type LayoutOptionType.enum
    -- Rust registers no choices and no parser for ENUM options of this plugin
    checkEq "width approximation no choices (elk-rs)" o.choices.size 0
    check "width approximation cannot parse (elk-rs)" (!o.canParseValue)
  -- whitespace_elimination_defaults
  match ← LayoutMetaDataService.getOptionData RectPackingOptions.WHITE_SPACE_ELIMINATION_STRATEGY.id with
  | none => report "whitespace elimination option registered" false
  | some o =>
    checkEq "whitespace elimination group" o.group "whiteSpaceElimination"
    check "whitespace elimination targets parents" (o.targets.contains .parents)
    check "whitespace elimination default NONE"
      ((o.defaultValue.bind PropCodec.dec : Option WhiteSpaceEliminationStrategy) == some .none)
  -- compaction_iterations_default
  match ← LayoutMetaDataService.getOptionData RectPackingOptions.PACKING_COMPACTION_ITERATIONS.id with
  | none => report "compaction iterations option registered" false
  | some o =>
    check "compaction iterations default 1"
      (match o.defaultValue with | some (.int v) => v == 1 | _ => false)
    check "compaction iterations lower bound 1"
      (match o.lowerBound with | some (.inclusive (.int v)) => v == 1 | _ => false)
    checkEq "compaction iterations group" o.group "packing.compaction"
  match ← LayoutMetaDataService.getOptionData RectPackingOptions.DESIRED_POSITION.id with
  | none => report "desired position option registered" false
  | some o =>
    check "desired position targets nodes" (o.targets == EnumSet.of #[LayoutOptionTarget.nodes])
    checkEq "desired position visibility" o.visibility LayoutOptionVisibility.advanced
    check "desired position lower bound -1"
      (match o.lowerBound with | some (.inclusive (.int v)) => v == -1 | _ => false)
    checkEq "desired position group" o.group ""
  match ← LayoutMetaDataService.getOptionData RectPackingOptions.TRYBOX.id with
  | none => report "trybox option registered" false
  | some o =>
    checkEq "trybox visibility" o.visibility LayoutOptionVisibility.advanced
    check "trybox default false" (match o.defaultValue with | some (.bool false) => true | _ => false)
  match ← LayoutMetaDataService.getAlgorithmData RectPackingOptions.ALGORITHM_ID with
  | none => report "algorithm registered" false
  | some a =>
    checkEq "algorithm name" a.name "ELK Rectangle Packing"
    checkEq "algorithm bundle" a.definingBundleId (some "org.eclipse.elk.alg.rectpacking")
    check "algorithm description" (a.description.startsWith "Algorithm for packing of unconnected boxes")
    checkEq "algorithm known options" a.knownOptionIds.size 26
    checkEq "first known option" a.knownOptionIds[0]! CoreOptions.ASPECT_RATIO.id
    checkEq "last known option" a.knownOptionIds[25]! RectPackingOptions.ORDER_BY_SIZE.id
    check "aspect ratio default 1.3" (a.defaultValue CoreOptions.ASPECT_RATIO == some 1.3)
    check "spacing default 15" (a.defaultValue CoreOptions.SPACING_NODE_NODE == some 15.0)
    check "padding default 15" (a.defaultValue CoreOptions.PADDING == some (ElkPadding.ofAny 15.0))
    check "fixed graph size default false" (a.defaultValue CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE == some false)
    check "content alignment without default" (a.knowsOption CoreOptions.CONTENT_ALIGNMENT.id &&
      (a.defaultValueRaw CoreOptions.CONTENT_ALIGNMENT.id).isNone)
  match ← LayoutMetaDataService.getCategoryData "" with
  | none => report "backup category registered" false
  | some c => check "algorithm in the backup category" (c.layouters.contains RectPackingOptions.ALGORITHM_ID)
  let s ← LayoutMetaDataService.getInstance
  -- rank 60: after force (30), before spore (70)
  let order := s.algorithmOrder
  match order.findIdx? (· == RectPackingOptions.ALGORITHM_ID), order.findIdx? (· == "org.eclipse.elk.force"),
      order.findIdx? (· == "org.eclipse.elk.sporeOverlap") with
  | some r, some f, some sp => check "registration order force < rectpacking < spore" (f < r && r < sp)
  | _, _, _ => report "registration order" false
  let r := RectPackingMetaDataProvider.metaDataProvider.apply {}
  checkEq "provider options" r.options.size 13
  checkEq "provider algorithms" r.algorithms.size 1
  checkEq "provider supports" r.optionSupport.size 26
  checkEq "provider categories" r.categories.size 0
  checkEq "phase java name" (ElkEnum.javaName RectPackingLayoutPhases.p1WidthApproximation) "P1_WIDTH_APPROXIMATION"
  checkEq "processor java name" (ElkEnum.javaName IntermediateProcessorStrategy.minSizePostProcessor)
    "MIN_SIZE_POST_PROCESSOR"
  checkEq "optimization goal ordinal" (ElkEnum.ordinal OptimizationGoal.areaDriven) 2

/-! ### Drawing data, drawing util -/

def drawingTests : Suite := suite "rectpacking.drawing" do
  -- hand: min(1.3 / 100, 1 / 50) = 0.013
  checkFloat "scale measure" (DrawingUtil.computeScaleMeasure 100.0 50.0 1.3) 0.013
  -- hand: min(1.3 / 10, 1 / 50) = 0.02
  checkFloat "scale measure height bound" (DrawingUtil.computeScaleMeasure 10.0 50.0 1.3) 0.02
  let d := DrawingData.new 1.3 100.0 50.0 .wholeDrawing
  checkFloat "area" d.area 5000.0
  checkFloat "aspect ratio" d.aspectRatio 2.0
  checkFloat "drawing scale measure" d.scaleMeasure 0.013
  checkFloat "next x default" d.nextXCoordinate 0.0
  let z := DrawingData.new 1.3 0.0 50.0 .wholeDrawing
  checkFloat "zero width keeps area 0" z.area 0.0
  checkFloat "zero width keeps aspect ratio 0" z.aspectRatio 0.0
  let d2 := d.setDrawingWidth 200.0
  checkFloat "set width recomputes area" d2.area 10000.0
  checkFloat "set width recomputes aspect ratio" d2.aspectRatio 4.0
  let d3 := d.setDrawingHeight 100.0
  checkFloat "set height recomputes aspect ratio" d3.aspectRatio 1.0
  -- calculate_dimensions_from_nodes
  let (g, _, kids) := mkGraph #[(30.0, 20.0), (10.0, 40.0)]
  let g := g.modifyNode kids[1]! fun n => { n with x := 50.0, y := 5.0 }
  let (dim, _) ← runElk g (DrawingUtil.calculateDimensionsFromNodes kids)
  checkFloat "dimensions from nodes width" dim.x 60.0
  checkFloat "dimensions from nodes height" dim.y 45.0
  let (_, g) ← runElk g (DrawingUtil.resetCoordinates kids)
  checkPos "reset coordinates" g kids[1]! 0.0 0.0

/-! ### Best candidate filters -/

def filterTests : Suite := suite "rectpacking.filters" do
  let c1 := dd 100.0 50.0 .candidatePositionLastPlacedRight
  let c2 := dd 50.0 100.0 .candidatePositionLastPlacedBelow
  let c3 := dd 70.0 70.0 .candidatePositionWholeDrawingRight
  let p0 : ElkPadding := {}
  -- hand: areas 5000, 5000, 4900
  let a := AreaFilter.filterList #[c1, c2, c3] 1.3 p0
  checkEq "area filter keeps the smallest" a.size 1
  check "area filter result" (a[0]!.placementOption == .candidatePositionWholeDrawingRight)
  checkEq "area filter ties kept" (AreaFilter.filterList #[c1, c2] 1.3 (ElkPadding.ofAny 10.0)).size 2
  -- hand: padded 120x70 vs 70x120 = 8400 each; with an asymmetric padding (left 30): 130x50 = 6500
  -- vs 80x100 = 8000
  let pl : ElkPadding := { left := 30.0 }
  let a2 := AreaFilter.filterList #[c1, c2] 1.3 pl
  check "area filter with padding" (a2.size == 1 && a2[0]!.placementOption == .candidatePositionLastPlacedRight)
  -- hand: ratios 2, 0.5, 1 against 1.0 → deviations 1, 0.5, 0
  let r := AspectRatioFilter.filterList #[c1, c2, c3] 1.0 p0
  check "aspect ratio filter" (r.size == 1 && r[0]!.placementOption == .candidatePositionWholeDrawingRight)
  let r2 := AspectRatioFilter.filterList #[c1, c2] 1.0 p0
  check "aspect ratio filter 2" (r2.size == 1 && r2[0]!.placementOption == .candidatePositionLastPlacedBelow)
  -- hand: scales 0.013, 0.01, min(1.3/70, 1/70) = 1/70
  let s := ScaleMeasureFilter.filterList #[c1, c2, c3] 1.3 p0
  check "scale measure filter" (s.size == 1 && s[0]!.placementOption == .candidatePositionWholeDrawingRight)
  checkEq "scale measure filter keeps equal" (ScaleMeasureFilter.filterList #[c1, c1] 1.3 p0).size 2

/-! ### Calculations -/

def calculationTests : Suite := suite "rectpacking.calculations" do
  checkFloat "width lpr" (Calculations.widthLprOrLpb 100.0 80.0 30.0) 110.0
  checkFloat "width lpr keeps drawing" (Calculations.widthLprOrLpb 100.0 50.0 30.0) 100.0
  checkFloat "height lpb" (Calculations.heightLprOrLpb 40.0 30.0 20.0) 50.0
  -- A at (0,0) 30x20, B at (40,0) 20x50 (last placed), C 10x10
  let (g, _, kids) := mkGraph #[(30.0, 20.0), (20.0, 50.0), (10.0, 10.0)]
  let g := g.modifyNode kids[1]! fun n => { n with x := 40.0 }
  let placed := #[kids[0]!, kids[1]!]
  -- hand: x = 70 passes neither (70 < 40, 70 < 70 fail) → 0
  checkFloat "y for lpr without neighbor" (Calculations.calculateYForLpr g 70.0 placed kids[1]! 10.0) 0.0
  -- hand: x = 35: A bottom 20, B bottom 50 (closer to y 0 - 50 < 0 - 20) → 50 + 10
  checkFloat "y for lpr" (Calculations.calculateYForLpr g 35.0 placed kids[1]! 10.0) 60.0
  -- hand: y = 60 passes neither → 0
  checkFloat "x for lpb without neighbor" (Calculations.calculateXForLpb g 60.0 placed kids[1]! 10.0) 0.0
  -- hand: y = 25: A right 30, B right 60 (40 - 60 < 40 - 30) → 60 + 10
  checkFloat "x for lpb" (Calculations.calculateXForLpb g 25.0 placed kids[1]! 10.0) 70.0
  -- hand: LPR at (70, 0): height max(50, 10) - min(0, 0) = 50, width 70 + 10 - 40 = 40
  let lpr := dd 0.0 0.0 .candidatePositionLastPlacedRight 1.3 70.0 0.0
  checkFloat "area lpr" (Calculations.calculateAreaLpr g kids[1]! kids[2]! lpr) 2000.0
  -- hand: LPB at (40, 60): width max(60, 50) - min(40, 40) = 20, height 60 + 10 - 0 = 70
  let lpb := dd 0.0 0.0 .candidatePositionLastPlacedBelow 1.3 40.0 60.0
  checkFloat "area lpb" (Calculations.calculateAreaLpb g kids[1]! kids[2]! lpb) 1400.0
  -- check_special_cases: LPR (2000) vs LPB (1400) → LPB; both orders
  check "special case lpr vs lpb" ((AreaApproximation.checkSpecialCases g lpr lpb kids[1]! kids[2]!).placementOption ==
    .candidatePositionLastPlacedBelow)
  check "special case lpb vs lpr" ((AreaApproximation.checkSpecialCases g lpb lpr kids[1]! kids[2]!).placementOption ==
    .candidatePositionLastPlacedBelow)
  let wdb := dd 0.0 0.0 .candidatePositionWholeDrawingBelow
  let wdr := dd 0.0 0.0 .candidatePositionWholeDrawingRight
  check "special case below pair prefers WDB" ((AreaApproximation.checkSpecialCases g lpb wdb kids[1]! kids[2]!).placementOption ==
    .candidatePositionWholeDrawingBelow)
  check "special case right pair prefers WDR" ((AreaApproximation.checkSpecialCases g wdr lpr kids[1]! kids[2]!).placementOption ==
    .candidatePositionWholeDrawingRight)
  check "special case mixed takes first" ((AreaApproximation.checkSpecialCases g wdr wdb kids[1]! kids[2]!).placementOption ==
    .candidatePositionWholeDrawingRight)

/-! ### Area approximation and the width approximators -/

def approximationTests : Suite := suite "rectpacking.p1" do
  LayoutMetaDataService.ensureInitialized
  -- A 30x30, C 10x10, D 60x10, spacing 10, aspect ratio 1.3, MAX_SCALE_DRIVEN, last place shift
  let (g, root, kids) := mkGraph #[(30.0, 30.0), (10.0, 10.0), (60.0, 10.0)]
  let approx := AreaApproximation.new 1.3 .maxScaleDriven true
  -- hand, C: LPR 50x30 at (40, 0), LPB 30x50, WDR 50x30 at (40, 0), WDB 30x50; scale keeps LPR and
  -- WDR (0.026 > 0.02), area/aspect ratio tie, special case right pair → WDR at (40, 0)
  let (d, g1) ← runElk g (approx.approxBoundingBox #[kids[0]!, kids[1]!] 10.0 {})
  checkFloat "two rects width" d.drawingWidth 50.0
  checkFloat "two rects height" d.drawingHeight 30.0
  check "two rects placement reset to WHOLE_DRAWING" (d.placementOption == .wholeDrawing)
  checkPos "two rects C" g1 kids[1]! 40.0 0.0
  -- hand, D (last placed C at (40, 0)): LPR 120x30, LPB at x 40 (A passes 20 < 40) 100x30,
  -- WDR 120x30, WDB 60x50 at (0, 40); scale 0.0108, 0.013, 0.0108, 0.02 → WDB
  let (d, g2) ← runElk g (approx.approxBoundingBox kids 10.0 {})
  checkFloat "three rects width" d.drawingWidth 60.0
  checkFloat "three rects height" d.drawingHeight 50.0
  checkFloat "three rects next y" d.nextYCoordinate 40.0
  checkPos "three rects A" g2 kids[0]! 0.0 0.0
  checkPos "three rects D" g2 kids[2]! 0.0 40.0
  -- calc_values_for_opt without last place shift: LPR keeps the y of the last placed rectangle
  let noShift := AreaApproximation.new 1.3 .maxScaleDriven false
  let g3 := g.modifyNode kids[0]! fun n => { n with y := 5.0 }
  let lpr := noShift.calcValuesForOpt g3 .candidatePositionLastPlacedRight kids[1]! kids[0]!
    (DrawingData.new 1.3 30.0 35.0 .wholeDrawing) #[kids[0]!] 10.0
  checkFloat "lpr without shift y" lpr.nextYCoordinate 5.0
  checkFloat "lpr without shift x" lpr.nextXCoordinate 40.0
  checkFloat "lpr without shift width" lpr.drawingWidth 50.0
  checkThrows "empty rectangle list" (do let _ ← runElk g (approx.approxBoundingBox #[] 10.0 {}))
  -- GreedyWidthApproximator: aspect ratio from the algorithm default (1.3), padding 0, spacing 10;
  -- the children are reset to (0, 0) first
  let g4 := (g.setNodeProp root CoreOptions.PADDING {}).setNodeProp root CoreOptions.SPACING_NODE_NODE 10.0
  let g4 := g4.modifyNode kids[1]! fun n => { n with x := 99.0, y := 99.0 }
  let (_, _, g4) ← runRP g4 (GreedyWidthApproximator.phase.process root ProgressMonitor.null)
  check "greedy target width" ((g4.node root).props.get InternalProperties.TARGET_WIDTH == some 60.0)
  checkPos "greedy C" g4 kids[1]! 40.0 0.0
  checkPos "greedy D" g4 kids[2]! 0.0 40.0
  -- AREA_DRIVEN: C candidates have areas 1500 (LPR/WDR) and 1500 (LPB/WDB): scale then keeps the
  -- right candidates (hand) → same result for C
  let g5 := g4.setNodeProp root RectPackingOptions.WIDTH_APPROXIMATION_OPTIMIZATION_GOAL .areaDriven
  let (_, _, g5) ← runRP g5 (GreedyWidthApproximator.phase.process root ProgressMonitor.null)
  -- hand, D with AREA_DRIVEN: areas 3600, 3000, 3600, 3000 → LPB 100x30 and WDB 60x50; scale 0.013
  -- vs 0.02 → WDB (0, 40)
  checkPos "area driven D" g5 kids[2]! 0.0 40.0
  check "area driven target width" ((g5.node root).props.get InternalProperties.TARGET_WIDTH == some 60.0)
  -- TargetWidthWidthApproximator: default -1 when unset (elk-rs), else the option value
  let (_, _, g6) ← runRP g (TargetWidthWidthApproximator.phase.process root ProgressMonitor.null)
  check "target width default -1" ((g6.node root).props.get InternalProperties.TARGET_WIDTH == some (-1.0))
  let g7 := g.setNodeProp root RectPackingOptions.WIDTH_APPROXIMATION_TARGET_WIDTH 123.0
  let (_, _, g7) ← runRP g7 (TargetWidthWidthApproximator.phase.process root ProgressMonitor.null)
  check "target width copied" ((g7.node root).props.get InternalProperties.TARGET_WIDTH == some 123.0)
  -- phase factory
  checkEq "greedy phase" (WidthApproximationStrategy.createPhase .greedy).name "GreedyWidthApproximator"
  checkEq "target width phase" (WidthApproximationStrategy.createPhase .targetWidth).name
    "TargetWidthWidthApproximator"
  -- the assembler orders the intermediate processors around the phase
  let assembler : RectPackingAlgorithmAssembler ← AlgorithmAssembler.create IntermediateProcessorStrategy.factory
  assembler.withFailOnMissingPhase false
  assembler.setPhase .p1WidthApproximation (WidthApproximationStrategy.phaseFactory .greedy)
  let config : RectPackingProcessorConfiguration :=
    ((LayoutProcessorConfiguration.create.addBefore .p1WidthApproximation .minSizePreProcessor).addBefore
      .p2Packing .minSizePostProcessor).addBefore .p1WidthApproximation .nodeSizeReorderer
  assembler.addProcessorConfiguration config
  let (algo, _, _) ← runRP g (assembler.build root)
  checkEqR "assembled processors" (algo.map (·.name))
    #["NodeSizeReorderer", "MinSizePreProcessor", "GreedyWidthApproximator", "MinSizePostProcessor"]

/-! ### Intermediate processors -/

def intermediateTests : Suite := suite "rectpacking.intermediate" do
  LayoutMetaDataService.ensureInitialized
  -- NodeSizeReorderer: heights 10, 30, 20, 30 → 30 (n1), 30 (n3), 20, 10 (stable)
  let (g, root, kids) := mkGraph #[(5.0, 10.0), (5.0, 30.0), (5.0, 20.0), (5.0, 30.0)]
  let (_, _, g1) ← runRP g (NodeSizeReorderer.processor.process root ProgressMonitor.null)
  checkEqR "node size reorderer" (g1.node root).children #[kids[1]!, kids[3]!, kids[2]!, kids[0]!]
  -- InteractiveNodeReorderer: n1 → 0, n3 → 0, n4 → 10; free n0, n2
  -- hand: sorted [n3, n1, n4] (ties reversed); insert n3 at 0, n1 at 0, n4 at min(10, 4)
  let (g, root, kids) := mkGraph #[(1.0, 1.0), (1.0, 1.0), (1.0, 1.0), (1.0, 1.0), (1.0, 1.0)]
  let g := g.setNodeProp kids[1]! RectPackingOptions.DESIRED_POSITION 0
  let g := g.setNodeProp kids[3]! RectPackingOptions.DESIRED_POSITION 0
  let g := g.setNodeProp kids[4]! RectPackingOptions.DESIRED_POSITION 10
  let (_, _, g2) ← runRP g (InteractiveNodeReorderer.processor.process root ProgressMonitor.null)
  checkEqR "interactive reorderer order" (g2.node root).children #[kids[1]!, kids[3]!, kids[0]!, kids[2]!, kids[4]!]
  check "current position of n0" ((g2.node kids[0]!).props.get RectPackingOptions.CURRENT_POSITION == some 2)
  check "current position of n4" ((g2.node kids[4]!).props.get RectPackingOptions.CURRENT_POSITION == some 4)
  -- a negative desired position is clamped to 0 (elk-rs)
  let (g, root, kids) := mkGraph #[(1.0, 1.0), (1.0, 1.0)]
  let g := g.setNodeProp kids[1]! RectPackingOptions.DESIRED_POSITION (-5)
  let (_, _, g3) ← runRP g (InteractiveNodeReorderer.processor.process root ProgressMonitor.null)
  checkEqR "negative desired position" (g3.node root).children #[kids[1]!, kids[0]!]
  -- MinSizePreProcessor: MINIMUM_SIZE with minimum (50, 0) and DEFAULT_MINIMUM_SIZE → (50, 20)
  let (g, root, _) := mkGraph #[]
  let g := g.setNodeProp root CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.minimumSize])
  let g := g.setNodeProp root CoreOptions.NODE_SIZE_MINIMUM ⟨50.0, 0.0⟩
  let (_, _, g4) ← runRP g (MinSizePreProcessor.processor.process root ProgressMonitor.null)
  check "min width" ((g4.node root).props.get InternalProperties.MIN_WIDTH == some 50.0)
  check "min height (default minimum)" ((g4.node root).props.get InternalProperties.MIN_HEIGHT == some 20.0)
  let (g, root, _) := mkGraph #[]
  let (_, _, g5) ← runRP g (MinSizePreProcessor.processor.process root ProgressMonitor.null)
  check "no minimum size constraint" ((g5.node root).props.get InternalProperties.MIN_WIDTH == some 0.0)
  -- MinSizePostProcessor
  let g6 := (g4.setNodeProp root InternalProperties.TARGET_WIDTH 40.0)
  let (_, _, g6) ← runRP g6 (MinSizePostProcessor.processor.process root ProgressMonitor.null)
  check "target width raised to min width" ((g6.node root).props.get InternalProperties.TARGET_WIDTH == some 50.0)
  let g7 := (g4.setNodeProp root InternalProperties.TARGET_WIDTH 70.0)
  let (_, _, g7) ← runRP g7 (MinSizePostProcessor.processor.process root ProgressMonitor.null)
  check "target width kept" ((g7.node root).props.get InternalProperties.TARGET_WIDTH == some 70.0)
  let (_, _, g8) ← runRP g (MinSizePostProcessor.processor.process root ProgressMonitor.null)
  check "unset values default to 0" ((g8.node root).props.get InternalProperties.TARGET_WIDTH == some 0.0)
  checkEq "factory names" ((ElkEnum.values : Array IntermediateProcessorStrategy).map
    (·.createProcessor.name)) #["NodeSizeReorderer", "InteractiveNodeReorderer", "MinSizePreProcessor",
      "MinSizePostProcessor"]

/-! ### Block, block row, rect row -/

def blockTests : Suite := suite "rectpacking.block" do
  LayoutMetaDataService.ensureInitialized
  -- r1 30x20, r2 20x10, r3 40x30, spacing 10
  let (g, _, kids) := mkGraph #[(30.0, 20.0), (20.0, 10.0), (40.0, 30.0)]
  let r1 := kids[0]!
  let r2 := kids[1]!
  let r3 := kids[2]!
  let ((blk, h50, h100, w100, w60, changed, rowAfterAdd, rowAfterPlace), arena, g) ← runRP g do
    let row ← RectRow.create 0.0 10.0
    let b ← Block.create 0.0 0.0 row 10.0
    RectRow.addBlock row b
    Block.addChild b r1
    Block.addChild b r2
    Block.addChildInNewRow b r3
    let rowAfterAdd ← RectPackingM.getRow row
    let h50 ← Block.heightForTargetWidth b 50.0
    let h100 ← Block.heightForTargetWidth b 100.0
    let w100 ← Block.widthForTargetHeight b 100.0
    let w60 ← Block.widthForTargetHeight b 60.0
    let blk ← RectPackingM.getBlock b
    let changed ← Block.placeRectsIn b 50.0
    let rowAfterPlace ← RectPackingM.getRow row
    return (blk, h50, h100, w100, w60, changed, rowAfterAdd, rowAfterPlace)
  -- hand: r1 (0,0), r2 (40,0), r3 in a new block row at y 20 + 10
  checkEq "one block in the arena" arena.blocks.size 1
  checkFloat "block width" blk.width 60.0
  checkFloat "block height" blk.height 60.0
  checkFloat "block min width" blk.minWidth 50.0
  checkFloat "block max height" blk.maxHeight 80.0
  -- hand: 80 / 3 - 10 * (2 / 3)
  checkFloat "block average height" blk.averageHeight 20.0 1e-9
  checkFloat "block smallest rect width" blk.smallestRectWidth 20.0
  checkFloat "block smallest rect height" blk.smallestRectHeight 10.0
  checkEq "block rows" blk.rows.size 2
  checkFloat "row width notified" rowAfterAdd.width 60.0
  checkFloat "row height notified" rowAfterAdd.height 60.0
  -- hand: in 50: rows r1 | r2 | r3 → 20 + 10 + 10 + 10 + 30
  checkFloat "height for width 50" h50 80.0
  -- hand: in 100: rows r1 r2 | r3 → 20 + 10 + 30
  checkFloat "height for width 100" h100 60.0
  checkFloat "width for height 100 (all stacked fit)" w100 50.0
  -- hand: binary search between 50 and 60 never fits into 60 → the block width
  checkFloat "width for height 60" w60 60.0
  check "place rects in 50 changed the size" changed
  checkFloat "row width after place" rowAfterPlace.width 40.0
  checkFloat "row height after place" rowAfterPlace.height 80.0
  checkPos "placed r1" g r1 0.0 0.0
  checkPos "placed r2" g r2 0.0 30.0
  checkPos "placed r3" g r3 0.0 50.0
  -- location, removal, expansion
  let ((blk, rowRemoved), _, g) ← runRP g do
    let row ← RectRow.create 0.0 10.0
    let b ← Block.create 0.0 0.0 row 10.0
    RectRow.addBlock row b
    Block.addChild b r1
    Block.addChild b r2
    Block.addChildInNewRow b r3
    let _ ← Block.placeRectsIn b 50.0
    Block.setLocation b 5.0 7.0
    Block.removeChild b r2
    let rowRemoved ← RectPackingM.getRow row
    Block.expand b 10.0 20.0
    return (← RectPackingM.getBlock b, rowRemoved)
  checkEq "rows after remove" blk.rows.size 2
  checkFloat "row width after remove" rowRemoved.width 40.0
  checkFloat "row height after remove" rowRemoved.height 60.0
  checkFloat "block min height after remove" blk.minHeight 30.0
  -- hand: (20 + 10 + 30 + 10) / 2 - 10 / 2
  checkFloat "block average height after remove" blk.averageHeight 30.0
  checkFloat "block width after expand" blk.width 50.0
  checkFloat "block height after expand" blk.height 80.0
  -- hand: r1 at (5, 7) grows to 50 x (20 + 10); r3 at (5, 57) moves down by 1 * 10, 50 x 40
  checkShape "expanded r1" g r1 5.0 7.0 50.0 30.0
  checkShape "expanded r3" g r3 5.0 67.0 50.0 40.0
  -- BlockRow alone
  let (row, g) ← runElk g do
    let row := BlockRow.new 0.0 0.0 5.0
    let row ← row.addRectangle r1
    let row ← row.addRectangle r2
    row.removeRectangle r1 true
  checkFloat "block row width after removal" row.width 20.0
  checkFloat "block row height after removal" row.height 10.0
  checkPos "block row re-placed r2" g r2 0.0 0.0

/-! ### Block stack, rect row, rows storage -/

def stackTests : Suite := suite "rectpacking.stack" do
  LayoutMetaDataService.ensureInitialized
  let (g, _, kids) := mkGraph #[(30.0, 20.0), (20.0, 40.0), (10.0, 10.0)]
  let a := kids[0]!
  let c := kids[1]!
  let e := kids[2]!
  let ((st, st2, wFixed, stacksBefore, b1Stack, b1StackAfterReset, rowRemoved), _, g) ← runRP g do
    let row ← RectRow.create 0.0 10.0
    let b1 ← Block.create 0.0 0.0 row 10.0
    let b2 ← Block.create 0.0 30.0 row 10.0
    let b3 ← Block.create 50.0 0.0 row 10.0
    Block.addChild b1 a
    Block.addChild b2 c
    Block.addChild b3 e
    let s ← BlockStack.create 0.0 0.0 10.0
    BlockStack.addBlock s b1
    BlockStack.addBlock s b2
    let st ← RectPackingM.getStack s
    BlockStack.setLocation s 10.0 5.0
    BlockStack.placeRectsIn s 100.0
    let st2 ← RectPackingM.getStack s
    let wFixed ← BlockStack.getWidthForFixedHeight s 100.0
    RectRow.addBlock row b1
    RectRow.addBlock row b2
    RectRow.addBlock row b3
    RectRow.calculateBlockStacks row
    let stacksBefore := (← RectPackingM.getRow row).stacks
    let b1Stack ← Block.stackOf b1
    RectRow.resetStacks row
    let b1StackAfterReset ← Block.stackOf b1
    RectRow.calculateBlockStacks row
    RectRow.setY row 100.0
    RectRow.removeBlock row b3
    let rowRemoved ← RectPackingM.getRow row
    return (st, st2, wFixed, stacksBefore, b1Stack, b1StackAfterReset, rowRemoved)
  -- hand: width max(30, 20), height 20 + (40 + 10)
  checkFloat "stack width" st.width 30.0
  checkFloat "stack height" st.height 70.0
  -- hand: place from y 5: 5 + 20 + 10 = 35, 35 + 40 + 10 = 85 (the trailing spacing is kept)
  checkFloat "stack height after place" st2.height 85.0
  checkFloat "stack width after place" st2.width 30.0
  -- hand: minimum width 30 = stack width → no search
  checkFloat "width for fixed height" wFixed 30.0
  -- blocks b1 and b2 share x 10 → one stack; b3 at x 50 → second stack
  checkEq "calculated stacks" stacksBefore.size 2
  check "b1 in the first new stack" (b1Stack == some stacksBefore[0]!)
  check "reset stacks drops the stack (Weak)" b1StackAfterReset.isNone
  -- set_y moves the stacks by 100: a from y 5 to 105, c from 35 to 135, e from 0 to 100
  checkPos "a after set y" g a 10.0 105.0
  checkPos "c after set y" g c 10.0 135.0
  checkPos "e after set y" g e 50.0 100.0
  -- hand: row width 30 + (20 + 10) + (10 + 10) = 80, minus (10 + 10) after removing b3
  checkFloat "row width after remove block" rowRemoved.width 60.0
  checkFloat "row height after remove block" rowRemoved.height 40.0
  checkEq "row children after remove block" rowRemoved.children.size 2
  -- notify deferral: a second mutably borrowed child aborts the update
  let (g, _, kids) := mkGraph #[(30.0, 20.0), (20.0, 40.0)]
  let ((before, after), _, _) ← runRP g do
    let row ← RectRow.create 0.0 10.0
    let b1 ← Block.create 0.0 0.0 row 10.0
    let b2 ← Block.create 40.0 0.0 row 10.0
    RectRow.addBlock row b1
    RectRow.addBlock row b2
    Block.addChild b2 kids[1]!
    let before ← RectPackingM.getRow row
    RectPackingM.withBorrowed #[b2] (Block.addChild b1 kids[0]!)
    let after ← RectPackingM.getRow row
    return (before, after)
  -- hand: b2 notifies with b1 (0 x 0) readable: width 0 + (20 + 10), height 40
  checkFloat "row width before deferral" before.width 30.0
  checkFloat "row width unchanged (deferred)" after.width 30.0
  -- rows storage and drawing dimensions of rows
  let (g, root, _) := mkGraph #[]
  let ((stored, taken, gone, dims), _, _) ← runRP g do
    let r1 ← RectRow.create 0.0 10.0
    let r2 ← RectRow.create 0.0 10.0
    RectRow.setWidth r1 50.0
    RectRow.setHeight r1 20.0
    RectRow.setWidth r2 70.0
    RectRow.setHeight r2 5.0
    let key ← RowsStorage.storeRows root #[r1, r2]
    let stored ← RowsStorage.getRows key
    let taken ← RowsStorage.takeRows key
    let gone ← RowsStorage.getRows key
    let dims ← DrawingUtil.calculateDimensions #[r1, r2] 10.0
    return (stored.map (·.size), taken.map (·.size), gone, dims)
  checkEq "stored rows" stored (some 2)
  checkEq "taken rows" taken (some 2)
  check "rows removed after take" gone.isNone
  checkFloat "rows dimension width" dims.x 70.0
  -- hand: 20 + (5 + 10)
  checkFloat "rows dimension height" dims.y 35.0

/-! ### Packing phase (p2packing) -/

def packingTests : Suite := suite "rectpacking.p2" do
  LayoutMetaDataService.ensureInitialized
  -- InitialPlacement.place: width 100, spacing 10: a 30x30, b 30x28, c 50x10, d 20x60
  let (g, root, kids) := mkGraph #[(30.0, 30.0), (30.0, 28.0), (50.0, 10.0), (20.0, 60.0)]
  let ((rows, rowData, blockData, sim), _, g1) ← runRP g do
    let rows ← InitialPlacement.place kids 100.0 10.0
    let mut rowData := #[]
    let mut blockData := #[]
    for r in rows do
      let row ← RectPackingM.getRow r
      rowData := rowData.push row
      for b in row.children do
        blockData := blockData.push (← RectPackingM.getBlock b)
    let sim ← InitialPlacement.isSimilarHeight (← RectRow.getFirstBlock rows[0]!) kids[2]! 10.0
    return (rows, rowData, blockData, sim)
  -- hand: a at (0, 0), b at (40, 0) in the same block (28 within 50 % of 30); c: 70 + 50 + 10 > 100
  -- → new row at y 30 + 10, new block; d: 50 + 20 + 10 = 80 fits, height 60 not similar to 10 →
  -- new block at x 50 + 10
  checkEq "initial rows" rows.size 2
  checkEq "row 0 blocks" rowData[0]!.children.size 1
  checkEq "row 1 blocks" rowData[1]!.children.size 2
  checkFloat "row 1 y" rowData[1]!.y 40.0
  checkFloat "row 0 width" rowData[0]!.width 70.0
  checkFloat "block 0 width" blockData[0]!.width 70.0
  checkFloat "block 2 x" blockData[2]!.x 60.0
  check "c is not of similar height to the first block" (!sim)
  checkPos "placed a" g1 kids[0]! 0.0 0.0
  checkPos "placed b" g1 kids[1]! 40.0 0.0
  checkPos "placed c" g1 kids[2]! 0.0 40.0
  checkPos "placed d" g1 kids[3]! 60.0 40.0
  -- IN_NEW_ROW forces a row break
  let g2 := g.setNodeProp kids[1]! RectPackingOptions.IN_NEW_ROW true
  let (rows2, _, _) ← runRP g2 (InitialPlacement.place kids 1000.0 10.0)
  checkEq "in new row breaks the row" rows2.size 2
  -- row height reevaluation on the parent: every rectangle opens a new block
  let g3 := g.setNodeProp root RectPackingOptions.PACKING_COMPACTION_ROW_HEIGHT_REEVALUATION true
  let (blocks3, _, _) ← runRP g3 do
    let rows ← InitialPlacement.place #[kids[0]!, kids[1]!] 1000.0 10.0
    return (← RectPackingM.getRow rows[0]!).children.size
  checkEq "row height reevaluation: one block per rectangle" blocks3 2
  -- SimplePlacement: target width 100 (set as TARGET_WIDTH), padding 0, spacing 10
  let gs := ((g.setNodeProp root InternalProperties.TARGET_WIDTH 100.0).setNodeProp root
    CoreOptions.SPACING_NODE_NODE 10.0).setNodeProp root CoreOptions.PADDING {}
  let (_, arena, gs) ← runRP gs (SimplePlacement.phase.process root ProgressMonitor.null)
  -- hand: rows 70x30 and (50 + 10 + 20)x60 → 80 x (30 + 10 + 60)
  check "simple drawing width" ((gs.node root).props.get InternalProperties.DRAWING_WIDTH == some 80.0)
  check "simple drawing height" ((gs.node root).props.get InternalProperties.DRAWING_HEIGHT == some 100.0)
  check "simple rows stored" ((gs.node root).props.get InternalProperties.ROWS).isSome
  checkEq "simple stacks (one per block)" arena.stacks.size 3
  -- NoPlacement keeps the positions: (0,0) 30x30 ... drawing = bounding box of the nodes
  let gn := (g.modifyNode kids[3]! fun n => { n with x := 100.0, y := 5.0 }).setNodeProp root CoreOptions.PADDING {}
  let (_, _, gn) ← runRP gn (NoPlacement.phase.process root ProgressMonitor.null)
  check "none drawing width" ((gn.node root).props.get InternalProperties.DRAWING_WIDTH == some 120.0)
  check "none drawing height" ((gn.node root).props.get InternalProperties.DRAWING_HEIGHT == some 65.0)
  check "none stores no rows" ((gn.node root).props.get InternalProperties.ROWS).isNone
  -- MIN_HEIGHT larger than the drawing: the additional height is counted twice (Rust/Java)
  let gm := (gn.setNodeProp root InternalProperties.MIN_HEIGHT 100.0)
  let (_, _, gm) ← runRP gm (NoPlacement.phase.process root ProgressMonitor.null)
  check "none additional height" ((gm.node root).props.get InternalProperties.ADDITIONAL_HEIGHT == some 35.0)
  check "none drawing height with additional height" ((gm.node root).props.get InternalProperties.DRAWING_HEIGHT == some 135.0)
  -- factories
  checkEqR "packing phases" ((ElkEnum.values : Array PackingStrategy).map (·.createPhase.name))
    #["Compactor", "SimplePlacement", "NoPlacement"]
  checkEqR "whitespace phases" ((ElkEnum.values : Array WhiteSpaceEliminationStrategy).map (·.createPhase.name))
    #["EqualWhitespaceEliminator", "ToAspectratioNodeExpander", "NoopWhitespaceEliminator"]

/-! ### Whitespace elimination (p3whitespaceelimination) -/

def whitespaceTests : Suite := suite "rectpacking.p3" do
  LayoutMetaDataService.ensureInitialized
  let (g, root, kids) := mkGraph #[(30.0, 30.0), (30.0, 28.0), (50.0, 10.0)]
  let g := ((g.setNodeProp root InternalProperties.TARGET_WIDTH 100.0).setNodeProp root
    CoreOptions.SPACING_NODE_NODE 10.0).setNodeProp root CoreOptions.PADDING {}
  -- simple placement, then the equal whitespace eliminator expands to DRAWING_WIDTH 120 and
  -- additional height 20 (10 per row)
  let ((), _, g1) ← runRP g do
    SimplePlacement.phase.process root ProgressMonitor.null
    ElkM.setNodeProp root InternalProperties.DRAWING_WIDTH 120.0
    ElkM.setNodeProp root InternalProperties.ADDITIONAL_HEIGHT 20.0
    EqualWhitespaceEliminator.phase.process root ProgressMonitor.null
  -- hand: row 0 (a b, one stack, width 70) grows by 50: the block grows to 120, both rectangles by
  -- 25 → a 55 wide at 0, b at 40 + 25 = 65; row height 30 + 10; row 1 moves down by 10
  checkShape "expanded a" g1 kids[0]! 0.0 0.0 55.0 40.0
  checkShape "expanded b" g1 kids[1]! 65.0 0.0 55.0 40.0
  checkShape "expanded c" g1 kids[2]! 0.0 50.0 120.0 20.0
  -- without rows: UnsupportedConfigurationException
  checkThrows "no rows" (do let _ ← runRP g (EqualWhitespaceEliminator.phase.process root ProgressMonitor.null))
  -- ToAspectratioNodeExpander: 70 x 50 drawing (rows 70x30 and 50x10) with aspect ratio 2 → width
  -- 50 * 2
  let (_, _, g2) ← runRP (g.setNodeProp root CoreOptions.ASPECT_RATIO 2.0) do
    SimplePlacement.phase.process root ProgressMonitor.null
    ToAspectratioNodeExpander.phase.process root ProgressMonitor.null
  check "to aspect ratio width" ((g2.node root).props.get InternalProperties.DRAWING_WIDTH == some 100.0)
  -- … and aspect ratio 0.5 (1.4 ≥ 0.5) → additional height 70 / 0.5 - 50 = 90, height 50 + 90
  let (_, _, g3) ← runRP (g.setNodeProp root CoreOptions.ASPECT_RATIO 0.5) do
    SimplePlacement.phase.process root ProgressMonitor.null
    ToAspectratioNodeExpander.phase.process root ProgressMonitor.null
  check "to aspect ratio additional height" ((g3.node root).props.get InternalProperties.ADDITIONAL_HEIGHT == some 90.0)
  check "to aspect ratio height" ((g3.node root).props.get InternalProperties.DRAWING_HEIGHT == some 140.0)
  -- RectangleExpansion of no rows is a no-op
  let (_, _, g4) ← runRP g (RectangleExpansion.expand #[] 100.0 10.0 0.0)
  checkPos "no rows: unchanged" g4 kids[0]! 0.0 0.0

/-! ### Provider: `rectpacking_compaction_test.rs`, `padding_test.rs`, `issue_583_test.rs` -/

/-- Runs the provider directly (like the elk-rs tests, not through the engine). -/
private def runLayout (g : ElkGraph) (root : NodeId) : IO ElkGraph := do
  let (_, g) ← ElkM.run (RectPackingLayoutProvider.layout root ProgressMonitor.null) g
  return g

/-- `create_compaction_graph(target_width, spacing)` + `create_node`s. -/
private def compactionGraph (targetWidth spacing : Float) (sizes : Array (Float × Float)) :
    ElkGraph × NodeId × Array NodeId :=
  let (g, root, kids) := mkGraph sizes
  let g := g.setNodeProp root CoreOptions.ALGORITHM RectPackingOptions.ALGORITHM_ID
  let g := g.setNodeProp root RectPackingOptions.WIDTH_APPROXIMATION_TARGET_WIDTH targetWidth
  let g := g.setNodeProp root RectPackingOptions.WIDTH_APPROXIMATION_STRATEGY .targetWidth
  let g := g.setNodeProp root CoreOptions.SPACING_NODE_NODE spacing
  let g := g.setNodeProp root CoreOptions.PADDING (ElkPadding.ofAny 0.0)
  (g, root, kids)

private def checkSizeE (name : String) (g : ElkGraph) (n : NodeId) (w h : Float) : TestM Unit := do
  checkFloat s!"{name} width" (g.node n).width w 1.0
  checkFloat s!"{name} height" (g.node n).height h 1.0

private def checkPosE (name : String) (g : ElkGraph) (n : NodeId) (x y : Float) : TestM Unit := do
  checkFloat s!"{name} x" (g.node n).x x 1.0
  checkFloat s!"{name} y" (g.node n).y y 1.0

def providerTests : Suite := suite "rectpacking.provider" do
  LayoutMetaDataService.ensureInitialized
  check "provider registered" (← LayoutProvider.isRegistered RectPackingOptions.ALGORITHM_ID)
  -- test_place_block_from_next_row_on_top
  let (g, root, k) := compactionGraph 110.0 10.0
    #[(30.0, 70.0), (30.0, 10.0), (30.0, 10.0), (30.0, 50.0), (30.0, 50.0), (100.0, 10.0), (100.0, 10.0)]
  let g ← runLayout g root
  checkSizeE "on top: graph" g root 110.0 110.0
  checkPosE "on top: n1" g k[0]! 0.0 0.0
  checkPosE "on top: n2" g k[1]! 40.0 0.0
  checkPosE "on top: n3" g k[2]! 80.0 0.0
  checkPosE "on top: n4" g k[3]! 40.0 20.0
  checkPosE "on top: n5" g k[4]! 80.0 20.0
  checkPosE "on top: n6" g k[5]! 0.0 80.0
  -- test_place_block_from_next_row_on_top_does_not_work
  let (g, root, k) := compactionGraph 110.0 10.0
    #[(30.0, 70.0), (40.0, 10.0), (30.0, 10.0), (30.0, 50.0), (30.0, 50.0), (100.0, 10.0), (100.0, 10.0)]
  let g ← runLayout g root
  checkSizeE "on top fails: graph" g root 100.0 170.0
  checkPosE "on top fails: n1" g k[0]! 0.0 0.0
  checkPosE "on top fails: n2" g k[1]! 40.0 0.0
  checkPosE "on top fails: n3" g k[2]! 40.0 20.0
  checkPosE "on top fails: n4" g k[3]! 0.0 80.0
  checkPosE "on top fails: n5" g k[4]! 40.0 80.0
  -- test_absorb_block
  let (g, root, k) := compactionGraph 110.0 10.0
    #[(30.0, 70.0), (30.0, 30.0), (30.0, 30.0), (30.0, 30.0), (30.0, 30.0), (100.0, 10.0), (100.0, 10.0)]
  let g ← runLayout g root
  checkSizeE "absorb: graph" g root 110.0 110.0
  checkPosE "absorb: n1" g k[0]! 0.0 0.0
  checkPosE "absorb: n2" g k[1]! 40.0 0.0
  checkPosE "absorb: n3" g k[2]! 80.0 0.0
  checkPosE "absorb: n4" g k[3]! 40.0 40.0
  checkPosE "absorb: n5" g k[4]! 80.0 40.0
  checkPosE "absorb: n6" g k[5]! 0.0 80.0
  -- test_compact_block
  let (g, root, k) := compactionGraph 190.0 10.0
    #[(30.0, 70.0), (30.0, 30.0), (30.0, 30.0), (30.0, 30.0), (30.0, 30.0)]
  let g ← runLayout g root
  checkSizeE "compact: graph" g root 110.0 70.0
  checkPosE "compact: n1" g k[0]! 0.0 0.0
  checkPosE "compact: n2" g k[1]! 40.0 0.0
  checkPosE "compact: n3" g k[2]! 80.0 0.0
  checkPosE "compact: n4" g k[3]! 40.0 40.0
  checkPosE "compact: n5" g k[4]! 80.0 40.0
  -- test_split_block
  let (g, root, k) := compactionGraph 110.0 10.0
    #[(30.0, 70.0), (30.0, 30.0), (30.0, 30.0), (30.0, 30.0), (30.0, 30.0), (30.0, 30.0), (100.0, 10.0)]
  let g ← runLayout g root
  checkSizeE "split: graph" g root 110.0 130.0
  checkPosE "split: n1" g k[0]! 0.0 0.0
  checkPosE "split: n2" g k[1]! 40.0 0.0
  checkPosE "split: n3" g k[2]! 80.0 0.0
  checkPosE "split: n4" g k[3]! 40.0 40.0
  checkPosE "split: n5" g k[4]! 80.0 40.0
  checkPosE "split: n6" g k[5]! 0.0 80.0
  checkPosE "split: n7" g k[6]! 0.0 120.0
  -- test_place_block_from_next_row_right
  let (g, root, k) := compactionGraph 110.0 10.0 #[(30.0, 70.0), (30.0, 30.0), (20.0, 20.0), (30.0, 70.0)]
  let g ← runLayout g root
  checkSizeE "right: graph" g root 110.0 70.0
  checkPosE "right: n1" g k[0]! 0.0 0.0
  checkPosE "right: n2" g k[1]! 40.0 0.0
  checkPosE "right: n3" g k[2]! 40.0 40.0
  checkPosE "right: n4" g k[3]! 80.0 0.0
  -- test_place_block_from_current_row_on_top
  let (g, root, k) := compactionGraph 150.0 10.0 #[(30.0, 70.0), (30.0, 10.0), (30.0, 10.0), (30.0, 50.0)]
  let g ← runLayout g root
  checkSizeE "current row: graph" g root 110.0 70.0
  checkPosE "current row: n1" g k[0]! 0.0 0.0
  checkPosE "current row: n2" g k[1]! 40.0 0.0
  checkPosE "current row: n3" g k[2]! 80.0 0.0
  checkPosE "current row: n4" g k[3]! 40.0 20.0
  -- padding_test.rs: four 30x30 nodes, aspect ratio 1.3, spacing 10
  let paddingGraph (p : ElkPadding) : ElkGraph × NodeId × Array NodeId :=
    let (g, root, kids) := mkGraph #[(30.0, 30.0), (30.0, 30.0), (30.0, 30.0), (30.0, 30.0)]
    let g := g.setNodeProp root CoreOptions.ALGORITHM RectPackingOptions.ALGORITHM_ID
    let g := g.setNodeProp root RectPackingOptions.ASPECT_RATIO 1.3
    let g := g.setNodeProp root CoreOptions.SPACING_NODE_NODE 10.0
    (g.setNodeProp root CoreOptions.PADDING p, root, kids)
  let (g, root, k) := paddingGraph { top := 1000.0 }
  let g ← runLayout g root
  checkSizeE "top padding: graph" g root 150.0 1030.0
  for i in [0:4] do checkPosE s!"top padding: n{i}" g k[i]! (40.0 * i.toFloat) 1000.0
  let (g, root, k) := paddingGraph { left := 1000.0 }
  let g ← runLayout g root
  checkSizeE "left padding: graph" g root 1030.0 150.0
  for i in [0:4] do checkPosE s!"left padding: n{i}" g k[i]! 1000.0 (40.0 * i.toFloat)
  let (g, root, k) := paddingGraph { bottom := 1000.0 }
  let g ← runLayout g root
  checkSizeE "bottom padding: graph" g root 150.0 1030.0
  for i in [0:4] do checkPosE s!"bottom padding: n{i}" g k[i]! (40.0 * i.toFloat) 0.0
  let (g, root, k) := paddingGraph { right := 1000.0 }
  let g ← runLayout g root
  checkSizeE "right padding: graph" g root 1030.0 150.0
  for i in [0:4] do checkPosE s!"right padding: n{i}" g k[i]! 0.0 (40.0 * i.toFloat)
  -- issue_583_test.rs: test_decrease_approximated_width
  let (g, root, _) := mkGraph #[(30.0, 30.0), (10.0, 10.0), (30.0, 30.0), (40.0, 10.0)]
  let g := g.setNodeProp root CoreOptions.ALGORITHM RectPackingOptions.ALGORITHM_ID
  let g := g.setNodeProp root CoreOptions.SPACING_NODE_NODE 0.0
  let g := g.setNodeProp root CoreOptions.PADDING (ElkPadding.ofAny 0.0)
  let g := g.setNodeProp root RectPackingOptions.PACKING_STRATEGY .none
  let g ← runLayout g root
  checkFloat "issue 583: width with approximation only" (g.node root).width 60.0 1.0
  let g := g.setNodeProp root RectPackingOptions.PACKING_STRATEGY .compaction
  let g ← runLayout g root
  checkFloat "issue 583: width with compaction" (g.node root).width 40.0 1.0
  -- the assembled processors (ORDER_BY_SIZE, INTERACTIVE)
  let (g, root, _) := mkGraph #[(10.0, 10.0)]
  let g := (g.setNodeProp root RectPackingOptions.ORDER_BY_SIZE true).setNodeProp root
    RectPackingOptions.INTERACTIVE true
  let (algo, _, _) ← runRP g (RectPackingLayoutProvider.assembleAlgorithm root)
  checkEqR "assembled algorithm" (algo.map (·.name))
    #["NodeSizeReorderer", "InteractiveNodeReorderer", "MinSizePreProcessor", "GreedyWidthApproximator",
      "MinSizePostProcessor", "Compactor", "NoopWhitespaceEliminator"]
  -- TRYBOX: 70 ≥ 10 + 10 + 10 → stackable, packed; 20/20/20 → box layout (priority order)
  let (g, root, k) := mkGraph #[(20.0, 20.0), (20.0, 20.0), (20.0, 20.0)]
  let g := g.setNodeProp root RectPackingOptions.TRYBOX true
  let g ← runLayout g root
  check "trybox: priorities set" ((g.node k[0]!).props.get CoreOptions.PRIORITY == some 3)
  -- box layout with the values of the engine snapshot: padding 12, spacing 20 (core defaults, not
  -- the rectangle packing defaults); one box per row (oracle: (12, 12), (12, 52), (12, 92))
  checkPosE "trybox: box n0" g k[0]! 12.0 12.0
  checkPosE "trybox: box n1" g k[1]! 12.0 52.0
  checkPosE "trybox: box n2" g k[2]! 12.0 92.0
  checkSizeE "trybox: graph" g root 44.0 124.0
  -- the interactive visitor
  let (g, root, _) := mkGraph #[(10.0, 10.0)]
  let g := g.setNodeProp root CoreOptions.ALGORITHM "rectpacking"
  let (_, g) ← runElk g (InteractiveRectPackingGraphVisitor.visitor.visit (.node root))
  check "visitor sets interactive" ((g.node root).props.get? RectPackingOptions.INTERACTIVE == some true)
  let (g, root, _) := mkGraph #[]
  let g := g.setNodeProp root CoreOptions.ALGORITHM "rectpacking"
  let (_, g) ← runElk g (InteractiveRectPackingGraphVisitor.setInteractiveOptions root)
  check "visitor skips nodes without children" ((g.node root).props.get? RectPackingOptions.INTERACTIVE).isNone

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
    let expectedFile := dir / s!"{name}.expected.json"
    if ← expectedFile.pathExists then
      let expected ← IO.FS.readFile expectedFile
      match ← Elk.Api.layoutJson input "{}" (lenient := false) (pretty := true) (sortKeys := true) with
      | .error e => report s!"{name}: layout" false e
      | .ok actual => checkEq s!"{name}: matches oracle" actual expected
    else
      -- no oracle output: elk-rs panics (e.g. NONE packing + a whitespace eliminator)
      match ← Elk.Api.layoutJson input "{}" (lenient := false) (pretty := true) (sortKeys := true) with
      | .error _ => report s!"{name}: error like the oracle" true
      | .ok _ => report s!"{name}: error like the oracle" false "layout succeeded"

/-- The fixture directory: `ELK_RECTPACKING_FIXTURES<suffix>` overrides the default (used for
large parity runs outside the repository). -/
private def fixtureDir (envSuffix : String) (default : System.FilePath) : IO (System.FilePath × Nat) := do
  match ← IO.getEnv s!"ELK_RECTPACKING_FIXTURES{envSuffix}" with
  | some d => return (d, 1)
  | none => return (default, 40)

/-- `rectpacking.fixtures`: `Elk.Api.layoutJson` reproduces the stock elk-rs output byte-for-byte.
The stock oracle registers the four enum options without a value parser, so their strings in the
JSON are ignored (by the port as well). -/
def fixtureTests : Suite := suite "rectpacking.fixtures" do
  LayoutMetaDataService.ensureInitialized
  let (dir, minimum) ← fixtureDir "" "tests/fixtures/rectpacking"
  checkFixtures dir minimum

/-- Java-like variant of the four enum options of the rectangle packing (the registration of
`RectPackingMetaDataProvider.registerOptions` plus the enum choices and the lenient enum parser).
Registering it replaces the entries in place. Test only: elk-rs registers no parser. -/
def enumParserProvider : LayoutMetaDataProvider where
  apply r :=
    let withParser {α : Type} [ElkEnum α] (r : Registry) (property : Property α)
        (name description group : String) : Registry :=
      r.registerOption
        { id := property.id, type := .enum, defaultValue := property.default.map PropCodec.enc,
          name, description, targets := EnumSet.of #[.parents], visibility := .visible, group,
          choices := LayoutOptionData.enumChoices α, parser := some (LayoutOptionData.enumParser α) }
    let r := withParser r RectPackingOptions.WIDTH_APPROXIMATION_STRATEGY "Width Approximation Strategy"
      "Strategy for finding an initial width of the drawing." "widthApproximation"
    let r := withParser r RectPackingOptions.WIDTH_APPROXIMATION_OPTIMIZATION_GOAL "Optimization Goal"
      "Optimization goal for approximation of the bounding box given by the first iteration."
      "widthApproximation"
    let r := withParser r RectPackingOptions.PACKING_STRATEGY "Compaction Strategy"
      "Strategy for finding an initial placement on nodes." "packing"
    withParser r RectPackingOptions.WHITE_SPACE_ELIMINATION_STRATEGY "White Space Approximation Strategy"
      "Strategy for expanding nodes to eliminate whitespace." "whiteSpaceElimination"

/-- Runs `action` with `enumParserProvider` installed, then restores the registry. -/
def withEnumParsers {α : Type} (action : IO α) : IO α := do
  let snapshot ← LayoutMetaDataService.getInstance
  LayoutMetaDataService.registerLayoutMetaDataProvider enumParserProvider
  try action finally LayoutMetaDataService.instanceRef.set snapshot

/-- `rectpacking.fixtures.enum`: with the enum parsers installed, the output equals the output of
an elk-rs build whose rectangle packing provider registers the same parsers (the only change to
elk-rs); this reaches every strategy from JSON. Inputs without an expected file are the models
on which elk-rs panics (`NONE` packing with a whitespace eliminator). -/
def enumFixtureTests : Suite := suite "rectpacking.fixtures.enum" do
  LayoutMetaDataService.ensureInitialized
  let (dir, minimum) ← fixtureDir "_ENUM" "tests/fixtures/rectpacking/enum"
  let st ← get
  let (_, st') ← withEnumParsers ((checkFixtures dir minimum).run st)
  set st'

def suites : Array Suite :=
  #[metadataTests, drawingTests, filterTests, calculationTests, approximationTests, intermediateTests,
    blockTests, stackTests, packingTests, whitespaceTests, providerTests, fixtureTests, enumFixtureTests]

end Tests.RectPacking
