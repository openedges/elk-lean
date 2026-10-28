import Elk.Core.Alg
import Elk.Core.LayoutProvider
import Elk.Core.Options
import Elk.Core.Util.ElkUtil
import Elk.Core.Util.BoxLayoutProvider
import Elk.Alg.Common.NodeSpacing.NodeMicroLayout
import Elk.Alg.RectPacking.RectPackingLayoutPhases
import Elk.Alg.RectPacking.Options
import Elk.Alg.RectPacking.Intermediate
import Elk.Alg.RectPacking.P1WidthApproximation
import Elk.Alg.RectPacking.P2Packing
import Elk.Alg.RectPacking.P3WhitespaceElimination
/-!
# `org.eclipse.elk.alg.rectpacking.RectPackingLayoutProvider`

Port of `rect_packing_layout_provider.rs` (elk-rs): lays out the children of a node as packed
rectangles. Sets the algorithm defaults (padding 15, node spacing 15, aspect ratio 1.3) on the
graph if absent, runs the node micro layout, falls back to the box layout if `TRYBOX` is set and
no three consecutive rectangles are "stackable", and otherwise runs the three phases and the
intermediate processors assembled by an `AlgorithmAssembler` (before phase 1:
`NodeSizeReorderer` if `ORDER_BY_SIZE`, `InteractiveNodeReorderer` if `INTERACTIVE`,
`MinSizePreProcessor`; before phase 2: `MinSizePostProcessor`). Finally the content is aligned
in the drawing (`ElkUtil.translate`), padding is applied, the graph is resized (unless
`NODE_SIZE_FIXED_GRAPH_SIZE`) and the node micro layout runs again.

The whole layout runs in `RectPackingM` with a fresh arena; `RowsStorage.withRowsGuard` is the
Rust `RowsGuard`. Hierarchy is handled by `RecursiveGraphLayoutEngine` (the provider is not
hierarchy aware).

Strategy options are read with `get_property(..).unwrap_or_default()`; like elk-rs, the enum
options cannot be parsed from JSON (no parser registered), so only typed values take effect.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl15p0 : Float := 15.0
private def fl1p3 : Float := 1.3

namespace Elk.Alg.RectPacking

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Util Elk.Core.Options
open Elk.Alg.Common.NodeSpacing
open Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options Elk.Alg.RectPacking.Intermediate
open Elk.Alg.RectPacking.P1WidthApproximation Elk.Alg.RectPacking.P2Packing
open Elk.Alg.RectPacking.P3WhitespaceElimination

namespace RectPackingLayoutProvider

/-- `get_phase_independent_layout_processor_configuration(layout_graph)`. -/
def phaseIndependentLayoutProcessorConfiguration (layoutGraph : NodeId) :
    RectPackingM RectPackingProcessorConfiguration := do
  let props := (← ElkM.getNode layoutGraph).props
  let mut configuration : RectPackingProcessorConfiguration := LayoutProcessorConfiguration.create
  configuration := configuration.addBefore .p1WidthApproximation .minSizePreProcessor
  configuration := configuration.addBefore .p2Packing .minSizePostProcessor
  if (props.get RectPackingOptions.ORDER_BY_SIZE).getD false then
    configuration := configuration.addBefore .p1WidthApproximation .nodeSizeReorderer
  if (props.get RectPackingOptions.INTERACTIVE).getD false then
    configuration := configuration.addBefore .p1WidthApproximation .interactiveNodeReorderer
  return configuration

/-- `assemble_algorithm(layout_graph)`: the processor list for the strategies set on the graph. -/
def assembleAlgorithm (layoutGraph : NodeId) : RectPackingM (Array RectPackingProcessor) := do
  let assembler : RectPackingAlgorithmAssembler ←
    AlgorithmAssembler.create IntermediateProcessorStrategy.factory
  let props := (← ElkM.getNode layoutGraph).props
  let widthStrategy := props.getD RectPackingOptions.WIDTH_APPROXIMATION_STRATEGY .greedy
  let packingStrategy := props.getD RectPackingOptions.PACKING_STRATEGY .compaction
  let whitespaceStrategy := props.getD RectPackingOptions.WHITE_SPACE_ELIMINATION_STRATEGY .none
  assembler.setPhase .p1WidthApproximation (WidthApproximationStrategy.phaseFactory widthStrategy)
  assembler.setPhase .p2Packing (PackingStrategy.phaseFactory packingStrategy)
  assembler.setPhase .p3WhitespaceElimination (WhiteSpaceEliminationStrategy.phaseFactory whitespaceStrategy)
  let config ← phaseIndependentLayoutProcessorConfiguration layoutGraph
  assembler.addProcessorConfiguration config
  assembler.build layoutGraph

/-- `apply_algorithm_defaults(graph)`: padding 15, node spacing 15 and aspect ratio 1.3 unless set
on the graph. -/
def applyAlgorithmDefaults (graph : NodeId) : ElkM Unit := do
  ElkM.modifyNode graph fun n => Id.run do
    let mut props := n.props
    if !props.has CoreOptions.PADDING then props := props.set CoreOptions.PADDING (ElkPadding.ofAny fl15p0)
    if !props.has CoreOptions.SPACING_NODE_NODE then props := props.set CoreOptions.SPACING_NODE_NODE fl15p0
    if !props.has CoreOptions.ASPECT_RATIO then props := props.set CoreOptions.ASPECT_RATIO fl1p3
    return { n with props }

/-- `apply_padding(rectangles, padding)`: moves every rectangle by the left/top padding. -/
def applyPadding (rectangles : Array NodeId) (padding : ElkPadding) : ElkM Unit := do
  for rect in rectangles do
    ElkM.modifyNode rect fun n => { n with x := n.x + padding.left, y := n.y + padding.top }

/-- `try_box` check of `layout`: some three consecutive rectangles where the first (or the third)
is at least as high as the other two plus spacing; trivially `true` with fewer than three
rectangles or without `TRYBOX`. -/
def isStackable (rectangles : Array NodeId) (tryBox : Bool) (nodeNodeSpacing : Float) : ElkM Bool := do
  if tryBox && rectangles.size >= 3 then
    let g ← get
    let mut region2 := rectangles[0]!
    let mut region3 := rectangles[1]!
    let mut counter := 0
    while counter + 2 < rectangles.size do
      let region1 := region2
      region2 := region3
      region3 := rectangles[counter + 2]!
      let region1Height := (g.node region1).height
      let region2Height := (g.node region2).height
      let region3Height := (g.node region3).height
      if region1Height >= region2Height + region3Height + nodeNodeSpacing ||
          region3Height >= region1Height + region2Height + nodeNodeSpacing then
        return true
      counter := counter + 1
    return false
  else
    return true

/-- The `TRYBOX` fallback: `BoxLayoutProvider::new().layout(layout_graph, &mut
BasicProgressMonitor::new())` as elk-rs runs it inside `RecursiveGraphLayoutEngine`. The Rust box
provider reads its five configuration options (`SPACING_NODE_NODE`, `PADDING`, `EXPAND_NODES`,
`INTERACTIVE`, `BOX_PACKING_MODE`) from the layout-scoped arena snapshot
(`layout_arena_context::with_layout_arena`), which the engine takes before any provider runs, so
the rectangle packing defaults (padding 15, spacing 15) set by `apply_algorithm_defaults` are not
seen there; everything else (aspect ratio, priorities, minimum size) is read from the live graph.
`snapshot` is the property map of the graph before `apply_algorithm_defaults`. (Java and a direct
provider call outside the engine read the live values.) Options missing from the snapshot take the
box layouter defaults (`BoxLayouterOptions`: padding 15, spacing 15), which is what ELK Java ends up
with as well (its rectangle packing reads padding 15 and box spacing defaults to 15; elk-rs falls
back to the core defaults 12 / 20). -/
def boxLayoutFallback (layoutGraph : NodeId) (snapshot : PropertyMap) : ElkM Unit := do
  let objSpacing := snapshot.getD BoxLayouterOptions.SPACING_NODE_NODE 0.0
  let padding := snapshot.getD BoxLayouterOptions.PADDING {}
  let expandNodes := snapshot.getD BoxLayouterOptions.EXPAND_NODES false
  let interactive := snapshot.getD BoxLayouterOptions.INTERACTIVE false
  let packingMode := snapshot.getD BoxLayouterOptions.BOX_PACKING_MODE .simple
  match packingMode with
  | .simple => BoxLayoutProvider.placeBoxes layoutGraph objSpacing padding expandNodes interactive
  | _ => BoxLayoutProvider.placeBoxesGrouping layoutGraph objSpacing padding expandNodes

/-- The layout in `RectPackingM` (inside the `RowsGuard`). -/
private def layoutM (layoutGraph : NodeId) (monitor : ProgressMonitor) : RectPackingM Unit := do
  let _ ← monitor.begin "Rectangle Packing" 1.0
  let snapshot := (← ElkM.getNode layoutGraph).props
  applyAlgorithmDefaults layoutGraph
  let props := (← ElkM.getNode layoutGraph).props
  let padding := props.getD RectPackingOptions.PADDING {}
  let fixedGraphSize := props.getD RectPackingOptions.NODE_SIZE_FIXED_GRAPH_SIZE false
  let nodeNodeSpacing := props.getD RectPackingOptions.SPACING_NODE_NODE 0.0
  let tryBox := props.getD RectPackingOptions.TRYBOX false
  let rectangles := (← ElkM.getNode layoutGraph).children
  if !((← ElkM.getNode layoutGraph).props.getD RectPackingOptions.OMIT_NODE_MICRO_LAYOUT false) then
    (← NodeMicroLayout.forGraph layoutGraph).execute
  let stackable ← isStackable rectangles tryBox nodeNodeSpacing
  if !stackable then
    let mut priority : Int := rectangles.size
    for rect in rectangles do
      ElkM.setNodeProp rect CoreOptions.PRIORITY priority
      priority := priority - 1
    boxLayoutFallback layoutGraph snapshot
    monitor.done
    return
  let algorithm ← assembleAlgorithm layoutGraph
  let monitorProgress : Float :=
    if algorithm.isEmpty then 1.0 else Float.toF32 (1.0 / algorithm.size.toFloat)
  for processor in algorithm do
    if ← monitor.isCanceled then return
    let sub ← monitor.subTask monitorProgress
    processor.process layoutGraph sub
  let mut realWidth : Float := 0.0
  let mut realHeight : Float := 0.0
  for rect in rectangles do
    let n ← ElkM.getNode rect
    realWidth := fmax realWidth (n.x + n.width)
    realHeight := fmax realHeight (n.y + n.height)
  let props := (← ElkM.getNode layoutGraph).props
  let drawingWidth := (props.get InternalProperties.DRAWING_WIDTH).getD realWidth
  let drawingHeight := (props.get InternalProperties.DRAWING_HEIGHT).getD realHeight
  ElkUtil.translateNodeWithSizes layoutGraph ⟨drawingWidth, drawingHeight⟩ ⟨realWidth, realHeight⟩
  applyPadding rectangles padding
  if !fixedGraphSize then
    let _ ← ElkUtil.resizeNodeWith layoutGraph (drawingWidth + padding.left + padding.right)
      (drawingHeight + padding.top + padding.bottom) false true
  if !((← ElkM.getNode layoutGraph).props.getD RectPackingOptions.OMIT_NODE_MICRO_LAYOUT false) then
    (← NodeMicroLayout.forGraph layoutGraph).execute
  monitor.done

/-- `layout(layout_graph, progress_monitor)`. -/
def layout (layoutGraph : NodeId) (monitor : ProgressMonitor) : ElkM Unit :=
  RectPackingM.run' (RowsStorage.withRowsGuard layoutGraph (layoutM layoutGraph monitor))

/-- The `org.eclipse.elk.rectpacking` layout provider. -/
def provider : LayoutProvider := { id := RectPackingOptions.ALGORITHM_ID, layout := layout }

end RectPackingLayoutProvider

end Elk.Alg.RectPacking
