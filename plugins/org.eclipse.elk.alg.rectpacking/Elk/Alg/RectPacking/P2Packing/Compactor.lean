import Elk.Alg.RectPacking.RectPackingLayoutPhases
import Elk.Alg.RectPacking.P2Packing.RowFillingAndCompaction
/-!
# `org.eclipse.elk.alg.rectpacking.p2packing.Compactor`

Port of `p2packing/compactor.rs` (elk-rs): the `COMPACTION` packing phase. Runs
`RowFillingAndCompaction` on the graph and, for `PACKING_COMPACTION_ITERATIONS > 1`, repeats it
on shallow clones of the graph with a changed target width, keeping a clone's packing if its
scale measure is not worse.

The clones are new nodes of the `ElkGraph` arena without a parent (Rust
`ElkGraphFactory::create_elk_node()`; they are not reachable from the laid-out graph and not
exported). Their rows are stored in `RowsStorage` under the clone's key and stay there (Rust only
removes the rows of the laid-out graph, `RowsGuard`).
-/
namespace Elk.Alg.RectPacking.P2Packing

open Elk.Graph Elk.Core.Util Elk.Core.Math Elk.Core.Alg
open Elk.Alg.RectPacking Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options
open RectPackingM

namespace Compactor

/-- `copy_row_width_change_values(graph, compaction)`: stores the potential row width changes as
`MIN_ROW_INCREASE`, `MAX_ROW_INCREASE`, `MIN_ROW_DECREASE`, `MAX_ROW_DECREASE`. -/
def copyRowWidthChangeValues (graph : NodeId) (compaction : RowFillingAndCompaction) : RectPackingM Unit := do
  ElkM.setNodeProp graph InternalProperties.MIN_ROW_INCREASE compaction.potentialRowWidthIncreaseMin
  ElkM.setNodeProp graph InternalProperties.MAX_ROW_INCREASE compaction.potentialRowWidthIncreaseMax
  ElkM.setNodeProp graph InternalProperties.MIN_ROW_DECREASE compaction.potentialRowWidthDecreaseMin
  ElkM.setNodeProp graph InternalProperties.MAX_ROW_DECREASE compaction.potentialRowWidthDecreaseMax

/-- `configure_second_iteration(layout_graph, clone, drawing)`: widens the clone's target width
by the minimal row increase if the padded drawing is narrower than the aspect ratio, or narrows
it by the minimal row decrease (at least the minimum width) if it is wider (only for more than
one child and finite values). -/
def configureSecondIteration (layoutGraph clone : NodeId) (drawing : DrawingData) : RectPackingM Unit := do
  let n ← ElkM.getNode layoutGraph
  let props := n.props
  let padding := props.getD RectPackingOptions.PADDING {}
  let aspectRatio := props.getD RectPackingOptions.ASPECT_RATIO 1.0
  let minRowIncrease := props.getD InternalProperties.MIN_ROW_INCREASE Float.posInf
  let minRowDecrease := props.getD InternalProperties.MIN_ROW_DECREASE Float.posInf
  let targetWidth := props.getD InternalProperties.TARGET_WIDTH 0.0
  let minWidth := props.getD InternalProperties.MIN_WIDTH 0.0
  let drawingRatio := (drawing.drawingWidth + padding.left + padding.right) /
    (drawing.drawingHeight + padding.top + padding.bottom)
  let childrenLen := n.children.size
  if childrenLen > 1 && minRowIncrease != Float.posInf && drawingRatio < aspectRatio then
    ElkM.setNodeProp clone InternalProperties.TARGET_WIDTH (targetWidth + minRowIncrease)
  else if childrenLen > 1 && minRowDecrease != Float.posInf && drawingRatio > aspectRatio then
    let newWidth := fmax (targetWidth - minRowDecrease) minWidth
    ElkM.setNodeProp clone InternalProperties.TARGET_WIDTH newWidth

/-- Copies shape (size, location), properties and identifier of `source` onto the new node
`target`. -/
private def copyShape (source target : NodeId) : RectPackingM Unit := do
  let s ← ElkM.getNode source
  ElkM.modifyNode target fun t =>
    { t with width := s.width, height := s.height, x := s.x, y := s.y,
             props := t.props.copyFrom s.props, identifier := s.identifier }

/-- `clone_graph(node)`: a parentless copy of the node and of its children (size, location,
properties, identifier; no grandchildren, ports, labels or edges). -/
def cloneGraph (node : NodeId) : RectPackingM NodeId := do
  let clone ← ElkM.createNode none
  copyShape node clone
  for child in (← ElkM.getNode node).children do
    let newChild ← ElkM.createNode (some clone)
    copyShape child newChild
  return clone

/-- `copy_position(source, target)`: copies size and location. The Rust recursion into the
children pairs (`zip`) never reaches a pair, because the source is a child of a clone, which has
no children. -/
def copyPosition (source target : NodeId) : RectPackingM Unit := do
  let s ← ElkM.getNode source
  ElkM.modifyNode target fun t => { t with width := s.width, height := s.height, x := s.x, y := s.y }

/-- `process(graph, progress_monitor)`. -/
def run (graph : NodeId) (monitor : ProgressMonitor) : RectPackingM Unit := do
  let _ ← monitor.begin "Compaction" 1.0
  let props := (← ElkM.getNode graph).props
  let aspectRatio := props.getD RectPackingOptions.ASPECT_RATIO 1.0
  let nodeNodeSpacing := props.getD RectPackingOptions.SPACING_NODE_NODE 0.0
  let padding := props.getD RectPackingOptions.PADDING {}
  let rectangles := (← ElkM.getNode graph).children
  let secondIt := RowFillingAndCompaction.new aspectRatio nodeNodeSpacing
  let (d, secondIt) ← secondIt.start rectangles monitor graph padding
  let mut drawing := d
  copyRowWidthChangeValues graph secondIt
  let mut iterations : Int :=
    ((← ElkM.getNode graph).props.get RectPackingOptions.PACKING_COMPACTION_ITERATIONS).getD 1
  while iterations > 1 do
    let clone ← cloneGraph graph
    let oldSm := drawing.scaleMeasure
    configureSecondIteration graph clone drawing
    let secondIt := RowFillingAndCompaction.new aspectRatio nodeNodeSpacing
    let (newDrawing, secondIt) ← secondIt.start rectangles monitor clone padding
    let newSm := newDrawing.scaleMeasure
    if newSm >= oldSm && !newSm.isNaN then
      let cloneChildren := (← ElkM.getNode clone).children
      let graphChildren := (← ElkM.getNode graph).children
      for (cloneChild, graphChild) in cloneChildren.zip graphChildren do
        copyPosition cloneChild graphChild
      copyRowWidthChangeValues graph secondIt
      drawing := drawing.setDrawingWidth newDrawing.drawingWidth
      drawing := drawing.setDrawingHeight newDrawing.drawingHeight
    iterations := iterations - 1
  ElkM.setNodeProp graph InternalProperties.DRAWING_HEIGHT drawing.drawingHeight
  ElkM.setNodeProp graph InternalProperties.DRAWING_WIDTH drawing.drawingWidth
  monitor.done

/-- `Compactor` as an `ILayoutPhase` (no processor configuration). -/
def phase : RectPackingPhase :=
  { name := "Compactor"
    process := fun graph monitor => run graph monitor
    getLayoutProcessorConfiguration := fun _ => pure none }

end Compactor

end Elk.Alg.RectPacking.P2Packing
