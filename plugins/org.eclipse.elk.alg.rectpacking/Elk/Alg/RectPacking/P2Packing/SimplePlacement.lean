import Elk.Alg.RectPacking.RectPackingLayoutPhases
import Elk.Alg.RectPacking.Options.InternalProperties
import Elk.Alg.RectPacking.P2Packing.InitialPlacement
/-!
# `org.eclipse.elk.alg.rectpacking.p2packing.SimplePlacement`

Port of `p2packing/simple_placement.rs` (elk-rs): the `SIMPLE` packing phase. Only the initial
placement (rows of blocks) is done; every block becomes its own stack. Like Rust and Java the
drawing height stored is `height + additional_height` (the additional height counted twice), and
the progress task is called "No Compaction".
-/
namespace Elk.Alg.RectPacking.P2Packing

open Elk.Graph Elk.Core.Util Elk.Core.Math Elk.Core.Alg
open Elk.Alg.RectPacking Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options
open RectPackingM

namespace SimplePlacement

/-- `process(graph, progress_monitor)`. -/
def run (graph : NodeId) (monitor : ProgressMonitor) : RectPackingM Unit := do
  let _ ← monitor.begin "No Compaction" 1.0
  let props := (← ElkM.getNode graph).props
  let targetWidth := props.getD InternalProperties.TARGET_WIDTH 0.0
  let nodeNodeSpacing := props.getD RectPackingOptions.SPACING_NODE_NODE 0.0
  let padding := props.getD RectPackingOptions.PADDING {}
  let rectangles := (← ElkM.getNode graph).children
  DrawingUtil.resetCoordinates rectangles
  let rows ← InitialPlacement.place rectangles targetWidth nodeNodeSpacing
  let size ← if rows.isEmpty then
      DrawingUtil.calculateDimensionsFromNodes rectangles
    else do
      for row in rows do
        let blocks := (← getRow row).children
        for block in blocks do
          let blk ← getBlock block
          let stack ← BlockStack.create blk.x blk.y nodeNodeSpacing
          BlockStack.addBlock stack block
          RectRow.addStack row stack
      DrawingUtil.calculateDimensions rows nodeNodeSpacing
  let props := (← ElkM.getNode graph).props
  let minWidth := props.getD InternalProperties.MIN_WIDTH 0.0
  let minHeight := props.getD InternalProperties.MIN_HEIGHT 0.0
  let width := javaMax size.x (minWidth - (padding.left + padding.right))
  let height := javaMax size.y (minHeight - (padding.top + padding.bottom))
  let additionalHeight := height - size.y
  ElkM.setNodeProp graph InternalProperties.ADDITIONAL_HEIGHT additionalHeight
  ElkM.setNodeProp graph InternalProperties.DRAWING_WIDTH width
  ElkM.setNodeProp graph InternalProperties.DRAWING_HEIGHT (height + additionalHeight)
  let rowsKey ← RowsStorage.storeRows graph rows
  ElkM.setNodeProp graph InternalProperties.ROWS rowsKey
  monitor.done

/-- `SimplePlacement` as an `ILayoutPhase` (no processor configuration). -/
def phase : RectPackingPhase :=
  { name := "SimplePlacement"
    process := fun graph monitor => run graph monitor
    getLayoutProcessorConfiguration := fun _ => pure none }

end SimplePlacement

end Elk.Alg.RectPacking.P2Packing
