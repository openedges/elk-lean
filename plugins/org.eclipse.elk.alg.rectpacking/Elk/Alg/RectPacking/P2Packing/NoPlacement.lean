import Elk.Alg.RectPacking.RectPackingLayoutPhases
import Elk.Alg.RectPacking.Options.InternalProperties
import Elk.Alg.RectPacking.Options.RectPackingOptions
import Elk.Alg.RectPacking.Util
/-!
# `org.eclipse.elk.alg.rectpacking.p2packing.NoPlacement`

Port of `p2packing/no_placement.rs` (elk-rs): the `NONE` packing phase. The rectangles keep the
positions of the width approximation; only the drawing size is computed (stored drawing height
`height + additional_height`, as in Rust and Java). No rows are stored.
-/
namespace Elk.Alg.RectPacking.P2Packing

open Elk.Graph Elk.Core.Util Elk.Core.Math Elk.Core.Alg
open Elk.Alg.RectPacking Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options

namespace NoPlacement

/-- `process(graph, progress_monitor)`. -/
def run (graph : NodeId) (monitor : ProgressMonitor) : RectPackingM Unit := do
  let _ ← monitor.begin "No Compaction" 1.0
  let props := (← ElkM.getNode graph).props
  let padding := props.getD RectPackingOptions.PADDING {}
  let rectangles := (← ElkM.getNode graph).children
  let size ← DrawingUtil.calculateDimensionsFromNodes rectangles
  let minWidth := props.getD InternalProperties.MIN_WIDTH 0.0
  let minHeight := props.getD InternalProperties.MIN_HEIGHT 0.0
  let width := javaMax size.x (minWidth - (padding.left + padding.right))
  let height := javaMax size.y (minHeight - (padding.top + padding.bottom))
  let additionalHeight := height - size.y
  ElkM.setNodeProp graph InternalProperties.ADDITIONAL_HEIGHT additionalHeight
  ElkM.setNodeProp graph InternalProperties.DRAWING_WIDTH width
  ElkM.setNodeProp graph InternalProperties.DRAWING_HEIGHT (height + additionalHeight)
  monitor.done

/-- `NoPlacement` as an `ILayoutPhase` (no processor configuration). -/
def phase : RectPackingPhase :=
  { name := "NoPlacement"
    process := fun graph monitor => run graph monitor
    getLayoutProcessorConfiguration := fun _ => pure none }

end NoPlacement

end Elk.Alg.RectPacking.P2Packing
