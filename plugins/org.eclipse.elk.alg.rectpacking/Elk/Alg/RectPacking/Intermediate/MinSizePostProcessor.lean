import Elk.Core.Alg
import Elk.Alg.RectPacking.Util.RectPackingArena
import Elk.Alg.RectPacking.Options.InternalProperties
/-!
# `org.eclipse.elk.alg.rectpacking.intermediate.MinSizePostProcessor`

Port of `intermediate/min_size_post_processor.rs` (elk-rs): raises `TARGET_WIDTH` to at least
`MIN_WIDTH` (both default to `0` when unset, Rust `unwrap_or(0.0)`; `f64::max`).
-/
namespace Elk.Alg.RectPacking.Intermediate

open Elk.Graph Elk.Core.Util Elk.Core.Alg Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options

namespace MinSizePostProcessor

/-- `process(graph, progress_monitor)` on the `ElkGraph`. -/
def run (graph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "Min Size Postprocessing" 1.0
  let minWidth ← ElkM.getNodePropD graph InternalProperties.MIN_WIDTH 0.0
  let targetWidth ← ElkM.getNodePropD graph InternalProperties.TARGET_WIDTH 0.0
  ElkM.setNodeProp graph InternalProperties.TARGET_WIDTH (fmax targetWidth minWidth)
  monitor.done

/-- `MinSizePostProcessor` as an `ILayoutProcessor<ElkNode>`. -/
def processor : LayoutProcessor RectPackingM NodeId :=
  { name := "MinSizePostProcessor", process := fun graph monitor => run graph monitor }

end MinSizePostProcessor

end Elk.Alg.RectPacking.Intermediate
