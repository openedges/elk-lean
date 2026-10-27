import Elk.Core.Alg
import Elk.Core.Util.ElkUtil
import Elk.Alg.RectPacking.Util.RectPackingArena
import Elk.Alg.RectPacking.Options.InternalProperties
/-!
# `org.eclipse.elk.alg.rectpacking.intermediate.MinSizePreProcessor`

Port of `intermediate/min_size_pre_processor.rs` (elk-rs): stores the effective minimum size of
the graph (`ElkUtil.effectiveMinSizeConstraintFor`) as `MIN_WIDTH` / `MIN_HEIGHT`.
-/
namespace Elk.Alg.RectPacking.Intermediate

open Elk.Graph Elk.Core.Util Elk.Core.Alg Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options

namespace MinSizePreProcessor

/-- `process(graph, progress_monitor)` on the `ElkGraph`. -/
def run (graph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "Min Size Preprocessing" 1.0
  let minSize := ElkUtil.effectiveMinSizeConstraintFor (← get) graph
  ElkM.setNodeProp graph InternalProperties.MIN_WIDTH minSize.x
  ElkM.setNodeProp graph InternalProperties.MIN_HEIGHT minSize.y
  monitor.done

/-- `MinSizePreProcessor` as an `ILayoutProcessor<ElkNode>`. -/
def processor : LayoutProcessor RectPackingM NodeId :=
  { name := "MinSizePreProcessor", process := fun graph monitor => run graph monitor }

end MinSizePreProcessor

end Elk.Alg.RectPacking.Intermediate
