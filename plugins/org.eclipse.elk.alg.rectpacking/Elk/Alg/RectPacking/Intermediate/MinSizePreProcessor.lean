import Elk.Core.Alg
import Elk.Core.Util.ElkUtil
import Elk.Core.Util.Java
import Elk.Core.Util.Adapters.ElkGraphAdapters
import Elk.Alg.Common.NodeSpacing.Calculators.NodeLabelAndSizeCalculator
import Elk.Alg.RectPacking.Util.RectPackingArena
import Elk.Alg.RectPacking.Options.InternalProperties
/-!
# `org.eclipse.elk.alg.rectpacking.intermediate.MinSizePreProcessor`

Stores the minimum size of the graph as `MIN_WIDTH` / `MIN_HEIGHT`: the effective minimum size
constraint (`ElkUtil.effectiveMinSizeConstraintFor`) and, for a graph with a parent, the size that
`NodeLabelAndSizeCalculator.process(parentAdapter, nodeAdapter, false, true)` computes for the graph
node (node labels, ports, port labels), whichever is larger per dimension (Java `Math.max`).

Deviation from elk-rs (`intermediate/min_size_pre_processor.rs`): elk-rs only uses the minimum size
constraint; the label-based size and the node size validation that comes with it (Java's
`NodeContext` / `PortContextCreator` exceptions, e.g. `Label and node size calculator can only be
used with ports that have port sides assigned.`) are Java's.
-/
namespace Elk.Alg.RectPacking.Intermediate

open Elk.Graph Elk.Core.Util Elk.Core.Alg Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options Elk.Alg.Common.NodeSpacing

namespace MinSizePreProcessor

/-- `process(graph, progress_monitor)` on the `ElkGraph`. -/
def run (graph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "Min Size Preprocessing" 1.0
  -- Get minimum size based on children
  let mut minSize := ElkUtil.effectiveMinSizeConstraintFor (← get) graph
  -- Get minimum size based on labels (only possible if a parent exists)
  if let some parent := (← ElkM.getNode graph).parent then
    let adapters ← ElkGraphAdapters.adaptSingleNode graph
    let layoutDirection ← adapters.graph.getPropertyD parent CoreOptions.DIRECTION Direction.undefined
    let minSize2 ← NodeLabelAndSizeCalculator.processWithOptions adapters graph layoutDirection false true
    minSize := { x := javaMax minSize.x minSize2.x, y := javaMax minSize.y minSize2.y }
  ElkM.setNodeProp graph InternalProperties.MIN_WIDTH minSize.x
  ElkM.setNodeProp graph InternalProperties.MIN_HEIGHT minSize.y
  monitor.done

/-- `MinSizePreProcessor` as an `ILayoutProcessor<ElkNode>`. -/
def processor : LayoutProcessor RectPackingM NodeId :=
  { name := "MinSizePreProcessor", process := fun graph monitor => run graph monitor }

end MinSizePreProcessor

end Elk.Alg.RectPacking.Intermediate
