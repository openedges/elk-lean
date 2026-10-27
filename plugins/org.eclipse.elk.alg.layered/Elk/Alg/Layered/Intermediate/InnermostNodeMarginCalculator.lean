import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.Transform.LGraphAdapters
import Elk.Alg.Common.NodeSpacing.NodeDimensionCalculation
/-!
# `org.eclipse.elk.alg.layered.intermediate.InnermostNodeMarginCalculator`

Port of elk-rs `intermediate/innermost_node_margin_calculator.rs` (Java
`InnermostNodeMarginCalculator`): "Sets the node margins. Node margins are influenced by both port
positions and sizes and label positions and sizes. Furthermore, comment boxes that are put next to
regular nodes also contribute to the margins."

Slot: before phase 4. Precondition: the port positions and label positions are fixed
(`LabelAndNodeSizeProcessor`). The margins of all layer nodes are computed by the node spacing
`NodeMarginCalculator` on `LGraphAdapters.adapt(graph, false, false, |_| true)` (no transparent
north/south edges, no comment nodes, every layer node) with the edge head/tail labels excluded
(they are placed by `EndLabelPreprocessor`); self loops and comment boxes are handled later.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph LayeredM
open Elk.Alg.Layered.Graph.Transform Elk.Alg.Common.NodeSpacing

namespace InnermostNodeMarginCalculator

/-- `process(layeredGraph, monitor)` (Rust `process`): `NodeDimensionCalculation
.getNodeMarginCalculator(adapter).excludeEdgeHeadTailLabels().process()`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Node margin calculation" 1.0
  let adapter ← LGraphAdapters.adapt graph false false fun _ => true
  (NodeDimensionCalculation.getNodeMarginCalculator adapter).excludeEdgeHeadTailLabels.process adapter graph
  monitor.done

/-- The `InnermostNodeMarginCalculator` processor. -/
def processor : LayeredProcessor := { name := "InnermostNodeMarginCalculator", process := process }

end InnermostNodeMarginCalculator

builtin_initialize registerInnermostNodeMarginCalculator : Unit ←
  IntermediateProcessorStrategy.register .innermostNodeMarginCalculator InnermostNodeMarginCalculator.processor

end Elk.Alg.Layered.Intermediate
