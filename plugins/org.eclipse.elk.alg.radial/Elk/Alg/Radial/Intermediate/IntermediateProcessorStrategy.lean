import Elk.Graph
import Elk.Core.Alg
import Elk.Alg.Radial.InternalProperties
import Elk.Alg.Radial.Intermediate.CalculateGraphSize
import Elk.Alg.Radial.Intermediate.EdgeAngleCalculator
import Elk.Alg.Radial.Intermediate.Compaction.GeneralCompactor
import Elk.Alg.Radial.Intermediate.Overlaps.RadiusExtensionOverlapRemoval
import Elk.Alg.Radial.Intermediate.Rotation.GeneralRotator
/-!
# `org.eclipse.elk.alg.radial.intermediate.IntermediateProcessorStrategy`

Port of `intermediate_processor_strategy.rs` (elk-rs): the intermediate processors of the radial
layout in their execution order (the enumeration order is the sort order of the
`AlgorithmAssembler`).
-/
namespace Elk.Alg.Radial.Intermediate

open Elk.Graph Elk.Core.Alg

/-- `IntermediateProcessorStrategy`: `OVERLAP_REMOVAL`, `COMPACTION`, `ROTATION`,
`GRAPH_SIZE_CALCULATION`, `OUTGOING_EDGE_ANGLES`. -/
elk_enum IntermediateProcessorStrategy :=
  overlapRemoval compaction rotation graphSizeCalculation outgoingEdgeAngles

namespace IntermediateProcessorStrategy

/-- `ILayoutProcessorFactory::create()`. -/
def create : IntermediateProcessorStrategy → IO (LayoutProcessor RadialM NodeId)
  | .overlapRemoval => pure Overlaps.RadiusExtensionOverlapRemoval.processor
  | .compaction => pure Compaction.GeneralCompactor.processor
  | .rotation => pure Rotation.GeneralRotator.processor
  | .graphSizeCalculation => pure CalculateGraphSize.processor
  | .outgoingEdgeAngles => pure EdgeAngleCalculator.processor

end IntermediateProcessorStrategy

end Elk.Alg.Radial.Intermediate
