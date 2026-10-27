import Elk.Alg.RectPacking.Intermediate.NodeSizeReorderer
import Elk.Alg.RectPacking.Intermediate.InteractiveNodeReorderer
import Elk.Alg.RectPacking.Intermediate.MinSizePreProcessor
import Elk.Alg.RectPacking.Intermediate.MinSizePostProcessor
/-!
# `org.eclipse.elk.alg.rectpacking.intermediate.IntermediateProcessorStrategy`

Port of `intermediate/intermediate_processor_strategy.rs` (elk-rs): the intermediate processor
factory enumeration `F` of the rectangle packing `AlgorithmAssembler` (ordinal = processor order
within a slot).
-/
namespace Elk.Alg.RectPacking.Intermediate

open Elk.Graph Elk.Core.Alg Elk.Alg.RectPacking.Util

/-- `IntermediateProcessorStrategy`: `NODE_SIZE_REORDERER`, `INTERACTIVE_NODE_REORDERER`,
`MIN_SIZE_PRE_PROCESSOR`, `MIN_SIZE_POST_PROCESSOR`. -/
elk_enum IntermediateProcessorStrategy :=
  nodeSizeReorderer interactiveNodeReorderer minSizePreProcessor minSizePostProcessor

namespace IntermediateProcessorStrategy

/-- `ILayoutProcessorFactory::create()`. -/
def createProcessor : IntermediateProcessorStrategy → LayoutProcessor RectPackingM NodeId
  | .nodeSizeReorderer => NodeSizeReorderer.processor
  | .interactiveNodeReorderer => InteractiveNodeReorderer.processor
  | .minSizePreProcessor => MinSizePreProcessor.processor
  | .minSizePostProcessor => MinSizePostProcessor.processor

/-- The processor factory of the assembler (`LayoutProcessorFactory`). -/
def factory : LayoutProcessorFactory RectPackingM NodeId IntermediateProcessorStrategy :=
  fun s => pure (createProcessor s)

end IntermediateProcessorStrategy

end Elk.Alg.RectPacking.Intermediate
