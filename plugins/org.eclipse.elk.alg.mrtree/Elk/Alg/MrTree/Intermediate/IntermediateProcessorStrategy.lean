import Elk.Core.Alg.LayoutProcessor
import Elk.Alg.MrTree.Intermediate.RootProcessor
import Elk.Alg.MrTree.Intermediate.FanProcessor
import Elk.Alg.MrTree.Intermediate.LevelProcessor
import Elk.Alg.MrTree.Intermediate.NeighborsProcessor
import Elk.Alg.MrTree.Intermediate.LevelHeightProcessor
import Elk.Alg.MrTree.Intermediate.DirectionProcessor
import Elk.Alg.MrTree.Intermediate.NodePositionProcessor
import Elk.Alg.MrTree.Intermediate.CompactionProcessor
import Elk.Alg.MrTree.Intermediate.LevelCoordinatesProcessor
import Elk.Alg.MrTree.Intermediate.GraphBoundsProcessor
import Elk.Alg.MrTree.Intermediate.Untreeifyer
/-!
# `org.eclipse.elk.alg.mrtree.intermediate.IntermediateProcessorStrategy`

Port of `intermediate/intermediate_processor_strategy.rs` (elk-rs): the intermediate processors of
the tree layout in Java ordinal order (also the order processors are sorted in within one slot of a
processor configuration) and the factory creating them. The processors are stateless records, so
`create` returns the same record for every call (Rust creates fresh instances; their only state is
cleared at the start of every `process`).
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Alg Elk.Alg.MrTree.Graph

/-- `org.eclipse.elk.alg.mrtree.intermediate.IntermediateProcessorStrategy`. -/
elk_enum IntermediateProcessorStrategy :=
  rootProc fanProc levelProc neighborsProc levelHeight directionProc nodePositionProc compactionProc
  levelCoords graphBoundsProc detreeifyingProc

namespace IntermediateProcessorStrategy

/-- `ILayoutProcessorFactory::create`. -/
def create : IntermediateProcessorStrategy → TreeProcessor
  | .rootProc => RootProcessor.processor
  | .fanProc => FanProcessor.processor
  | .levelProc => LevelProcessor.processor
  | .neighborsProc => NeighborsProcessor.processor
  | .levelHeight => LevelHeightProcessor.processor
  | .directionProc => DirectionProcessor.processor
  | .nodePositionProc => NodePositionProcessor.processor
  | .compactionProc => CompactionProcessor.processor
  | .levelCoords => LevelCoordinatesProcessor.processor
  | .graphBoundsProc => GraphBoundsProcessor.processor
  | .detreeifyingProc => Untreeifyer.processor

/-- The processor factory of the `AlgorithmAssembler`. -/
def factory : LayoutProcessorFactory MrTreeM TGraphId IntermediateProcessorStrategy :=
  fun s => pure (create s)

end IntermediateProcessorStrategy

end Elk.Alg.MrTree.Intermediate
