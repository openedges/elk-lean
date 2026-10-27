import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options
/-!
# `org.eclipse.elk.alg.layered.p3order.NoCrossingMinimizer` (elk-rs `no_crossing_minimizer.rs`)

Crossing minimization that does nothing: the node and port order and all ids are left as the
layerer produced them. Only the processor configuration matters (long edge splitting and joining,
the in-layer constraint processor, and always the port list sorter).
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open Elk.Alg.Layered.Intermediate

namespace NoCrossingMinimizer

/-- `INTERMEDIATE_PROCESSING_CONFIGURATION`: `LONG_EDGE_SPLITTER` before P3,
`IN_LAYER_CONSTRAINT_PROCESSOR` before P4, `LONG_EDGE_JOINER` after P5. -/
def intermediateProcessingConfiguration : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p3NodeOrdering .longEdgeSplitter
    |>.addBefore .p4NodePlacement .inLayerConstraintProcessor
    |>.addAfter .p5EdgeRouting .longEdgeJoiner

/-- `getLayoutProcessorConfiguration(graph)`: the intermediate configuration plus
`PORT_LIST_SORTER` before P3 (unconditionally). -/
def getLayoutProcessorConfiguration (_graph : LGraphId) : LayeredM (Option LayeredProcessorConfiguration) :=
  return some ((LayoutProcessorConfiguration.createFrom intermediateProcessingConfiguration).addBefore
    .p3NodeOrdering .portListSorter)

/-- `process(graph, monitor)`: only reports progress. -/
def process (_graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "No crossing minimization" 1.0
  monitor.done

/-- The `NoCrossingMinimizer` phase. -/
def phase : LayeredPhase :=
  { name := "NoCrossingMinimizer"
    process := process
    getLayoutProcessorConfiguration := getLayoutProcessorConfiguration }

end NoCrossingMinimizer

/-- Registers `CrossingMinimizationStrategy.NONE` → `NoCrossingMinimizer`. -/
builtin_initialize registerNoCrossingMinimizer : Unit ←
  LayeredPhases.registerPhase .p3NodeOrdering (ElkEnum.ordinal CrossingMinimizationStrategy.none)
    (pure NoCrossingMinimizer.phase)

end Elk.Alg.Layered.P3Order
