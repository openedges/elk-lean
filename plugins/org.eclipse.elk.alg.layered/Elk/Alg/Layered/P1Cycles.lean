import Elk.Alg.Layered.P1Cycles.GroupModelOrderCalculator
import Elk.Alg.Layered.P1Cycles.GreedyCycleBreaker
import Elk.Alg.Layered.P1Cycles.DepthFirstCycleBreaker
import Elk.Alg.Layered.P1Cycles.InteractiveCycleBreaker
import Elk.Alg.Layered.P1Cycles.ModelOrderCycleBreaker
import Elk.Alg.Layered.P1Cycles.SCCModelOrderCycleBreaker
import Elk.Alg.Layered.P1Cycles.SCConnectivity
import Elk.Alg.Layered.P1Cycles.SCCNodeTypeCycleBreaker
import Elk.Alg.Layered.P1Cycles.DFSNodeOrderCycleBreaker
import Elk.Alg.Layered.P1Cycles.BFSNodeOrderCycleBreaker
/-!
# `org.eclipse.elk.alg.layered.p1cycles`

Aggregator of the cycle breaking phase implementations. Each module registers its phase with
`LayeredPhases.registerPhase .p1CycleBreaking`; `CycleBreakingStrategy.createPhase` is the direct
mapping (elk-rs `CycleBreakingStrategy::create_phase`).
-/
namespace Elk.Alg.Layered.Options.CycleBreakingStrategy

open Elk.Alg.Layered Elk.Alg.Layered.P1Cycles

/-- `CycleBreakingStrategy.create()` (Rust `create_phase`). -/
def createPhase : CycleBreakingStrategy → LayeredPhase
  | .greedy => GreedyCycleBreaker.phase
  | .depthFirst => DepthFirstCycleBreaker.phase
  | .modelOrder => ModelOrderCycleBreaker.phase
  | .greedyModelOrder => GreedyCycleBreaker.modelOrderPhase
  | .sccConnectivity => SCConnectivity.phase
  | .sccNodeType => SCCNodeTypeCycleBreaker.phase
  | .dfsNodeOrder => DFSNodeOrderCycleBreaker.phase
  | .bfsNodeOrder => BFSNodeOrderCycleBreaker.phase
  | .interactive => InteractiveCycleBreaker.phase

end Elk.Alg.Layered.Options.CycleBreakingStrategy
