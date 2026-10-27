import Elk.Alg.Layered.Intermediate.Wrapping.BreakingPointInfo
import Elk.Alg.Layered.Intermediate.Wrapping.GraphStats
import Elk.Alg.Layered.Intermediate.Wrapping.ICutIndexCalculator
import Elk.Alg.Layered.Intermediate.Wrapping.ARDCutIndexHeuristic
import Elk.Alg.Layered.Intermediate.Wrapping.MSDCutIndexHeuristic
import Elk.Alg.Layered.Intermediate.Wrapping.CuttingUtils
import Elk.Alg.Layered.Intermediate.Wrapping.SingleEdgeGraphWrapper
import Elk.Alg.Layered.Intermediate.Wrapping.BreakingPointInserter
import Elk.Alg.Layered.Intermediate.Wrapping.BreakingPointProcessor
import Elk.Alg.Layered.Intermediate.Wrapping.BreakingPointRemover
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping`

Graph wrapping (`WRAPPING_STRATEGY`): the `SingleEdgeGraphWrapper` (`SINGLE_EDGE`) and the three
breaking point processors (`MULTI_EDGE`: `BreakingPointInserter` after P2,
`BreakingPointProcessor` after P3, `BreakingPointRemover` after P5) with their cut index
calculators (`ManualCutIndexCalculator`, `ARDCutIndexHeuristic`, `MSDCutIndexHeuristic`),
`GraphStats` and `CuttingUtils`. Ported from the elk-rs files
`intermediate/{breaking_point_info,breaking_point_inserter,breaking_point_processor,breaking_point_remover,single_edge_graph_wrapper}.rs`.
-/
