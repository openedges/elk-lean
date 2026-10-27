import Elk.Graph
/-! # `LayerSweepCrossingMinimizer.CrossMinType` -/
namespace Elk.Alg.Layered.P3Order

/-- `CrossMinType` (elk-rs `layer_sweep_crossing_minimizer.rs`): `BARYCENTER`,
`ONE_SIDED_GREEDY_SWITCH`, `TWO_SIDED_GREEDY_SWITCH`, `MEDIAN` (elk-rs adds `MEDIAN` for
`CrossingMinimizationStrategy.MEDIAN_LAYER_SWEEP`; Java has the first three). -/
elk_enum CrossMinType := barycenter oneSidedGreedySwitch twoSidedGreedySwitch median

end Elk.Alg.Layered.P3Order
