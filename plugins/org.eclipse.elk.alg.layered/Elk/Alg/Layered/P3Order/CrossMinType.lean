import Elk.Graph
/-! # `LayerSweepCrossingMinimizer.CrossMinType` -/
namespace Elk.Alg.Layered.P3Order

/-- `CrossMinType`: `BARYCENTER`, `ONE_SIDED_GREEDY_SWITCH`, `TWO_SIDED_GREEDY_SWITCH`. -/
elk_enum CrossMinType := barycenter oneSidedGreedySwitch twoSidedGreedySwitch

end Elk.Alg.Layered.P3Order
