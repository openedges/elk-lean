import Elk.Alg.Layered.P3Order.RandomTrace
import Elk.Alg.Layered.P3Order.BarycenterHeuristic
import Elk.Alg.Layered.P3Order.ModelOrderBarycenterHeuristic
import Elk.Alg.Layered.P3Order.MedianHeuristic
import Elk.Alg.Layered.P3Order.SweepCopy
/-!
Aggregator of the `org.eclipse.elk.alg.layered.p3order` crossing minimisation heuristics
(`BarycenterHeuristic`, `ModelOrderBarycenterHeuristic`, elk-rs `MedianHeuristic`), `SweepCopy`
and elk-rs `RandomTrace`. The `GreedySwitchHeuristic` lives in
`Elk.Alg.Layered.Intermediate.GreedySwitch` (Java package `intermediate.greedyswitch`).
-/
