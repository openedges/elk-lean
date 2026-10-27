import Elk.Alg.Layered.P3Order.CrossMinType
import Elk.Alg.Layered.P3Order.AbstractBarycenterPortDistributor
import Elk.Alg.Layered.P3Order.NodeRelativePortDistributor
import Elk.Alg.Layered.P3Order.LayerTotalPortDistributor
import Elk.Alg.Layered.P3Order.BarycenterPortDistributor
import Elk.Alg.Layered.P3Order.GreedyPortDistributor
import Elk.Alg.Layered.P3Order.ForsterConstraintResolver
import Elk.Core.Util.Random
/-!
Aggregator of the `org.eclipse.elk.alg.layered.p3order` port distributors and the
`ForsterConstraintResolver`, plus the `ISweepPortDistributor.create` factory (which needs all
three distributors, so it cannot live in `ISweepPortDistributor.lean`).

Random numbers: Rust's `create(cross_min_type, random: &mut Random, num_layers)` draws from a
`Random` owned by its caller (the `LayerSweepCrossingMinimizer`'s shared generator for the root
graph, a copy of the graph's `RANDOM` for nested graphs). The caller passes that generator as an
`IO.Ref Random`; the factory advances it in place.
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Util

namespace SweepPortDistributor

/-- `ISweepPortDistributor::create(cross_min_type, random, num_layers)`: the greedy distributor
for `TWO_SIDED_GREEDY_SWITCH`, otherwise `random.nextBoolean()` picks the node-relative (`true`)
or the layer-total (`false`) barycenter distributor. -/
def create (crossMinType : CrossMinType) (random : IO.Ref Random) (numLayers : Nat) : BaseIO SweepPortDistributor := do
  if crossMinType == .twoSidedGreedySwitch then
    return (← GreedyPortDistributor.new).toSweepPortDistributor
  else if ← random.modifyGet (·.nextBoolean) then
    return (← NodeRelativePortDistributor.new numLayers).toSweepPortDistributor
  else
    return (← LayerTotalPortDistributor.new numLayers).toSweepPortDistributor

end SweepPortDistributor

end Elk.Alg.Layered.P3Order
