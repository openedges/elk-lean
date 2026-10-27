import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.SelfLoopDistributionStrategy`

Port of `options/self_loop_distribution_strategy.rs` (elk-rs) and `SelfLoopDistributionStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.SelfLoopDistributionStrategy`: The possible ways to
distribute self loops around a node. -/
elk_enum SelfLoopDistributionStrategy := equally north northSouth

end Elk.Alg.Layered.Options
