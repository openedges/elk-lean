import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.SelfLoopOrderingStrategy`

Port of `options/self_loop_ordering_strategy.rs` (elk-rs) and `SelfLoopOrderingStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.SelfLoopOrderingStrategy`: Determines how self loops will
be placed in certain `SelfLoopDistributionStrategy distribution strategies`. -/
elk_enum SelfLoopOrderingStrategy := stacked reverseStacked sequenced

end Elk.Alg.Layered.Options
