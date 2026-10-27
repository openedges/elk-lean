import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.GroupOrderStrategy`

Port of `options/group_order_strategy.rs` (elk-rs) and `GroupOrderStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.GroupOrderStrategy`: Determines how to count ordering
violations during layered phases. Hence, this must be implemented by the several model order
strategies to work correctly. -/
elk_enum GroupOrderStrategy := onlyWithinGroup modelOrder enforced

end Elk.Alg.Layered.Options
