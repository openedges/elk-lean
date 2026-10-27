import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.GreedySwitchType`

Port of `options/greedy_switch_type.rs` (elk-rs) and `GreedySwitchType.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.GreedySwitchType`: Sets the variant of the greedy switch
heuristic. -/
elk_enum GreedySwitchType := oneSided twoSided off

end Elk.Alg.Layered.Options
