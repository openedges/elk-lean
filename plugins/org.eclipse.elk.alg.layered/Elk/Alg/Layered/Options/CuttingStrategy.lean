import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.CuttingStrategy`

Port of `options/cutting_strategy.rs` (elk-rs) and `CuttingStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.CuttingStrategy`: Specifies the strategy employed to
calculate cut indexes during graph wrapping. -/
elk_enum CuttingStrategy := ard msd manual

end Elk.Alg.Layered.Options
