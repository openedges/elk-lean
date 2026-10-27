import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.ConstraintCalculationStrategy`

Port of `options/constraint_calculation_strategy.rs` (elk-rs) and `ConstraintCalculationStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.ConstraintCalculationStrategy`: Which strategy should be
used by the `org.eclipse.elk.alg.layered.compaction.oned.OneDimensionalCompactor
OneDimensionalCompactor` to calculate the constraint graph. -/
elk_enum ConstraintCalculationStrategy := quadratic scanline

end Elk.Alg.Layered.Options
