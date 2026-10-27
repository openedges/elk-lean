import Elk.Alg.Common.Compaction.OneD.ICompactionAlgorithm
/-!
# `org.eclipse.elk.alg.common.compaction.oned.IConstraintCalculationAlgorithm`

A constraint calculation strategy (elk-rs `i_constraint_calculation_algorithm.rs`), run in
`CompactM` (see `ICompactionAlgorithm` for the split of the compactor state).
-/
namespace Elk.Alg.Common.Compaction.OneD

/-- `IConstraintCalculationAlgorithm.calculateConstraints(compactor)`. -/
structure ConstraintCalculationAlgorithm where
  /-- Fills `CNode.constraints` of all nodes of `cGraph` for the current `direction`. -/
  calculateConstraints : CompactM Unit

end Elk.Alg.Common.Compaction.OneD
