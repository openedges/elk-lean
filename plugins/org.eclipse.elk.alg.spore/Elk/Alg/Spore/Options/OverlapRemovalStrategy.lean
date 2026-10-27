import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.spore.options.OverlapRemovalStrategy`

Port of `options/overlap_removal_strategy.rs` (elk-rs) and `OverlapRemovalStrategy.java`.

The Java enum implements `ILayoutPhaseFactory` (`create()` builds the execution phase of the
overlap removal); that factory is not part of this module: see `Elk.Alg.Spore.PhaseFactories`.
-/
namespace Elk.Alg.Spore.Options

/-- `org.eclipse.elk.alg.spore.options.OverlapRemovalStrategy`: strategy of the execution phase of
the overlap removal (growing a tree, Nachmanson et al.). -/
elk_enum OverlapRemovalStrategy := growTree

end Elk.Alg.Spore.Options
