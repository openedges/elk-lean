import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.spore.options.CompactionStrategy`

Port of `options/compaction_strategy.rs` (elk-rs) and `CompactionStrategy.java`.

The Java enum implements `ILayoutPhaseFactory` (`create()` builds the execution phase of the
compaction); that factory is not part of this module: see `Elk.Alg.Spore.PhaseFactories`.
-/
namespace Elk.Alg.Spore.Options

/-- `org.eclipse.elk.alg.spore.options.CompactionStrategy`: this option defines how the compaction
is applied. -/
elk_enum CompactionStrategy := depthFirst

end Elk.Alg.Spore.Options
