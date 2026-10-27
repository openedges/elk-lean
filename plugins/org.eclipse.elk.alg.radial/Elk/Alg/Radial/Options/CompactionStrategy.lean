import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.radial.options.CompactionStrategy`

Port of `compaction_strategy.rs` (elk-rs). The factory half of the Rust enum (`create`, which
builds the `IRadialCompactor`) lives in `Elk.Alg.Radial.Intermediate.Compaction.GeneralCompactor`,
the only user, because the compactors depend on the options.
-/
namespace Elk.Alg.Radial.Options

/-- `CompactionStrategy`: the compaction applied after the radial positioning. -/
elk_enum CompactionStrategy := none radialCompaction wedgeCompaction

end Elk.Alg.Radial.Options
