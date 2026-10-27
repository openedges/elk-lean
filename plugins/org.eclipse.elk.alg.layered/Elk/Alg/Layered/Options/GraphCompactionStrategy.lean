import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.GraphCompactionStrategy`

Port of `options/graph_compaction_strategy.rs` (elk-rs) and `GraphCompactionStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.GraphCompactionStrategy`: Definition of strategies for
horizontal compaction. -/
elk_enum GraphCompactionStrategy := none left right leftRightConstraintLocking leftRightConnectionLocking edgeLength

end Elk.Alg.Layered.Options
