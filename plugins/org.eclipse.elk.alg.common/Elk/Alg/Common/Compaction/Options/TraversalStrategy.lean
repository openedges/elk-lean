import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.common.compaction.options.TraversalStrategy`

Traversal strategies for trying candidate positions of polyominoes (elk-rs
`traversal_strategy.rs`). Declaration order = Java ordinal order; the Rust `#[default]` is
`QUADRANTS_LINE_BY_LINE` (`TraversalStrategy.rustDefault`), not the first constructor.
-/
namespace Elk.Alg.Common.Compaction.Options

/-- `org.eclipse.elk.alg.common.compaction.options.TraversalStrategy`. -/
elk_enum TraversalStrategy := spiral lineByLine manhattan jitter quadrantsLineByLine
  quadrantsManhattan quadrantsJitter combineLineByLineManhattan combineJitterManhattan

namespace TraversalStrategy

/-- Rust `TraversalStrategy::default()`. -/
def rustDefault : TraversalStrategy := .quadrantsLineByLine

end TraversalStrategy

end Elk.Alg.Common.Compaction.Options
