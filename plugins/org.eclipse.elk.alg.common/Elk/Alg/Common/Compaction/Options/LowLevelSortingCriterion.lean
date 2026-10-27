import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.common.compaction.options.LowLevelSortingCriterion`

Secondary sorting criteria for the processing order of polyominoes (elk-rs
`low_level_sorting_criterion.rs`). The Rust `#[default]` is `BY_SIZE_AND_SHAPE`
(`LowLevelSortingCriterion.rustDefault`), not the first constructor.
-/
namespace Elk.Alg.Common.Compaction.Options

/-- `org.eclipse.elk.alg.common.compaction.options.LowLevelSortingCriterion`. -/
elk_enum LowLevelSortingCriterion := bySize bySizeAndShape

namespace LowLevelSortingCriterion

/-- Rust `LowLevelSortingCriterion::default()`. -/
def rustDefault : LowLevelSortingCriterion := .bySizeAndShape

end LowLevelSortingCriterion

end Elk.Alg.Common.Compaction.Options
