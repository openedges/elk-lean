import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.common.compaction.options.HighLevelSortingCriterion`

Primary sorting criteria for the processing order of polyominoes (elk-rs
`high_level_sorting_criterion.rs`). The Rust `#[default]` is the first constructor.
-/
namespace Elk.Alg.Common.Compaction.Options

/-- `org.eclipse.elk.alg.common.compaction.options.HighLevelSortingCriterion`. -/
elk_enum HighLevelSortingCriterion := numOfExternalSidesThanNumOfExtensionsLast
  cornerCasesThanSingleSideLast

namespace HighLevelSortingCriterion

/-- Rust `HighLevelSortingCriterion::default()`. -/
def rustDefault : HighLevelSortingCriterion := .numOfExternalSidesThanNumOfExtensionsLast

end HighLevelSortingCriterion

end Elk.Alg.Common.Compaction.Options
