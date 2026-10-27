import Elk.Core.Math.Spacing
import Elk.Alg.RectPacking.Util.DrawingData
/-!
# `org.eclipse.elk.alg.rectpacking.p1widthapproximation.BestCandidateFilter`

Port of `p1widthapproximation/best_candidate_filter.rs` (elk-rs): the filter interface of the
width approximation (a closure field, PORTING §14).
-/
namespace Elk.Alg.RectPacking.P1WidthApproximation

open Elk.Core.Math Elk.Alg.RectPacking.Util

/-- `BestCandidateFilter`: keeps the best candidates by one criterion (input order kept). -/
structure BestCandidateFilter where
  /-- `filter_list(candidates, aspect_ratio, padding)`. -/
  filterList : Array DrawingData → Float → ElkPadding → Array DrawingData

end Elk.Alg.RectPacking.P1WidthApproximation
