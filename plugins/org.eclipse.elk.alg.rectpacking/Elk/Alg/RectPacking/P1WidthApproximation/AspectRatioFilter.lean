import Elk.Alg.RectPacking.P1WidthApproximation.BestCandidateFilter
/-!
# `org.eclipse.elk.alg.rectpacking.p1widthapproximation.AspectRatioFilter`

Port of `p1widthapproximation/aspect_ratio_filter.rs` (elk-rs): keeps the candidates whose
padded aspect ratio `(w + left + right) / (h + top + bottom)` deviates least from the desired
aspect ratio (exact float equality).
-/
namespace Elk.Alg.RectPacking.P1WidthApproximation

open Elk.Core.Util Elk.Core.Math Elk.Alg.RectPacking.Util

namespace AspectRatioFilter

/-- `|ratio - aspect_ratio|` of a candidate with padding. -/
@[inline] def deviation (d : DrawingData) (aspectRatio : Float) (padding : ElkPadding) : Float :=
  let ratio := (d.drawingWidth + (padding.left + padding.right)) /
    (d.drawingHeight + (padding.top + padding.bottom))
  (ratio - aspectRatio).abs

/-- `filter_list(candidates, aspect_ratio, padding)`. -/
def filterList (candidates : Array DrawingData) (aspectRatio : Float) (padding : ElkPadding) :
    Array DrawingData := Id.run do
  let mut smallestDeviation := Float.posInf
  for opt in candidates do
    smallestDeviation := javaMin smallestDeviation (deviation opt aspectRatio padding)
  return candidates.filter fun c => deviation c aspectRatio padding == smallestDeviation

/-- `AspectRatioFilter` as a `BestCandidateFilter`. -/
def filter : BestCandidateFilter := ⟨filterList⟩

end AspectRatioFilter

end Elk.Alg.RectPacking.P1WidthApproximation
