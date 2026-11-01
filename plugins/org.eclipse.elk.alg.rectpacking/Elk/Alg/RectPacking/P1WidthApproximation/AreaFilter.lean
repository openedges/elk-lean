import Elk.Alg.RectPacking.P1WidthApproximation.BestCandidateFilter
/-!
# `org.eclipse.elk.alg.rectpacking.p1widthapproximation.AreaFilter`

Port of `p1widthapproximation/area_filter.rs` (elk-rs): keeps the candidates with the smallest
padded area `(w + left + right) * (h + top + bottom)` (exact float equality).
-/
namespace Elk.Alg.RectPacking.P1WidthApproximation

open Elk.Core.Util Elk.Core.Math Elk.Alg.RectPacking.Util

namespace AreaFilter

/-- The padded area of a candidate. -/
@[inline] def paddedArea (d : DrawingData) (padding : ElkPadding) : Float :=
  (d.drawingWidth + (padding.left + padding.right)) * (d.drawingHeight + (padding.top + padding.bottom))

/-- `filter_list(candidates, aspect_ratio, padding)`. -/
def filterList (candidates : Array DrawingData) (_aspectRatio : Float) (padding : ElkPadding) :
    Array DrawingData := Id.run do
  let mut minArea := Float.posInf
  for opt in candidates do
    minArea := javaMin minArea (paddedArea opt padding)
  return candidates.filter fun c => paddedArea c padding == minArea

/-- `AreaFilter` as a `BestCandidateFilter`. -/
def filter : BestCandidateFilter := ⟨filterList⟩

end AreaFilter

end Elk.Alg.RectPacking.P1WidthApproximation
