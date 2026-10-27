import Elk.Alg.RectPacking.P1WidthApproximation.BestCandidateFilter
/-!
# `org.eclipse.elk.alg.rectpacking.p1widthapproximation.ScaleMeasureFilter`

Port of `p1widthapproximation/scale_measure_filter.rs` (elk-rs): keeps the candidates with the
largest scale measure of the padded drawing (`DrawingUtil.computeScaleMeasure`, the candidate's
own desired aspect ratio; exact float equality).
-/
namespace Elk.Alg.RectPacking.P1WidthApproximation

open Elk.Core.Util Elk.Core.Math Elk.Alg.RectPacking.Util

namespace ScaleMeasureFilter

/-- The scale measure of a candidate with padding. -/
@[inline] def paddedScale (d : DrawingData) (padding : ElkPadding) : Float :=
  DrawingUtil.computeScaleMeasure (d.drawingWidth + padding.left + padding.right)
    (d.drawingHeight + padding.top + padding.bottom) d.desiredAspectRatio

/-- `filter_list(candidates, aspect_ratio, padding)`. -/
def filterList (candidates : Array DrawingData) (_aspectRatio : Float) (padding : ElkPadding) :
    Array DrawingData := Id.run do
  let mut maxScale := Float.negInf
  for opt in candidates do
    maxScale := fmax maxScale (paddedScale opt padding)
  return candidates.filter fun c => paddedScale c padding == maxScale

/-- `ScaleMeasureFilter` as a `BestCandidateFilter`. -/
def filter : BestCandidateFilter := ⟨filterList⟩

end ScaleMeasureFilter

end Elk.Alg.RectPacking.P1WidthApproximation
