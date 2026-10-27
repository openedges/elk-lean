import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.rectpacking.util.DrawingDataDescriptor`

Port of `util/drawing_data_descriptor.rs` (elk-rs): the candidate positions of the width
approximation (`LPR`/`LPB` = right of / below the last placed rectangle, `WDR`/`WDB` = right of /
below the whole drawing) and the whole-drawing marker.
-/
namespace Elk.Alg.RectPacking.Util

/-- `DrawingDataDescriptor`. -/
elk_enum DrawingDataDescriptor :=
  candidatePositionLastPlacedRight candidatePositionLastPlacedBelow
  candidatePositionWholeDrawingRight candidatePositionWholeDrawingBelow wholeDrawing

end Elk.Alg.RectPacking.Util
