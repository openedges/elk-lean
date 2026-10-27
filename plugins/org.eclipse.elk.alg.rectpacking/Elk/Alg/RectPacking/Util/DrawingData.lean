import Elk.Alg.RectPacking.Util.DrawingDataDescriptor
import Elk.Alg.RectPacking.Util.DrawingUtil
/-!
# `org.eclipse.elk.alg.rectpacking.util.DrawingData`

Port of `util/drawing_data.rs` (elk-rs): the metrics of a (candidate) drawing. Area, aspect ratio
and scale measure are recomputed whenever the drawing width or height changes, and only when
both are positive (otherwise the previous values, initially `0`, are kept).
-/
namespace Elk.Alg.RectPacking.Util

/-- `DrawingData`. -/
structure DrawingData where
  scaleMeasure : Float := 0.0
  drawingWidth : Float
  drawingHeight : Float
  area : Float := 0.0
  aspectRatio : Float := 0.0
  desiredAspectRatio : Float
  placementOption : DrawingDataDescriptor
  nextXCoordinate : Float := 0.0
  nextYCoordinate : Float := 0.0
  deriving Inhabited, Repr

namespace DrawingData

/-- `calc_area_aspect_ratio_scale_measure()`. -/
def calcAreaAspectRatioScaleMeasure (d : DrawingData) : DrawingData :=
  if d.drawingWidth > 0.0 && d.drawingHeight > 0.0 then
    { d with area := d.drawingWidth * d.drawingHeight
             aspectRatio := d.drawingWidth / d.drawingHeight
             scaleMeasure := DrawingUtil.computeScaleMeasure d.drawingWidth d.drawingHeight d.desiredAspectRatio }
  else d

/-- `DrawingData::with_coordinates(desired_aspect_ratio, drawing_width, drawing_height,
placement_option, next_x_coordinate, next_y_coordinate)`. -/
def withCoordinates (desiredAspectRatio drawingWidth drawingHeight : Float)
    (placementOption : DrawingDataDescriptor) (nextXCoordinate nextYCoordinate : Float) : DrawingData :=
  calcAreaAspectRatioScaleMeasure
    { drawingWidth, drawingHeight, desiredAspectRatio, placementOption, nextXCoordinate, nextYCoordinate }

/-- `DrawingData::new(desired_aspect_ratio, drawing_width, drawing_height, placement_option)`
(next coordinates `0`). -/
def new (desiredAspectRatio drawingWidth drawingHeight : Float)
    (placementOption : DrawingDataDescriptor) : DrawingData :=
  withCoordinates desiredAspectRatio drawingWidth drawingHeight placementOption 0.0 0.0

/-- `set_drawing_width(width)` (recomputes the metrics). -/
def setDrawingWidth (d : DrawingData) (drawingWidth : Float) : DrawingData :=
  calcAreaAspectRatioScaleMeasure { d with drawingWidth }

/-- `set_drawing_height(height)` (recomputes the metrics). -/
def setDrawingHeight (d : DrawingData) (drawingHeight : Float) : DrawingData :=
  calcAreaAspectRatioScaleMeasure { d with drawingHeight }

/-- `set_placement_option(option)`. -/
def setPlacementOption (d : DrawingData) (placementOption : DrawingDataDescriptor) : DrawingData :=
  { d with placementOption }

end DrawingData

end Elk.Alg.RectPacking.Util
