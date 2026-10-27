import Elk.Graph
import Elk.Alg.RectPacking.Util.DrawingData
/-!
# `org.eclipse.elk.alg.rectpacking.p1widthapproximation.Calculations`

Port of `p1widthapproximation/calculations.rs` (elk-rs): geometry helpers of the width
approximation. They only read the rectangles, so they are pure functions of the `ElkGraph`.
-/
namespace Elk.Alg.RectPacking.P1WidthApproximation

open Elk.Graph Elk.Core.Util Elk.Alg.RectPacking.Util

namespace Calculations

/-- `width_lpr_or_lpb(drawing_width, x, width)`: `max(drawing_width, x + width)`. -/
@[inline] def widthLprOrLpb (drawingWidth x width : Float) : Float := fmax drawingWidth (x + width)

/-- `height_lpr_or_lpb(drawing_height, y, height)`: `max(drawing_height, y + height)`. -/
@[inline] def heightLprOrLpb (drawingHeight y height : Float) : Float := fmax drawingHeight (y + height)

/-- `calculate_y_for_lpr(x, placed_rects, last_placed, node_node_spacing)`: the y below the
closest placed rectangle above `x` (whose right border plus spacing lies right of `x`): its bottom
border plus spacing, or `0` if there is none. The first closest neighbor wins on ties. -/
def calculateYForLpr (g : ElkGraph) (x : Float) (placedRects : Array NodeId) (lastPlaced : NodeId)
    (nodeNodeSpacing : Float) : Float := Id.run do
  let mut found := false
  let mut closestNeighborBottomBorder : Float := 0.0
  let lastPlacedY := (g.node lastPlaced).y
  for placedRect in placedRects do
    let pr := g.node placedRect
    let placedRectBottomBorder := pr.y + pr.height
    let passesConstraint := x < pr.x + pr.width + nodeNodeSpacing
    if passesConstraint && (!found ||
        lastPlacedY - placedRectBottomBorder < lastPlacedY - closestNeighborBottomBorder) then
      found := true
      closestNeighborBottomBorder := placedRectBottomBorder
  return if !found then 0.0 else closestNeighborBottomBorder + nodeNodeSpacing

/-- `calculate_x_for_lpb(y, placed_rects, last_placed, node_node_spacing)`: the x right of the
closest placed rectangle left of `y` (whose bottom border plus spacing lies below `y`): its right
border plus spacing, or `0` if there is none. -/
def calculateXForLpb (g : ElkGraph) (y : Float) (placedRects : Array NodeId) (lastPlaced : NodeId)
    (nodeNodeSpacing : Float) : Float := Id.run do
  let mut found := false
  let mut closestNeighborRightBorder : Float := 0.0
  let lastPlacedX := (g.node lastPlaced).x
  for placedRect in placedRects do
    let pr := g.node placedRect
    let placedRectRightBorder := pr.x + pr.width
    let passesConstraint := y < pr.y + pr.height + nodeNodeSpacing
    if passesConstraint && (!found ||
        lastPlacedX - placedRectRightBorder < lastPlacedX - closestNeighborRightBorder) then
      found := true
      closestNeighborRightBorder := placedRectRightBorder
  return if !found then 0.0 else closestNeighborRightBorder + nodeNodeSpacing

/-- `calculate_area_lpr(last_placed, to_place, lpr_opt)`: the area of the bounding box of the last
placed rectangle and the rectangle to place at the LPR candidate position. -/
def calculateAreaLpr (g : ElkGraph) (lastPlaced toPlace : NodeId) (lprOpt : DrawingData) : Float :=
  let lp := g.node lastPlaced
  let tp := g.node toPlace
  let lastPlacedBottomBorder := lp.y + lp.height
  let toPlaceBottomBorder := lprOpt.nextYCoordinate + tp.height
  let maxYLpr := fmax lastPlacedBottomBorder toPlaceBottomBorder
  let heightLpr := maxYLpr - fmin lp.y lprOpt.nextYCoordinate
  let widthLpr := lprOpt.nextXCoordinate + tp.width - lp.x
  widthLpr * heightLpr

/-- `calculate_area_lpb(last_placed, to_place, lpb_opt)`: the area of the bounding box of the last
placed rectangle and the rectangle to place at the LPB candidate position. -/
def calculateAreaLpb (g : ElkGraph) (lastPlaced toPlace : NodeId) (lpbOpt : DrawingData) : Float :=
  let lp := g.node lastPlaced
  let tp := g.node toPlace
  let lastPlacedRightBorder := lp.x + lp.width
  let toPlaceRightBorder := lpbOpt.nextXCoordinate + tp.width
  let maxXLpb := fmax lastPlacedRightBorder toPlaceRightBorder
  let widthLpb := maxXLpb - fmin lp.x lpbOpt.nextXCoordinate
  let heightLpb := lpbOpt.nextYCoordinate + tp.height - lp.y
  widthLpb * heightLpb

end Calculations

end Elk.Alg.RectPacking.P1WidthApproximation
