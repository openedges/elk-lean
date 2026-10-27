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

/-- The geometry of the placed rectangles in placement order, interleaved in one float array
(`x, y, width, height` of rectangle `i` at `4i .. 4i+3`). The width approximation scans all
placed rectangles for every candidate (`calculate_y_for_lpr` / `calculate_x_for_lpb`), so the scan
reads unboxed contiguous values instead of the `ElkNode`s (performance; the values are those of
the nodes). -/
structure PlacedRects where
  data : FloatArray := .empty
  deriving Inhabited

namespace PlacedRects

/-- Appends the current geometry of a rectangle. -/
@[inline] def push (p : PlacedRects) (x y width height : Float) : PlacedRects :=
  { data := ((p.data.push x).push y |>.push width).push height }

/-- The geometry of the given rectangles. -/
def ofNodes (g : ElkGraph) (rects : Array NodeId) : PlacedRects :=
  rects.foldl (init := {}) fun p r => let n := g.node r; p.push n.x n.y n.width n.height

end PlacedRects

/-- Loop of `calculateYForLprSoA` (tail recursive, unboxed state; `i` steps by 4). -/
private def yForLprLoop (d : FloatArray) (x lastPlacedY nodeNodeSpacing : Float) (i : Nat)
    (found : Bool) (closestNeighborBottomBorder : Float) : Float :=
  if h : i + 3 < d.size then
    let placedRectBottomBorder := d[i + 1] + d[i + 3]
    let passesConstraint := x < d[i] + d[i + 2] + nodeNodeSpacing
    if passesConstraint && (!found ||
        lastPlacedY - placedRectBottomBorder < lastPlacedY - closestNeighborBottomBorder) then
      yForLprLoop d x lastPlacedY nodeNodeSpacing (i + 4) true placedRectBottomBorder
    else
      yForLprLoop d x lastPlacedY nodeNodeSpacing (i + 4) found closestNeighborBottomBorder
  else if !found then 0.0 else closestNeighborBottomBorder + nodeNodeSpacing
  termination_by d.size - i

/-- `calculate_y_for_lpr` on the placed rectangle geometry (`lastPlacedY`: y of the last placed
rectangle). -/
@[inline] def calculateYForLprSoA (x : Float) (placed : PlacedRects) (lastPlacedY nodeNodeSpacing : Float) :
    Float :=
  yForLprLoop placed.data x lastPlacedY nodeNodeSpacing 0 false 0.0

/-- Loop of `calculateXForLpbSoA` (tail recursive, unboxed state; `i` steps by 4). -/
private def xForLpbLoop (d : FloatArray) (y lastPlacedX nodeNodeSpacing : Float) (i : Nat)
    (found : Bool) (closestNeighborRightBorder : Float) : Float :=
  if h : i + 3 < d.size then
    let placedRectRightBorder := d[i] + d[i + 2]
    let passesConstraint := y < d[i + 1] + d[i + 3] + nodeNodeSpacing
    if passesConstraint && (!found ||
        lastPlacedX - placedRectRightBorder < lastPlacedX - closestNeighborRightBorder) then
      xForLpbLoop d y lastPlacedX nodeNodeSpacing (i + 4) true placedRectRightBorder
    else
      xForLpbLoop d y lastPlacedX nodeNodeSpacing (i + 4) found closestNeighborRightBorder
  else if !found then 0.0 else closestNeighborRightBorder + nodeNodeSpacing
  termination_by d.size - i

/-- `calculate_x_for_lpb` on the placed rectangle geometry (`lastPlacedX`: x of the last placed
rectangle). -/
@[inline] def calculateXForLpbSoA (y : Float) (placed : PlacedRects) (lastPlacedX nodeNodeSpacing : Float) :
    Float :=
  xForLpbLoop placed.data y lastPlacedX nodeNodeSpacing 0 false 0.0

/-- Loop of `calculateLprAndLpbSoA`: both scans in one pass (tail recursive, unboxed state). -/
private def lprLpbLoop (d : FloatArray) (x lastPlacedY y lastPlacedX nodeNodeSpacing : Float) (i : Nat)
    (foundY : Bool) (closestNeighborBottomBorder : Float)
    (foundX : Bool) (closestNeighborRightBorder : Float) : Float × Float :=
  if h : i + 3 < d.size then
    let px := d[i]
    let py := d[i + 1]
    let pw := d[i + 2]
    let ph := d[i + 3]
    let placedRectBottomBorder := py + ph
    let takeY := x < px + pw + nodeNodeSpacing && (!foundY ||
        lastPlacedY - placedRectBottomBorder < lastPlacedY - closestNeighborBottomBorder)
    let placedRectRightBorder := px + pw
    let takeX := y < py + ph + nodeNodeSpacing && (!foundX ||
        lastPlacedX - placedRectRightBorder < lastPlacedX - closestNeighborRightBorder)
    lprLpbLoop d x lastPlacedY y lastPlacedX nodeNodeSpacing (i + 4)
      (foundY || takeY) (if takeY then placedRectBottomBorder else closestNeighborBottomBorder)
      (foundX || takeX) (if takeX then placedRectRightBorder else closestNeighborRightBorder)
  else
    (if !foundY then 0.0 else closestNeighborBottomBorder + nodeNodeSpacing,
     if !foundX then 0.0 else closestNeighborRightBorder + nodeNodeSpacing)
  termination_by d.size - i

/-- `(calculate_y_for_lpr(x, ..), calculate_x_for_lpb(y, ..))` in one pass over the placed
rectangle geometry (`lastPlacedX`/`lastPlacedY`: position of the last placed rectangle). -/
@[inline] def calculateLprAndLpbSoA (x y : Float) (placed : PlacedRects) (lastPlacedX lastPlacedY nodeNodeSpacing : Float) :
    Float × Float :=
  lprLpbLoop placed.data x lastPlacedY y lastPlacedX nodeNodeSpacing 0 false 0.0 false 0.0

/-- `calculate_y_for_lpr(x, placed_rects, last_placed, node_node_spacing)`: the y below the
closest placed rectangle above `x` (whose right border plus spacing lies right of `x`): its bottom
border plus spacing, or `0` if there is none. The first closest neighbor wins on ties. -/
def calculateYForLpr (g : ElkGraph) (x : Float) (placedRects : Array NodeId) (lastPlaced : NodeId)
    (nodeNodeSpacing : Float) : Float :=
  calculateYForLprSoA x (PlacedRects.ofNodes g placedRects) (g.node lastPlaced).y nodeNodeSpacing

/-- `calculate_x_for_lpb(y, placed_rects, last_placed, node_node_spacing)`: the x right of the
closest placed rectangle left of `y` (whose bottom border plus spacing lies below `y`): its right
border plus spacing, or `0` if there is none. -/
def calculateXForLpb (g : ElkGraph) (y : Float) (placedRects : Array NodeId) (lastPlaced : NodeId)
    (nodeNodeSpacing : Float) : Float :=
  calculateXForLpbSoA y (PlacedRects.ofNodes g placedRects) (g.node lastPlaced).x nodeNodeSpacing

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
