import Elk.Graph
import Elk.Alg.RectPacking.Util.DrawingData
/-!
# `org.eclipse.elk.alg.rectpacking.p1widthapproximation.Calculations`

Port of `p1widthapproximation/calculations.rs` (elk-rs): geometry helpers of the width
approximation. They only read the rectangles, so they are pure functions of the `ElkGraph`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.RectPacking.P1WidthApproximation

open Elk.Graph Elk.Core.Util Elk.Alg.RectPacking.Util

namespace Calculations

/-- `width_lpr_or_lpb(drawing_width, x, width)`: `max(drawing_width, x + width)`. -/
@[inline] def widthLprOrLpb (drawingWidth x width : Float) : Float := fmax drawingWidth (x + width)

/-- `height_lpr_or_lpb(drawing_height, y, height)`: `max(drawing_height, y + height)`. -/
@[inline] def heightLprOrLpb (drawingHeight y height : Float) : Float := fmax drawingHeight (y + height)

/-- An index below `a.usize` is in bounds. -/
theorem usize_lt_size {a : FloatArray} {i : USize} (h : i < a.usize) : i.toNat < a.size := by
  have h1 : i.toNat < a.usize.toNat := (USize.lt_iff_toNat_lt).mp h
  have h2 : a.usize.toNat ≤ a.size := by
    simp only [FloatArray.usize, Nat.toUSize]
    exact Nat.mod_le _ _
  omega

/-- `FloatArray.push` adds one element. -/
theorem size_push (a : FloatArray) (v : Float) : (a.push v).size = a.size + 1 := by
  cases a; simp [FloatArray.push, FloatArray.size]

/-- The borders of the placed rectangles in placement order: right border `x + width` and bottom
border `y + height` of rectangle `i` at index `i`. The width approximation scans all placed
rectangles for every candidate (`calculate_y_for_lpr` / `calculate_x_for_lpb`) and only ever uses
these two sums (computed once here, the same float operations), so the scan reads unboxed contiguous
values instead of the `ElkNode`s. -/
structure PlacedRects where
  right : FloatArray := .empty
  bottom : FloatArray := .empty
  hsize : right.size = bottom.size := by rfl

instance : Inhabited PlacedRects := ⟨{}⟩

namespace PlacedRects

/-- Appends the borders of a rectangle with the given geometry. -/
@[inline] def push (p : PlacedRects) (x y width height : Float) : PlacedRects :=
  { right := p.right.push (x + width), bottom := p.bottom.push (y + height)
    hsize := by rw [size_push, size_push, p.hsize] }

/-- The borders of the given rectangles. -/
def ofNodes (g : ElkGraph) (rects : Array NodeId) : PlacedRects :=
  rects.foldl (init := {}) fun p r => let n := g.node r; p.push n.x n.y n.width n.height

end PlacedRects

/-! The scans of `calculate_y_for_lpr` and `calculate_x_for_lpb` share one shape: over the placed
rectangles in order, the rectangles that pass the constraint `v < a[i] + spacing` (`a`: the right
borders for LPR, the bottom borders for LPB) are candidates, and the first candidate wins until a
later one has a strictly smaller distance `last - b[i]` (`b`: the bottom borders for LPR, the right
borders for LPB). The result is the closest border plus spacing, or `0` without candidates.

The scan jumps from one taken candidate to the next: `nextTaken` returns the index of the next
rectangle that passes the constraint and is strictly closer than the current closest border; the
first candidate is taken unconditionally (`nextCandidate`). Between two takes the distance is loop
invariant, so the inner loops carry no float state and the (rare) takes are branches instead of a
select chain. Tail recursive with unboxed parameters and `USize` indices; the index proofs make the
loads unchecked. -/

/-- The index of the first rectangle `≥ i` that passes the constraint (`a.usize` if none). -/
private partial def nextCandidate (a : FloatArray) (v spacing : Float) (i : USize) : USize :=
  if h : i < a.usize then
    if v < a.uget i (usize_lt_size h) + spacing then i else nextCandidate a v spacing (i + 1)
  else i

/-- The index of the first rectangle `≥ i` that passes the constraint and whose distance
`last - b[j]` is strictly smaller than `dist` (`a.usize` if none). -/
private partial def nextTaken (a b : FloatArray) (hab : a.size = b.size) (v last spacing dist : Float)
    (i : USize) : USize :=
  if h : i < a.usize then
    have ha : i.toNat < a.size := usize_lt_size h
    have hb : i.toNat < b.size := hab ▸ ha
    if v < a.uget i ha + spacing && last - b.uget i hb < dist then i
    else nextTaken a b hab v last spacing dist (i + 1)
  else i

/-- The scan after a taken candidate (`closest` = its border, `dist` = `last - closest`), from
`i` on. -/
private partial def closestFound (a b : FloatArray) (hab : a.size = b.size) (v last spacing : Float)
    (i : USize) (closest dist : Float) : Float :=
  let j := nextTaken a b hab v last spacing dist i
  if h : j < a.usize then
    have hb : j.toNat < b.size := hab ▸ usize_lt_size h
    let border := b.uget j hb
    closestFound a b hab v last spacing (j + 1) border (last - border)
  else closest + spacing

/-- The whole scan (see above; `zero = 0.0`). -/
private def closestScan (a b : FloatArray) (hab : a.size = b.size) (v last spacing zero : Float) :
    Float :=
  let j := nextCandidate a v spacing 0
  if h : j < a.usize then
    have hb : j.toNat < b.size := hab ▸ usize_lt_size h
    let border := b.uget j hb
    closestFound a b hab v last spacing (j + 1) border (last - border)
  else zero

/-- `calculate_y_for_lpr` on the placed rectangle borders (`lastPlacedY`: y of the last placed
rectangle). -/
@[inline] def calculateYForLprSoA (x : Float) (placed : PlacedRects) (lastPlacedY nodeNodeSpacing : Float) :
    Float :=
  closestScan placed.right placed.bottom placed.hsize x lastPlacedY nodeNodeSpacing fl0p0

/-- `calculate_x_for_lpb` on the placed rectangle borders (`lastPlacedX`: x of the last placed
rectangle). -/
@[inline] def calculateXForLpbSoA (y : Float) (placed : PlacedRects) (lastPlacedX nodeNodeSpacing : Float) :
    Float :=
  closestScan placed.bottom placed.right placed.hsize.symm y lastPlacedX nodeNodeSpacing fl0p0

/-- `(calculate_y_for_lpr(x, ..), calculate_x_for_lpb(y, ..))` over the placed rectangle borders
(`lastPlacedX`/`lastPlacedY`: position of the last placed rectangle). -/
@[inline] def calculateLprAndLpbSoA (x y : Float) (placed : PlacedRects) (lastPlacedX lastPlacedY nodeNodeSpacing : Float) :
    Float × Float :=
  (calculateYForLprSoA x placed lastPlacedY nodeNodeSpacing,
   calculateXForLpbSoA y placed lastPlacedX nodeNodeSpacing)

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
