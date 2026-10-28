import Elk.Core.Util.Sort
import Elk.Core.Math.ElkRectangle
import Elk.Alg.Common.Geometry.Point
/-!
# `org.eclipse.elk.alg.common.RectilinearConvexHull`

The rectilinear convex hull is represented by four staircases
(elk-rs `rectilinear_convex_hull.rs`):

```
  q1 | q2
 ---------
  q4 | q3
```

The Rust code drives its event handlers with `compaction::Scanline::execute`,
which is a stable sort with the given comparator followed by one handler call
per point in sorted order. That is inlined here (`stableSort` + loop) so this
module does not depend on the compaction package.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.Common

open Elk.Core.Util Elk.Core.Math

/-- `org.eclipse.elk.alg.common.RectilinearConvexHull` (Rust `RectilinearConvexHull`). -/
structure RectilinearConvexHull where
  /-- This hull's determined points. -/
  hull : Array Point := #[]
  /-- Last point with maximal x (`>=`). -/
  xMax1 : Option Point := none
  /-- Previous `xMax1`. -/
  xMax2 : Option Point := none
  /-- Last point with minimal x (`<=`). -/
  xMin1 : Option Point := none
  /-- Previous `xMin1`. -/
  xMin2 : Option Point := none
  /-- Last point with minimal y (`<=`). -/
  yMin1 : Option Point := none
  /-- Previous `yMin1`. -/
  yMin2 : Option Point := none
  /-- Last point with maximal y (`>=`). -/
  yMax1 : Option Point := none
  /-- Previous `yMax1`. -/
  yMax2 : Option Point := none
  deriving Repr, Inhabited

namespace RectilinearConvexHull

/-- Rust `right_high_first`. -/
def rightHighFirst (p1 p2 : Point) : Ordering :=
  if p1.x == p2.x then Float.comparePartial p2.y p1.y else Float.comparePartial p1.x p2.x

/-- Rust `right_low_first`. -/
def rightLowFirst (p1 p2 : Point) : Ordering :=
  if p1.x == p2.x then Float.comparePartial p1.y p2.y else Float.comparePartial p1.x p2.x

/-- Rust `left_high_first`. -/
def leftHighFirst (p1 p2 : Point) : Ordering :=
  if p1.x == p2.x then Float.comparePartial p2.y p1.y else Float.comparePartial p2.x p1.x

/-- Rust `left_low_first`. -/
def leftLowFirst (p1 p2 : Point) : Ordering :=
  if p1.x == p2.x then Float.comparePartial p1.y p2.y else Float.comparePartial p2.x p1.x

/-- Rust `right_special_order` (used to split the hull into rectangles). -/
def rightSpecialOrder (p1 p2 : Point) : Ordering := Id.run do
  if p1.x == p2.x then
    if p1.quadrant == p2.quadrant || Quadrant.isBothLeftOrBothRight p1.quadrant p2.quadrant then
      let val : Ordering := if p1.quadrant.isLeft then .gt else .lt
      if p1.convex && !p2.convex then
        return val
      else if !p1.convex && p2.convex then
        return val.swap
    return Quadrant.cmp p1.quadrant p2.quadrant
  return Float.comparePartial p1.x p2.x

/-- Rust `MaximalElementsEventHandler` run over `points` sorted with `cmp`
(`Scanline::execute`): the staircase of maximal elements of one quadrant. -/
def maximalElements (quadrant : Quadrant) (points : Array Point) (cmp : Point → Point → Ordering) :
    Array Point := Id.run do
  let (initialY, reverse) := match quadrant with
    | .q1 | .q2 => (Float.posInf, true)
    | .q3 | .q4 => (Float.negInf, false)
  let mut maximalY := initialY
  let mut out : Array Point := #[]
  for point in stableSort points cmp do
    let c := Float.comparePartial point.y maximalY
    let c := if reverse then c.swap else c
    if c == .gt then
      out := out.push (Point.withQuadrant point.x point.y quadrant)
      maximalY := point.y
  return out

/-- Rust `add_concave_corners`: inserts a concave corner `(next.x, last.y)` before every
point but the first. -/
def addConcaveCorners (points : Array Point) (quadrant : Quadrant) : Array Point := Id.run do
  let some first := points[0]? | return points
  let mut out : Array Point := #[first]
  let mut last := first
  for next in points.extract 1 points.size do
    out := out.push { Point.withQuadrant next.x last.y quadrant with convex := false }
    out := out.push next
    last := next
  return out

/-- `RectilinearConvexHull.of(points)`. -/
def «of» (points : Array Point) : RectilinearConvexHull := Id.run do
  let mut hull : RectilinearConvexHull := {}
  for p in points do
    if hull.xMax1.all (fun v => p.x >= v.x) then
      hull := { hull with xMax2 := hull.xMax1, xMax1 := some p }
    if hull.xMin1.all (fun v => p.x <= v.x) then
      hull := { hull with xMin2 := hull.xMin1, xMin1 := some p }
    if hull.yMax1.all (fun v => p.y >= v.y) then
      hull := { hull with yMax2 := hull.yMax1, yMax1 := some p }
    if hull.yMin1.all (fun v => p.y <= v.y) then
      hull := { hull with yMin2 := hull.yMin1, yMin1 := some p }
  let q1 := maximalElements .q1 points rightLowFirst
  let q4 := maximalElements .q4 points rightHighFirst
  let q2 := maximalElements .q2 points leftLowFirst
  let q3 := maximalElements .q3 points leftHighFirst
  let q1 := addConcaveCorners q1 .q1
  let q2 := addConcaveCorners q2 .q2
  let q3 := addConcaveCorners q3 .q3
  let q4 := addConcaveCorners q4 .q4
  return { hull with hull := q1 ++ q2.reverse ++ q3 ++ q4.reverse }

/-- `getHull()`. -/
@[inline] def getHull (h : RectilinearConvexHull) : Array Point := h.hull

/-- State of the Rust `RectangleEventHandler`. -/
private structure RectangleState where
  rects : Array ElkRectangle := #[]
  minY : Option Point := none
  maxY : Option Point := none
  lastX : Float := fl0p0
  queued : Option ElkRectangle := none
  queuedPoint : Option Point := none

/-- Rust `RectangleEventHandler::handle`. -/
private def handleRectangleEvent (s : RectangleState) (point : Point) : RectangleState := Id.run do
  let mut s := s
  match s.queued, s.queuedPoint with
  | some queued, some queuedPoint =>
    if point.x != queuedPoint.x || Quadrant.isOneLeftOneRight queuedPoint.quadrant point.quadrant then
      s := { s with rects := s.rects.push queued, lastX := queued.x + queued.width,
                    queued := none, queuedPoint := none }
  | _, _ => pure ()
  if point.quadrant.isUpper then
    s := { s with minY := some point }
  else
    s := { s with maxY := some point }
  let queueRect := if point.convex then
      (match point.quadrant with | .q2 | .q3 => true | _ => false)
    else
      (match point.quadrant with | .q1 | .q4 => true | _ => false)
  if queueRect then
    match s.minY, s.maxY with
    | some minY, some maxY =>
      let rect := ElkRectangle.ofValues s.lastX minY.y (point.x - s.lastX) (maxY.y - minY.y)
      s := { s with queued := some rect, queuedPoint := some point }
    | _, _ => pure ()
  return s

/-- `splitIntoRectangles()`: decomposes the hull into rectangles from left to right. -/
def splitIntoRectangles (h : RectilinearConvexHull) : Array ElkRectangle := Id.run do
  let mut lastX := 0.0
  if let some p1 := h.xMin1 then
    lastX := p1.x
  if let some p2 := h.xMin2 then
    lastX := fmin lastX p2.x
  let mut s : RectangleState := { lastX }
  for point in stableSort h.hull rightSpecialOrder do
    s := handleRectangleEvent s point
  match s.queued with
  | some queued => return s.rects.push queued
  | none => return s.rects

end RectilinearConvexHull

end Elk.Alg.Common
