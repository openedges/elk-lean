import Elk.Core.Math.ElkRectangle
import Elk.Alg.Common.Geometry.TEdge
/-!
# `org.eclipse.elk.alg.common.utils.Utils`

Geometry helpers for rectangles (elk-rs `utils/geometry_utils.rs`).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Common.Utils

open Elk.Core.Util Elk.Core.Math Elk.Alg.Common

namespace Utils

/-- `Utils.overlap(r1, r2)`: `1` if the rectangles do not overlap, otherwise `1 +` the
relative overlap along the center line (`0` for identical centers). -/
def overlap (r1 r2 : ElkRectangle) : Float := Id.run do
  let horizontalOverlap := fmin (r1.x - (r2.x + r2.width)).abs (r1.x + r1.width - r2.x).abs
  let verticalOverlap := fmin (r1.y - (r2.y + r2.height)).abs (r1.y + r1.height - r2.y).abs
  let horizontalCenterDistance := ((r1.x + r1.width / fl2p0) - (r2.x + r2.width / fl2p0)).abs
  if horizontalCenterDistance > r1.width / fl2p0 + r2.width / fl2p0 then
    return fl1p0
  let verticalCenterDistance := ((r1.y + r1.height / fl2p0) - (r2.y + r2.height / fl2p0)).abs
  if verticalCenterDistance > r1.height / fl2p0 + r2.height / fl2p0 then
    return fl1p0
  if horizontalCenterDistance == fl0p0 && verticalCenterDistance == fl0p0 then
    return fl0p0
  if horizontalCenterDistance == fl0p0 then
    return verticalOverlap / verticalCenterDistance + fl1p0
  if verticalCenterDistance == fl0p0 then
    return horizontalOverlap / horizontalCenterDistance + fl1p0
  return fmin (horizontalOverlap / horizontalCenterDistance)
    (verticalOverlap / verticalCenterDistance) + fl1p0

/-- `Utils.getRectEdges(r)`: top, left, right, bottom edges in this order:
`(tl,tr)`, `(tl,bl)`, `(br,tr)`, `(br,bl)`. -/
def getRectEdges (r : ElkRectangle) : Array TEdge :=
  #[TEdge.new r.topLeft r.topRight,
    TEdge.new r.topLeft r.bottomLeft,
    TEdge.new r.bottomRight r.topRight,
    TEdge.new r.bottomRight r.bottomLeft]

end Utils

end Elk.Alg.Common.Utils
