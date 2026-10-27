import Elk.Core.Math.KVector
/-!
# `org.eclipse.elk.core.math.ElkRectangle`
-/
namespace Elk.Core.Math

open Elk.Core.Util

structure ElkRectangle where
  x : Float := 0
  y : Float := 0
  width : Float := 0
  height : Float := 0
  deriving Repr, Inhabited, BEq

namespace ElkRectangle

def ofValues (x y width height : Float) : ElkRectangle := ⟨x, y, width, height⟩

@[inline] def position (r : ElkRectangle) : KVector := ⟨r.x, r.y⟩
@[inline] def topLeft (r : ElkRectangle) : KVector := ⟨r.x, r.y⟩
@[inline] def topRight (r : ElkRectangle) : KVector := ⟨r.x + r.width, r.y⟩
@[inline] def bottomLeft (r : ElkRectangle) : KVector := ⟨r.x, r.y + r.height⟩
@[inline] def bottomRight (r : ElkRectangle) : KVector := ⟨r.x + r.width, r.y + r.height⟩
@[inline] def center (r : ElkRectangle) : KVector := ⟨r.x + r.width / 2.0, r.y + r.height / 2.0⟩
@[inline] def maxX (r : ElkRectangle) : Float := r.x + r.width
@[inline] def maxY (r : ElkRectangle) : Float := r.y + r.height

/-- `union(other)`: the smallest rectangle containing both. -/
def union (r o : ElkRectangle) : ElkRectangle :=
  let x1 := fmin r.x o.x
  let y1 := fmin r.y o.y
  let x2 := fmax (r.x + r.width) (o.x + o.width)
  let y2 := fmax (r.y + r.height) (o.y + o.height)
  let (x1, x2) := if x2 < x1 then (x2, x1) else (x1, x2)
  let (y1, y2) := if y2 < y1 then (y2, y1) else (y1, y2)
  ⟨x1, y1, x2 - x1, y2 - y1⟩

/-- `move(offset)`. -/
@[inline] def moveBy (r : ElkRectangle) (o : KVector) : ElkRectangle := { r with x := r.x + o.x, y := r.y + o.y }

/-- `intersects(rect)`: strict overlap test. -/
def intersects (r o : ElkRectangle) : Bool :=
  r.x < o.x + o.width && r.x + r.width > o.x && r.y + r.height > o.y && r.y < o.y + o.height

instance : ToString ElkRectangle :=
  ⟨fun r => s!"Rect[x={Float.toRustDisplay r.x},y={Float.toRustDisplay r.y},w={Float.toRustDisplay r.width},h={Float.toRustDisplay r.height}]"⟩

end ElkRectangle

end Elk.Core.Math
