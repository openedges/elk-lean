import Elk.Graph.Enum
import Elk.Core.Math.KVector
/-!
# `org.eclipse.elk.alg.common.Point`

A very special point, used by the `RectilinearConvexHull` algorithm
(elk-rs `point.rs`). Equality and hashing only look at the coordinates, like
the Rust `PartialEq`/`Hash` implementations (`==` on the coordinates, hash of
`f64::to_bits`).
-/
namespace Elk.Alg.Common

open Elk Elk.Core.Util Elk.Core.Math

/-- `Point.Quadrant` (Java inner enum, Rust `Quadrant`): the quadrant a hull point
belongs to. Declaration order `Q1, Q4, Q2, Q3` is kept because the derived
ordering is used by `RectilinearConvexHull` (`rightSpecialOrder`). -/
elk_enum Quadrant := (q1 "Q1") (q4 "Q4") (q2 "Q2") (q3 "Q3")

namespace Quadrant

/-- `Quadrant.isUpper()`: `Q1` or `Q2`. -/
def isUpper : Quadrant → Bool
  | .q1 | .q2 => true
  | _ => false

/-- `Quadrant.isLeft()`: `Q1` or `Q4`. -/
def isLeft : Quadrant → Bool
  | .q1 | .q4 => true
  | _ => false

/-- `Quadrant.isBothLeftOrBothRight(q1, q2)`. -/
def isBothLeftOrBothRight : Quadrant → Quadrant → Bool
  | .q1, .q4 | .q4, .q1 | .q3, .q2 | .q2, .q3 => true
  | _, _ => false

/-- `Quadrant.isOneLeftOneRight(q1, q2)` (not symmetric, like the original). -/
def isOneLeftOneRight : Quadrant → Quadrant → Bool
  | .q1, .q2 | .q1, .q3 | .q4, .q3 | .q4, .q2 => true
  | _, _ => false

/-- Rust `Quadrant::cmp` (derived `Ord`, i.e. declaration order `Q1 < Q4 < Q2 < Q3`). -/
def cmp (a b : Quadrant) : Ordering := compare (ElkEnum.ordinal a) (ElkEnum.ordinal b)

end Quadrant

/-- `org.eclipse.elk.alg.common.Point` (Rust `Point`). -/
structure Point where
  /-- The x coordinate. -/
  x : Float
  /-- The y coordinate. -/
  y : Float
  /-- The quadrant this point is located in. -/
  quadrant : Quadrant := .q1
  /-- Whether this point is a convex corner of the hull. -/
  convex : Bool := true
  deriving Repr, Inhabited

namespace Point

/-- `Point::new(x, y)`: quadrant `Q1`, convex. -/
@[inline] def new (x y : Float) : Point := { x, y }

/-- `Point::with_quadrant(x, y, quadrant)`: convex. -/
@[inline] def withQuadrant (x y : Float) (quadrant : Quadrant) : Point := { x, y, quadrant }

/-- `Point::from(&KVector)`. -/
@[inline] def ofKVector (v : KVector) : Point := new v.x v.y

/-- Rust `PartialEq`: coordinates only (`==`). -/
instance : BEq Point := ⟨fun a b => a.x == b.x && a.y == b.y⟩

/-- Rust `Hash`: `x.to_bits()`, `y.to_bits()`. -/
instance : Hashable Point := ⟨fun p => mixHash (hash p.x.toBits) (hash p.y.toBits)⟩

instance : ToString Point := ⟨fun p => s!"({Float.toRustDisplay p.x},{Float.toRustDisplay p.y})"⟩

end Point

end Elk.Alg.Common
