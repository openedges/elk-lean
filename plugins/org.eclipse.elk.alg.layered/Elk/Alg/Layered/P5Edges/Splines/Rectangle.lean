import Elk.Alg.Layered.P5Edges.Splines.SplinesMath
/-!
# `org.eclipse.elk.alg.layered.p5edges.splines.Rectangle`

Port of elk-rs `p5edges/splines/rectangle.rs`: a rectangle stored by its four outer coordinates
(no width/height), which makes unions and side accesses cheap. Value type: the Rust `&mut self`
methods return the updated rectangle. The Rust constructors that panic (`new` with inverted
bounds, `from_vectors`/`union_all` on empty input) return `Except` with the Java
`IllegalArgumentException` message. Java `LShape` arguments are passed as `(position, size)`.
-/
namespace Elk.Alg.Layered.P5Edges.Splines

open Elk.Core.Math Elk.Core.Options Elk.Core.Util

/-- `Rectangle`: `top`/`bottom` are the minimum/maximum y, `left`/`right` the minimum/maximum x. -/
structure Rectangle where
  top : Float
  bottom : Float
  left : Float
  right : Float
  deriving Repr, Inhabited, BEq

namespace Rectangle

/-- `Rectangle(left, top, right, bottom)`; Java/Rust reject `top > bottom` and `left > right`. -/
def new (left top right bottom : Float) : Except String Rectangle :=
  if top > bottom then .error "java.lang.IllegalArgumentException: Top must be smaller or equal to bottom."
  else if left > right then .error "java.lang.IllegalArgumentException: Left must be smaller or equal to right."
  else .ok { top := top, right := right, bottom := bottom, left := left }

/-- `Rectangle(rectangle)` (Rust `from_other`): a copy. -/
@[inline] def fromOther (rectangle : Rectangle) : Rectangle := rectangle

/-- `Rectangle(position)` (Rust `from_vector`): the degenerate rectangle at a point. -/
def fromVector (position : KVector) : Rectangle :=
  { top := position.y, bottom := position.y, right := position.x, left := position.x }

/-- `Rectangle(shape)` (Rust `from_shape`): the box spanned by `position` and `position + size`. -/
def fromShape (position size : KVector) : Rectangle :=
  let extend := position + size
  { top := fmin position.y extend.y, bottom := fmax position.y extend.y,
    left := fmin position.x extend.x, right := fmax position.x extend.x }

/-- `Rectangle(vectors)` (Rust `from_vectors`): the bounding box of the vectors, starting from
`(MAX, -MAX, MAX, -MAX)`; rejects an empty list. -/
def fromVectors (vectors : Array KVector) : Except String Rectangle := Id.run do
  if vectors.isEmpty then return .error "java.lang.IllegalArgumentException: The list of vectors may not be empty."
  let mut rect : Rectangle :=
    { top := Float.maxValue, bottom := -Float.maxValue, left := Float.maxValue, right := -Float.maxValue }
  for vector in vectors do
    rect := { rect with
      top := fmin rect.top vector.y, right := fmax rect.right vector.x,
      bottom := fmax rect.bottom vector.y, left := fmin rect.left vector.x }
  return .ok rect

/-- `union(vector)` (Rust `union_vector`). -/
def unionVector (r : Rectangle) (vector : KVector) : Rectangle :=
  { r with top := fmin r.top vector.y, right := fmax r.right vector.x,
           bottom := fmax r.bottom vector.y, left := fmin r.left vector.x }

/-- Rust `from_vectors_iter`: starts with the first vector and unions the others; rejects an
empty list. -/
def fromVectorsIter (vectors : Array KVector) : Except String Rectangle :=
  match vectors[0]? with
  | none => .error "java.lang.IllegalArgumentException: The list of vectors may not be empty."
  | some first => .ok ((vectors.extract 1 vectors.size).foldl unionVector (fromVector first))

/-- `union(shape)` (Rust `union_shape`). -/
def unionShape (r : Rectangle) (position size : KVector) : Rectangle :=
  (r.unionVector position).unionVector (position + size)

/-- `union(rectangle)` (Rust `union_rectangle`). -/
def unionRectangle (r rectangle : Rectangle) : Rectangle :=
  { r with top := fmin r.top rectangle.top, right := fmax r.right rectangle.right,
           bottom := fmax r.bottom rectangle.bottom, left := fmin r.left rectangle.left }

/-- `union(rectangle1, rectangle2)` (static). -/
def union (rect1 rect2 : Rectangle) : Rectangle := (fromOther rect1).unionRectangle rect2

/-- `union(rectangles)` (Rust `union_all`); rejects an empty list. -/
def unionAll (rectangles : Array Rectangle) : Except String Rectangle :=
  match rectangles[0]? with
  | none => .error "java.lang.IllegalArgumentException: The list of vectors may not be null."
  | some first => .ok ((rectangles.extract 1 rectangles.size).foldl unionRectangle (fromOther first))

/-- `enlarge(enlargement)`: grows every side by `enlargement`. -/
def enlarge (r : Rectangle) (enlargement : Float) : Rectangle :=
  { top := r.top - enlargement, left := r.left - enlargement,
    right := r.right + enlargement, bottom := r.bottom + enlargement }

/-- `getHeight()`. -/
@[inline] def height (r : Rectangle) : Float := r.bottom - r.top
/-- `getWidth()`. -/
@[inline] def width (r : Rectangle) : Float := r.right - r.left

/-- `getFromPortSide(side)`: the coordinate of the given side. -/
def getFromPortSide (r : Rectangle) (side : PortSide) : Float :=
  match side with
  | .north => r.top
  | .east => r.right
  | .south => r.bottom
  | .west => r.left
  | .undefined => 0.0

/-- `toNodeMargins(shape)`: the margins needed around a shape of size `size` (at the origin) to
contain this rectangle. Rust builds `Rectangle::new(0, 0, size.x, size.y)` (which would panic for a
negative size); the margins only use its bounds, so they are used directly. -/
def toNodeMargins (r : Rectangle) (size : KVector) : ElkMargin :=
  { top := fmax (0.0 - r.top) 0.0, left := fmax (0.0 - r.left) 0.0,
    bottom := fmax (r.bottom - size.y) 0.0, right := fmax (r.right - size.x) 0.0 }

/-- `toString()` (Rust `Display`): `[top= t,left= l,bottom= b,right= r]` with one decimal. -/
def toDisplayString (r : Rectangle) : String :=
  s!"[top= {SplinesMath.formatFixed1 r.top},left= {SplinesMath.formatFixed1 r.left},bottom= {SplinesMath.formatFixed1 r.bottom},right= {SplinesMath.formatFixed1 r.right}]"

instance : ToString Rectangle := ⟨toDisplayString⟩

end Rectangle

end Elk.Alg.Layered.P5Edges.Splines
