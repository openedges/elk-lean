import Elk.Alg.Common.Geometry.TEdge
import Elk.Alg.Common.Spore.InternalProperties
/-!
# `org.eclipse.elk.alg.common.TTriangle`

Representation of a triangle (`TTriangle.java`, elk-rs `t_triangle.rs`).

Equality follows Java `equals`: two triangles are equal if every vertex of the other is a vertex of
this one (order independent). The Java `hashCode()` is the sum of the vertex hashes (order
independent; elk-rs hashed `a`, `b`, `c` in order, so its sets only identified triangles with the
same vertex order).
-/
namespace Elk.Alg.Common

open Elk.Core.Util Elk.Core.Math Elk.Alg.Common.Spore

/-- Rust `calculate_circumcenter(a, b, c)`. -/
def TTriangle.calculateCircumcenter (a b c : KVector) : KVector :=
  let ab := b - a
  let ac := c - a
  let bc := c - b
  let e := ab.x * (a.x + b.x) + ab.y * (a.y + b.y)
  let f := ac.x * (a.x + c.x) + ac.y * (a.y + c.y)
  let g := 2.0 * (ab.x * bc.y - ab.y * bc.x)
  let px := (ac.y * e - ab.y * f) / g
  let py := (ab.x * f - ac.x * e) / g
  ⟨px, py⟩

/-- `org.eclipse.elk.alg.common.TTriangle` (Rust `TTriangle`). Build it with `TTriangle.new`
so that the derived fields are consistent. -/
structure TTriangle where
  /-- Vertex a. -/
  a : KVector
  /-- Vertex b. -/
  b : KVector
  /-- Vertex c. -/
  c : KVector
  /-- The three edges `(a,b)`, `(b,c)`, `(c,a)`. -/
  tEdges : Array TEdge
  /-- The vertices `a`, `b`, `c`. -/
  vertices : Array KVector
  /-- The circumcenter (computed once in the constructor). -/
  circumcenter : KVector
  deriving Repr, Inhabited

namespace TTriangle

/-- `TTriangle::new(a, b, c)`. -/
def new (a b c : KVector) : TTriangle :=
  { a, b, c
    tEdges := #[TEdge.new a b, TEdge.new b c, TEdge.new c a]
    vertices := #[a, b, c]
    circumcenter := calculateCircumcenter a b c }

/-- `getCircumcenter()`. -/
@[inline] def getCircumcenter (t : TTriangle) : KVector := t.circumcenter

/-- `inCircumcircle(v)`: `v` lies strictly inside the circumcircle (fuzzy, with
`InternalProperties.FUZZINESS`). -/
def inCircumcircle (t : TTriangle) (v : KVector) : Bool :=
  InternalProperties.fuzzyCompare (t.circumcenter.distance v) (t.circumcenter.distance t.a)
    InternalProperties.FUZZINESS < 0

/-- `containsEdge(edge)` (unordered `TEdge` equality). -/
def containsEdge (t : TTriangle) (edge : TEdge) : Bool := t.tEdges.any (· == edge)

/-- `containsVertex(vertex)` (`KVector ==`). -/
def containsVertex (t : TTriangle) (vertex : KVector) : Bool := t.vertices.any (· == vertex)

/-- Java `equals`: the other triangle's vertices are all vertices of this one. -/
instance : BEq TTriangle :=
  ⟨fun s o => s.containsVertex o.a && s.containsVertex o.b && s.containsVertex o.c⟩

/-- Java `hashCode()`: `Objects.hashCode(a) + Objects.hashCode(b) + Objects.hashCode(c)`. -/
instance : JavaHashCode TTriangle where
  javaHashCode t := JavaHashCode.javaHashCode t.a + JavaHashCode.javaHashCode t.b + JavaHashCode.javaHashCode t.c
  javaSame s o := s.a.sameBits o.a && s.b.sameBits o.b && s.c.sameBits o.c

end TTriangle

end Elk.Alg.Common
