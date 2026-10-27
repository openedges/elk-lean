import Elk.Alg.Common.Geometry.TTriangle
/-!
# `org.eclipse.elk.alg.common.BowyerWatsonTriangulation`

Creates a Delaunay triangulation for the given points, represented by a list of
edges (elk-rs `bowyer_watson_triangulation.rs`). The approach was devised
independently by Bowyer, Adrian (1981) "Computing Dirichlet tessellations" and
Watson, David F. (1981) "Computing the n-dimensional Delaunay tessellation with
application to Voronoi polytopes".

Precondition: all vertices have to be distinct. Postcondition: the returned
edges form a connected graph that includes all input points without duplicate
edges.

## Collections and order
Rust keeps the triangulation in a `HashSet<TTriangle>` and returns a
`HashSet<TEdge>`, both with std `RandomState` (iteration order random per
process). The *set* of triangles and the *set* of returned edges do not depend
on that order (invalid triangles, boundary edges and new triangles are all
defined set-wise), only the iteration order does. The Lean port uses
insertion-ordered, duplicate-free arrays:
* triangulation: the super triangle, then new triangles appended in boundary
  order; removal keeps the order of the remaining triangles;
* result: the edges of the triangles in triangulation order, each triangle
  contributing `(a,b)`, `(b,c)`, `(c,a)`, first occurrence kept, then the edges
  touching the super triangle removed (order preserving `retain`).
Duplicate detection reproduces the Rust hash identity (`TTriangle.sameSetKey`,
`TEdge.sameSetKey`). SVG debug output is not ported (TODO(debug), see
`Elk.Alg.Common.Utils.SVGImage`).
-/
namespace Elk.Alg.Common

open Elk.Core.Util Elk.Core.Math

namespace BowyerWatsonTriangulation

/-- `HashSet<TTriangle>::insert` on an insertion-ordered array. -/
private def insertTriangle (ts : Array TTriangle) (t : TTriangle) : Array TTriangle :=
  if ts.any (TTriangle.sameSetKey · t) then ts else ts.push t

/-- `HashSet<TTriangle>::remove` on an insertion-ordered array. -/
private def removeTriangle (ts : Array TTriangle) (t : TTriangle) : Array TTriangle :=
  match ts.findIdx? (TTriangle.sameSetKey · t) with
  | some i => ts.eraseIdxIfInBounds i
  | none => ts

/-- `BowyerWatsonTriangulation.triangulate(vertices, debugOutputFile)`. The debug output
file is ignored (TODO(debug)). The result is duplicate free; see the module doc for the
order. -/
def triangulate (vertices : Array KVector) (_debugOutputFile : Option String := none) :
    Array TEdge := Id.run do
  let mut topleft : KVector := ⟨Float.posInf, Float.posInf⟩
  let mut bottomright : KVector := ⟨Float.negInf, Float.negInf⟩
  for v in vertices do
    topleft := ⟨fmin topleft.x v.x, fmin topleft.y v.y⟩
    bottomright := ⟨fmax bottomright.x v.x, fmax bottomright.y v.y⟩
  let size : KVector := ⟨bottomright.x - topleft.x, bottomright.y - topleft.y⟩
  let wiggleroom := 50.0
  let sa : KVector := ⟨topleft.x - wiggleroom, topleft.y - size.x - wiggleroom⟩
  let sb : KVector := ⟨topleft.x - wiggleroom, bottomright.y + size.x + wiggleroom⟩
  let sc : KVector := ⟨bottomright.x + size.y / 2.0 + wiggleroom, topleft.y + size.y / 2.0⟩
  let superTriangle := TTriangle.new sa sb sc

  let mut triangulation : Array TTriangle := #[superTriangle]
  for vertex in vertices do
    let invalidTriangles := triangulation.filter (·.inCircumcircle vertex)
    let mut boundary : Array TEdge := #[]
    for triangle in invalidTriangles do
      for edge in triangle.tEdges do
        let mut onBoundary := true
        for other in invalidTriangles do
          if !(other == triangle) && other.containsEdge edge then
            onBoundary := false
            break
        if onBoundary then
          boundary := boundary.push edge
    for triangle in invalidTriangles do
      triangulation := removeTriangle triangulation triangle
    for edge in boundary do
      triangulation := insertTriangle triangulation (TTriangle.new vertex edge.u edge.v)

  let mut tEdges : Array TEdge := #[]
  for triangle in triangulation do
    for edge in triangle.tEdges do
      tEdges := TEdge.insertUnique tEdges edge
  return tEdges.filter fun edge =>
    !superTriangle.containsVertex edge.u && !superTriangle.containsVertex edge.v

/-- `triangulate(vertices)` without debug output. -/
@[inline] def triangulateWithoutDebug (vertices : Array KVector) : Array TEdge :=
  triangulate vertices none

end BowyerWatsonTriangulation

end Elk.Alg.Common
