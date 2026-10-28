import Elk.Core.Util.JavaHashSet
import Elk.Alg.Common.Geometry.TTriangle
/-!
# `org.eclipse.elk.alg.common.BowyerWatsonTriangulation`

Creates a Delaunay triangulation for the given points, represented by a set of edges
(`BowyerWatsonTriangulation.java`, elk-rs `bowyer_watson_triangulation.rs`). The approach was devised
independently by Bowyer, Adrian (1981) "Computing Dirichlet tessellations" and Watson, David F.
(1981) "Computing the n-dimensional Delaunay tessellation with application to Voronoi polytopes".

Precondition: all vertices have to be distinct. Postcondition: the returned edges form a connected
graph that includes all input points without duplicate edges.

## Collections and order
Java keeps the triangulation in a `HashSet<TTriangle>` and returns a `HashSet<TEdge>`; both hash
codes are value based (sums of `KVector.hashCode()`), so the iteration orders — which decide the
order of the invalid triangles, of the boundary edges, of the new triangles and of the returned
edges, and through ties of the spanning tree costs the result of SPOrE — are a function of the input
and are reproduced with `JavaHashSet` (elk-rs used `std` hash sets with a random order; the earlier
Lean port used insertion order). `removeAll(invalidTriangles)` takes the `AbstractSet.removeAll`
branch of the sizes, the edges touching the super triangle are removed with the iterator. SVG debug
output is not ported (TODO(debug), see `Elk.Alg.Common.Utils.SVGImage`).
-/
namespace Elk.Alg.Common

open Elk.Core.Util Elk.Core.Math

namespace BowyerWatsonTriangulation

/-- `BowyerWatsonTriangulation.triangulate(vertices, debugOutputFile)`. The debug output file is
ignored (TODO(debug)). -/
def triangulate (vertices : Array KVector) (_debugOutputFile : Option String := none) :
    JavaHashSet TEdge := Id.run do
  let mut topleft : KVector := ⟨Float.posInf, Float.posInf⟩
  let mut bottomright : KVector := ⟨Float.negInf, Float.negInf⟩
  for v in vertices do
    topleft := ⟨javaMin topleft.x v.x, javaMin topleft.y v.y⟩
    bottomright := ⟨javaMax bottomright.x v.x, javaMax bottomright.y v.y⟩
  let size : KVector := ⟨bottomright.x - topleft.x, bottomright.y - topleft.y⟩
  let wiggleroom := 50.0
  let sa : KVector := ⟨topleft.x - wiggleroom, topleft.y - size.x - wiggleroom⟩
  let sb : KVector := ⟨topleft.x - wiggleroom, bottomright.y + size.x + wiggleroom⟩
  let sc : KVector := ⟨bottomright.x + size.y / 2.0 + wiggleroom, topleft.y + size.y / 2.0⟩
  let superTriangle := TTriangle.new sa sb sc

  let mut triangulation : JavaHashSet TTriangle := {}
  triangulation := (triangulation.add superTriangle).1
  for vertex in vertices do
    -- invalid triangles: the new vertex lies inside the circumcircle (set iteration order)
    let invalidTriangles := triangulation.toArray.filter (·.inCircumcircle vertex)
    -- boundary: edges not shared with another invalid triangle (`other != triangle` is identity)
    let mut boundary : Array TEdge := #[]
    for hi : i in [0:invalidTriangles.size] do
      let triangle := invalidTriangles[i]
      for edge in triangle.tEdges do
        let mut onBoundary := true
        for hj : j in [0:invalidTriangles.size] do
          if j != i && invalidTriangles[j].containsEdge edge then
            onBoundary := false
        if onBoundary then
          boundary := boundary.push edge
    triangulation := triangulation.removeAll invalidTriangles
    for edge in boundary do
      triangulation := (triangulation.add (TTriangle.new vertex edge.u edge.v)).1

  -- the edges of the triangulation (a set: shared edges once), then those touching the super
  -- triangle removed with the iterator
  let mut tEdges : JavaHashSet TEdge := {}
  for triangle in triangulation.toArray do
    tEdges := tEdges.addAll triangle.tEdges
  return tEdges.removeIf fun edge =>
    superTriangle.containsVertex edge.u || superTriangle.containsVertex edge.v

/-- `triangulate(vertices)` without debug output. -/
@[inline] def triangulateWithoutDebug (vertices : Array KVector) : JavaHashSet TEdge :=
  triangulate vertices none

end BowyerWatsonTriangulation

end Elk.Alg.Common
