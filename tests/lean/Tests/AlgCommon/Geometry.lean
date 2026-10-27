import Tests.Framework
import Elk.Alg.Common.Geometry
import Elk.Alg.Common.Utils
/-! Tests of `org.eclipse.elk.alg.common` (Geometry): the elk-rs test
`rectilinear_convex_hull_test.rs` (`test_cross`, `test_little_robot`) plus checks of
`Point`/`Quadrant`, `TEdge`, `TTriangle`, `Tree`, `BowyerWatsonTriangulation`,
`NaiveMinST`, `RectangleStripOverlapRemover` and `utils`. -/
namespace Tests.AlgCommon.Geometry

open Tests Elk Elk.Core.Util Elk.Core.Math Elk.Alg.Common Elk.Alg.Common.Overlaps
  Elk.Alg.Common.Utils

private def p (x y : Float) : Point := Point.new x y
private def kv (x y : Float) : KVector := ⟨x, y⟩
private def rect (x y w h : Float) : ElkRectangle := ElkRectangle.ofValues x y w h

/-- elk-rs `rectilinear_convex_hull_test.rs`. -/
def rectilinearConvexHull : Suite := suite "alg.common.RectilinearConvexHull" do
  -- test_cross
  let points := #[p 0 1, p 1 1, p 1 0, p 2 0, p 2 1, p 3 1, p 3 2, p 2 2, p 2 3, p 1 3, p 1 2, p 0 2]
  let hull := RectilinearConvexHull.of points
  checkEq "test_cross hull" hull.getHull points
  checkEq "test_cross rects" hull.splitIntoRectangles
    #[rect 0 1 1 1, rect 1 0 1 3, rect 2 1 1 1]
  -- test_little_robot
  let points := #[p 0 2, p 1 2, p 1 1, p 2 1, p 2 0, p 2 0, p 2 1, p 3 1, p 3 2, p 4 2,
    p 4 2, p 3 2, p 3 3, p 2 3, p 2 4, p 2 4, p 2 3, p 1 3, p 1 2, p 0 2]
  let hull := RectilinearConvexHull.of points
  checkEq "test_little_robot hull" hull.getHull points
  checkEq "test_little_robot rects" hull.splitIntoRectangles
    #[rect 0 2 1 0, rect 1 1 1 2, rect 2 0 0 4, rect 2 1 1 2, rect 3 2 1 0]
  -- own: quadrants and convexity of the computed hull points
  let hull := RectilinearConvexHull.of #[p 0 0, p 2 0, p 2 2, p 0 2]
  -- a square's rectilinear hull is its 4 corners (one maximal element per quadrant)
  checkEq "square hull" hull.getHull #[p 0 0, p 2 0, p 2 2, p 0 2]
  checkEq "square hull quadrants" (hull.getHull.map (ElkEnum.javaName ·.quadrant))
    #["Q1", "Q2", "Q3", "Q4"]
  checkEq "square concave corners" (hull.getHull.filter (!·.convex)).size 0
  -- an L shape gets one concave corner
  let lHull := RectilinearConvexHull.of #[p 0 0, p 1 0, p 1 1, p 2 1, p 2 2, p 0 2]
  checkEq "L concave corners" (lHull.getHull.filter (!·.convex)).size 1
  check "L concave corner position" (lHull.getHull.any fun q => !q.convex && q.x == 1 && q.y == 1)
  checkEq "square rects" hull.splitIntoRectangles #[rect 0 0 2 2]

def pointQuadrant : Suite := suite "alg.common.Point" do
  checkEq "quadrant declaration order" ((ElkEnum.values : Array Quadrant).map ElkEnum.javaName)
    #["Q1", "Q4", "Q2", "Q3"]
  check "quadrant cmp Q4 < Q2" (Quadrant.cmp .q4 .q2 == .lt && Quadrant.cmp .q3 .q1 == .gt)
  checkEq "isUpper" ((ElkEnum.values : Array Quadrant).map Quadrant.isUpper) #[true, false, true, false]
  checkEq "isLeft" ((ElkEnum.values : Array Quadrant).map Quadrant.isLeft) #[true, true, false, false]
  check "isBothLeftOrBothRight" (Quadrant.isBothLeftOrBothRight .q1 .q4
    && Quadrant.isBothLeftOrBothRight .q2 .q3 && !Quadrant.isBothLeftOrBothRight .q1 .q2
    && !Quadrant.isBothLeftOrBothRight .q1 .q1)
  check "isOneLeftOneRight" (Quadrant.isOneLeftOneRight .q1 .q2 && Quadrant.isOneLeftOneRight .q4 .q2
    && !Quadrant.isOneLeftOneRight .q2 .q1 && !Quadrant.isOneLeftOneRight .q1 .q4)
  check "point equality ignores quadrant/convex"
    (Point.withQuadrant 1 2 .q3 == { p 1 2 with convex := false })
  check "point hash ignores quadrant" (hash (Point.withQuadrant 1 2 .q3) == hash (p 1 2))
  check "point inequality" (!(p 1 2 == p 2 1))
  let pk := Point.ofKVector (kv 3 4)
  check "point from kvector" (pk.x == 3 && pk.y == 4 && pk.quadrant == .q1 && pk.convex)

def tEdgeTriangle : Suite := suite "alg.common.TEdge/TTriangle" do
  let e := TEdge.new (kv 0 0) (kv 1 2)
  let r := TEdge.new (kv 1 2) (kv 0 0)
  check "edge equality is unordered" (e == r)
  check "edge hash is unordered" (hash e == hash r)
  check "edge inequality" (!(e == TEdge.new (kv 0 0) (kv 1 3)))
  check "edge set key" (TEdge.sameSetKey e r && (TEdge.insertUnique #[e] r).size == 1)
  let t := TTriangle.new (kv 0 0) (kv 2 0) (kv 0 2)
  checkFloat "circumcenter x" t.getCircumcenter.x 1.0
  checkFloat "circumcenter y" t.getCircumcenter.y 1.0
  check "inCircumcircle inside" (t.inCircumcircle (kv 0.5 0.5))
  check "inCircumcircle on circle is outside (fuzzy)" (!t.inCircumcircle (kv 2 2))
  check "inCircumcircle near circle is outside (fuzzy)" (!t.inCircumcircle (kv 2.00005 2))
  check "inCircumcircle outside" (!t.inCircumcircle (kv 3 3))
  check "containsEdge reversed" (t.containsEdge (TEdge.new (kv 0 2) (kv 2 0)))
  check "containsVertex" (t.containsVertex (kv 2 0) && !t.containsVertex (kv 2 2))
  let t2 := TTriangle.new (kv 2 0) (kv 0 2) (kv 0 0)
  check "triangle equality is order independent" (t == t2)
  check "triangle set key is order dependent" (!TTriangle.sameSetKey t t2 && TTriangle.sameSetKey t t)

private def hasEdge (es : Array TEdge) (a b : KVector) : Bool := es.any (· == TEdge.new a b)

private def duplicateFree (es : Array TEdge) : Bool := Id.run do
  for i in [0:es.size] do
    for j in [i+1:es.size] do
      if es[i]! == es[j]! then return false
  return true

def bowyerWatson : Suite := suite "alg.common.BowyerWatsonTriangulation" do
  -- rhombus: the short diagonal (0,0)-(10,0) is the Delaunay edge
  let a := kv 0 0
  let b := kv 10 0
  let c := kv 5 8
  let d := kv 5 (-8)
  let es := BowyerWatsonTriangulation.triangulateWithoutDebug #[a, b, c, d]
  checkEq "rhombus edge count" es.size 5
  check "rhombus short diagonal" (hasEdge es a b)
  check "rhombus no long diagonal" (!hasEdge es c d)
  check "rhombus sides" (hasEdge es a c && hasEdge es c b && hasEdge es b d && hasEdge es d a)
  -- square with center: 4 sides + 4 spokes
  let sq := #[kv 0 0, kv 10 0, kv 10 10, kv 0 10, kv 5 5]
  let es := BowyerWatsonTriangulation.triangulate sq
  checkEq "square+center edge count" es.size 8
  check "square+center spokes" (#[kv 0 0, kv 10 0, kv 10 10, kv 0 10].all (hasEdge es (kv 5 5)))
  check "square+center no diagonal" (!hasEdge es (kv 0 0) (kv 10 10) && !hasEdge es (kv 10 0) (kv 0 10))
  check "square+center duplicate free" (duplicateFree es)
  check "edges only between input vertices"
    (es.all fun e => sq.any (· == e.u) && sq.any (· == e.v))
  -- 6 points: a triangle with three points inside forming a smaller triangle
  let six := #[kv 0 0, kv 100 0, kv 50 90, kv 50 20, kv 35 45, kv 65 45]
  let es := BowyerWatsonTriangulation.triangulateWithoutDebug six
  -- the finite super triangle swallows the two long hull edges (0,0)-(50,90) and
  -- (100,0)-(50,90): 10 edges instead of 3n - 3 - h = 12 (same edge set as elk-rs,
  -- checked against the oracle crate)
  checkEq "six points edge count" es.size 10
  check "six points missing hull edges"
    (!hasEdge es (kv 0 0) (kv 50 90) && !hasEdge es (kv 100 0) (kv 50 90))
  check "six points inner edges"
    (hasEdge es (kv 35 45) (kv 50 90) && hasEdge es (kv 35 45) (kv 65 45)
      && hasEdge es (kv 50 20) (kv 100 0) && hasEdge es (kv 0 0) (kv 100 0))
  check "six points duplicate free" (duplicateFree es)
  checkEq "two points" (BowyerWatsonTriangulation.triangulateWithoutDebug #[kv 0 0, kv 10 0]).size 1
  checkEq "no points" (BowyerWatsonTriangulation.triangulateWithoutDebug #[]).size 0

private def lengthCost : ICostFunction := fun e => e.u.distance e.v

def naiveMinST : Suite := suite "alg.common.NaiveMinST" do
  let a := kv 0 0
  let b := kv 1 0
  let c := kv 1 1
  let d := kv 5 5
  let edges := #[TEdge.new a d, TEdge.new c d, TEdge.new a c, TEdge.new b c, TEdge.new a b]
  let tree := NaiveMinST.createSpanningTreeWithoutDebug edges a lengthCost
  checkEq "min st size" tree.size 4
  checkEq "min st preorder" tree.preorder #[a, b, c, d]
  checkEq "root has one child" tree.children.size 1
  check "chain a-b-c-d" (match tree.getAt? [0, 0, 0] with
    | some t => t.node == d && t.children.isEmpty
    | none => false)
  -- ties keep the input order: from the root, (a,c) comes before (a,b) at equal cost
  let tie := NaiveMinST.createSpanningTree #[TEdge.new a c, TEdge.new b a] a (fun _ => 1.0)
  checkEq "tie keeps input order" (tie.children.map (·.node)) #[c, b]
  -- maximum spanning tree via an inverted cost function (MaxSTPhase)
  let maxST := NaiveMinST.createSpanningTreeWithoutDebug edges a (fun e => -lengthCost e)
  checkEq "max st root children" (maxST.children.map (·.node)) #[d]
  -- Tree.addChildTo: first match in pre-order
  let t := (Tree.new 1).addChildTo 1 2 |>.1
  let t := t.addChildTo 1 3 |>.1
  let (t, ok) := t.addChildTo 3 4
  check "addChildTo found" ok
  checkEq "addChildTo preorder" t.preorder #[1, 2, 3, 4]
  checkEq "addChildTo missing parent" (t.addChildTo 9 5).2 false

def overlapRemover : Suite := suite "alg.common.overlaps.RectangleStripOverlapRemover" do
  let rects := #[rect 0 0 10 10, rect 5 0 10 10, rect 20 0 10 10, rect 8 0 4 4]
  let remover := rects.foldl RectangleStripOverlapRemover.addRectangle
    ((RectangleStripOverlapRemover.createForDirection .down).withStartCoordinate 10)
  checkEq "default gaps" (remover.horizontalGap, remover.verticalGap) (5.0, 5.0)
  let (out, strip) := remover.removeOverlaps
  checkFloat "down strip size" strip 34
  checkEq "down y" (out.map (·.y)) #[10, 25, 10, 40]
  checkEq "down x unchanged" (out.map (·.x)) #[0, 5, 20, 8]
  -- overlaps of the x-sorted nodes
  let sorted := RectangleStripOverlapRemover.computeOverlaps
    (stableSort remover.rectangleNodes fun a b => Float.compareTotal a.rectangle.x b.rectangle.x)
  checkEq "overlaps" (sorted.map (·.overlappingNodes)) #[#[1, 2], #[0, 2], #[0, 1], #[]]
  -- upward with gap 0
  let up := rects.foldl RectangleStripOverlapRemover.addRectangle
    ((RectangleStripOverlapRemover.createForDirection .up).withGap 0 0)
  let (out, strip) := up.removeOverlaps
  checkFloat "up strip size" strip 24
  checkEq "up y" (out.map (·.y)) #[-10, -20, -10, -24]
  -- rightwards: rectangles stacked vertically are spread along x
  let right := #[rect 0 0 10 10, rect 0 5 20 10].foldl RectangleStripOverlapRemover.addRectangle
    (((RectangleStripOverlapRemover.createForDirection .right).withGap 2 2).withStartCoordinate 100)
  let (out, strip) := right.removeOverlaps
  checkFloat "right strip size" strip 32
  checkEq "right x" (out.map (·.x)) #[100, 112]
  checkEq "right y unchanged" (out.map (·.y)) #[0, 5]
  -- custom strategy
  let fixed : IRectangleStripOverlapRemovalStrategy := ⟨fun _ _ ns => (ns, 7.0)⟩
  let (_, strip) := (remover.withOverlapRemovalStrategy fixed).removeOverlaps
  checkFloat "custom strategy" strip 7

def utils : Suite := suite "alg.common.utils" do
  checkFloat "overlap disjoint" (Utils.overlap (rect 0 0 10 10) (rect 20 0 10 10)) 1.0
  checkFloat "overlap identical centers" (Utils.overlap (rect 0 0 10 10) (rect 0 0 10 10)) 0.0
  -- horizontal shift 5: overlap min(|0-15|, |10-5|) = 5, center distance 5
  checkFloat "overlap horizontal" (Utils.overlap (rect 0 0 10 10) (rect 5 0 10 10)) 2.0
  checkFloat "overlap diagonal" (Utils.overlap (rect 0 0 10 10) (rect 5 2 10 10)) 2.0
  let es := Utils.getRectEdges (rect 1 2 3 4)
  checkEq "rect edges"
    (es.map fun e => (e.u.x, e.u.y, e.v.x, e.v.y))
    #[(1, 2, 4, 2), (1, 2, 1, 6), (4, 6, 4, 2), (4, 6, 1, 6)]
  checkEq "unique triple toString" (toString (UniqueTriple.new 1 "a" true)) "(1, a, true)"
  let t := UniqueTriple.new 1 2 3
  checkEq "unique triple accessors" (t.first, t.second, t.third) (1, 2, 3)
  check "svg image disabled for blank and null names"
    (!(SVGImage.new (some " ")).debug && !(SVGImage.new (some "null/x")).debug
      && (SVGImage.new (some "out")).debug && !(SVGImage.new none).debug)

def suites : Array Tests.Suite :=
  #[rectilinearConvexHull, pointQuadrant, tEdgeTriangle, bowyerWatson, naiveMinST, overlapRemover, utils]

end Tests.AlgCommon.Geometry
