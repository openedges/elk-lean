import Tests.Framework
/-! Test suites for `org.eclipse.elk.core.math`: ports of the elk-rs tests
`elk_math_test`, `bezier_spline_test`, `cubic_spline_interpolator_test`,
`kvector_test` and `kvector_chain_test`. -/
namespace Tests.Core.Math

open Tests Elk.Core.Util Elk.Core.Math

private def kv (x y : Float) : KVector := ⟨x, y⟩

private def isErr {α : Type} (r : Except String α) : Bool :=
  match r with
  | .error _ => true
  | .ok _ => false

private def okD {α : Type} [Inhabited α] (r : Except String α) : α :=
  match r with
  | .ok v => v
  | .error _ => default

private def mkChain (pts : List (Float × Float)) : KVectorChain :=
  (pts.map fun p => kv p.1 p.2).toArray

private def rect : ElkRectangle := ElkRectangle.ofValues 23.0 14.0 20.0 20.0

private def basePath : KVectorChain :=
  mkChain [(24.0, 15.0), (27.0, 20.0), (39.0, 30.0), (29.0, 19.0)]

def elkMathContains : Suite := suite "core.math.ElkMath.contains" do
  checkEq "point contained" (ElkMath.containsRectPoint rect (kv 26.0 19.0)) true
  checkEq "point not contained" (ElkMath.containsRectPoint rect (kv 10.0 9.0)) false
  checkEq "point on border" (ElkMath.containsRectPoint rect (kv 23.0 20.0)) false
  checkEq "point on corner" (ElkMath.containsRectPoint rect (kv 23.0 14.0)) false
  checkEq "line contained" (ElkMath.containsRectLine rect (kv 24.0 20.0) (kv 40.0 32.0)) true
  checkEq "line not contained" (ElkMath.containsRectLine rect (kv 10.0 10.0) (kv 40.0 32.0)) false
  checkEq "path contained" (ElkMath.containsRectPath rect basePath) true
  checkEq "path with corner not contained"
    (ElkMath.containsRectPath rect (basePath.push (kv 23.0 14.0))) false
  checkEq "path with outside point not contained"
    (ElkMath.containsRectPath rect (basePath.push (kv 10.0 10.0))) false
  checkEq "short path not contained" (ElkMath.containsRectPath rect #[kv 24.0 15.0]) false

def elkMathIntersects : Suite := suite "core.math.ElkMath.intersects" do
  let l11 := kv 10.0 10.0
  let l12 := kv 20.0 20.0
  checkEq "crossing lines" (ElkMath.intersectsLines l11 l12 (kv 11.0 21.0) (kv 21.0 11.0)) true
  checkEq "touching at end" (ElkMath.intersectsLines l11 l12 (kv 10.0 10.0) (kv 15.0 10.0)) false
  checkEq "far away" (ElkMath.intersectsLines l11 l12 (kv 1.0 2.0) (kv 2.0 1.0)) false
  checkEq "identical" (ElkMath.intersectsLines l11 l12 l11 l12) false
  checkEq "reversed" (ElkMath.intersectsLines l11 l12 l12 l11) false
  checkEq "no crossing" (ElkMath.intersectsLines l11 l12 (kv 11.0 1.0) (kv 21.0 21.0)) false
  checkEq "path inside does not intersect" (ElkMath.intersectsRectPath rect basePath) false
  checkEq "path with corner does not intersect"
    (ElkMath.intersectsRectPath rect (basePath.push (kv 23.0 14.0))) false
  checkEq "path leaving intersects"
    (ElkMath.intersectsRectPath rect (basePath.push (kv 10.0 10.0))) true
  checkEq "rect line crossing" (ElkMath.intersectsRectLine rect (kv 30.0 20.0) (kv 50.0 20.0)) true
  checkEq "rect line inside" (ElkMath.intersectsRectLine rect (kv 30.0 20.0) (kv 35.0 25.0)) false
  checkEq "short path" (ElkMath.intersectsRectPath rect #[kv 24.0 15.0]) false

def elkMathFactorial : Suite := suite "core.math.ElkMath.factorial" do
  checkEq "factl 0" (okD (ElkMath.factl 0)) 1
  checkEq "factl 1" (okD (ElkMath.factl 1)) 1
  checkEq "factl 20" (okD (ElkMath.factl 20)) 2432902008176640000
  check "factl -50 fails" (isErr (ElkMath.factl (-50)))
  check "factl 21 fails" (isErr (ElkMath.factl 21))
  checkFloat "factd 0" (okD (ElkMath.factd 0)) 1.0
  checkFloat "factd 1" (okD (ElkMath.factd 1)) 1.0
  checkFloat "factd 5" (okD (ElkMath.factd 5)) 120.0
  check "factd -1 fails" (isErr (ElkMath.factd (-1)))
  -- Stirling approximation for x > 20 (22! = 1.1240007e21)
  let f22 := okD (ElkMath.factd 22)
  check "factd 22 approx" ((f22 / 1.1240007277776077e21 - 1.0).abs < 0.01)
  checkEq "binomiall 2 0" (okD (ElkMath.binomiall 2 0)) 1
  checkEq "binomiall 20 20" (okD (ElkMath.binomiall 20 20)) 1
  checkEq "binomiall 2 1" (okD (ElkMath.binomiall 2 1)) 2
  checkEq "binomiall 10 3" (okD (ElkMath.binomiall 10 3)) 120
  checkEq "binomiall 22 2" (okD (ElkMath.binomiall 22 2)) 231
  check "binomiall -1 1 fails" (isErr (ElkMath.binomiall (-1) 1))
  check "binomiall 1 2 fails" (isErr (ElkMath.binomiall 1 2))
  checkFloat "binomiald 2 0" (okD (ElkMath.binomiald 2 0)) 1.0
  checkFloat "binomiald 20 20" (okD (ElkMath.binomiald 20 20)) 1.0
  checkFloat "binomiald 2 1" (okD (ElkMath.binomiald 2 1)) 2.0
  check "binomiald -1 1 fails" (isErr (ElkMath.binomiald (-1) 1))

def elkMathPow : Suite := suite "core.math.ElkMath.pow" do
  checkFloat "powd 0" (ElkMath.powd 10.0 0) 1.0
  checkFloat "powf 0" (ElkMath.powf 10.0 0) 1.0 1e-6
  checkFloat "powd 2" (ElkMath.powd 10.0 2) 100.0
  checkFloat "powf 2" (ElkMath.powf 10.0 2) 100.0 1e-6
  checkFloat "powd -2" (ElkMath.powd 10.0 (-2)) 0.01
  checkFloat "powd 3" (ElkMath.powd 2.0 10) 1024.0
  checkFloat "powf -1 rounds to f32" (ElkMath.powf 3.0 (-1)) (Float.toF32 (1.0 / 3.0)) 1e-12

def elkMathBezier : Suite := suite "core.math.ElkMath.bezier" do
  let p1 := kv 10.0 10.0
  let p2 := kv 20.0 20.0
  let p3 := kv 30.0 30.0
  let p4 := kv 50.0 50.0
  let result := ElkMath.approximateBezierSegment 20 #[p1, p2, p3, p4]
  checkEq "segment size" result.size 20
  checkFloat "segment last x" result.back!.x p4.x
  checkFloat "segment last y" result.back!.y p4.y
  let h1 := kv 50.0 10.0
  let h2 := kv 70.0 10.0
  let h3 := kv 80.0 10.0
  let h4 := kv 100.0 10.0
  let result2 := ElkMath.approximateBezierSegment 20 #[h1, h2, h3, h4]
  check "horizontal segment constant y" (result2.all fun k => (k.y - 10.0).abs < 1e-9)
  check "empty result size" ((ElkMath.approximateBezierSegment 0 #[p1]).isEmpty)
  checkEq "default segment size" (ElkMath.approximateBezierSegmentDefault #[p1, p2, p3]).size 4
  -- spline
  let spline := ElkMath.approximateBezierSpline result
  checkFloat "spline last x" spline.back!.x p4.x
  checkFloat "spline last y" spline.back!.y p4.y
  let spline2 := ElkMath.approximateBezierSpline result2
  check "horizontal spline constant y" (spline2.all fun k => (k.y - 10.0).abs < 1e-9)
  check "empty spline" (ElkMath.approximateBezierSpline #[]).isEmpty
  -- point on segment
  let mid := ElkMath.getPointOnBezierSegment 0.5 #[kv 0.0 0.0, kv 10.0 0.0, kv 20.0 0.0]
  checkFloat "point on segment x" mid.x 10.0
  checkFloat "point on segment y" mid.y 0.0
  -- distance
  checkFloat "distance end" (ElkMath.distanceFromBezierSegment p1 p2 p3 p4 p4) 0.0 0.01
  checkFloat "distance c2" (ElkMath.distanceFromBezierSegment p1 p2 p3 p4 p3) 0.0 0.01
  checkFloat "distance c1" (ElkMath.distanceFromBezierSegment p1 p2 p3 p4 p2) 0.0 0.01
  checkFloat "distance start" (ElkMath.distanceFromBezierSegment p1 p2 p3 p4 p1) 0.0 0.01

def elkMathAggregates : Suite := suite "core.math.ElkMath.aggregates" do
  checkEq "maxi" (ElkMath.maxi #[1, 7, 5, 6]) 7
  checkFloat "maxf" (ElkMath.maxf #[1.0, 7.0, 5.0, 6.0]) 7.0 1e-6
  checkFloat "maxd" (ElkMath.maxd #[1.0, 7.0, 5.0, 6.0]) 7.0
  checkEq "mini 1" (ElkMath.mini #[1, 7, 5, 6]) 1
  checkEq "mini 0" (ElkMath.mini #[8, 1, 9, 0]) 0
  checkEq "mini 8" (ElkMath.mini #[8, 8, 8, 8]) 8
  checkFloat "minf 1" (ElkMath.minf #[1.0, 7.0, 5.0, 6.0]) 1.0 1e-6
  checkFloat "minf 0" (ElkMath.minf #[8.0, 1.0, 9.0, 0.0]) 0.0 1e-6
  checkFloat "minf 8" (ElkMath.minf #[8.0, 8.0, 8.0, 8.0]) 8.0 1e-6
  checkFloat "mind 1" (ElkMath.mind #[1.0, 7.0, 5.0, 6.0]) 1.0
  checkFloat "mind 0" (ElkMath.mind #[8.0, 1.0, 9.0, 0.0]) 0.0
  checkFloat "mind 8" (ElkMath.mind #[8.0, 8.0, 8.0, 8.0]) 8.0
  checkEq "averagel 4" (ElkMath.averagel #[5, 8, 2, 1]) 4
  checkEq "averagel 2" (ElkMath.averagel #[5, 0, 2, 1]) 2
  checkEq "averagei 4" (ElkMath.averagei #[5, 8, 2, 1]) 4
  checkFloat "averagef 4" (ElkMath.averagef #[5.0, 8.0, 2.0, 1.0]) 4.0 1e-6
  checkFloat "averagef 2" (ElkMath.averagef #[5.0, 0.0, 2.0, 1.0]) 2.0 1e-6
  checkFloat "averaged 4" (ElkMath.averaged #[5.0, 8.0, 2.0, 1.0]) 4.0
  checkFloat "averaged 2" (ElkMath.averaged #[5.0, 0.0, 2.0, 1.0]) 2.0
  checkEq "maxl" (ElkMath.maxl #[3, 9, 1]) 9
  checkEq "minl" (ElkMath.minl #[3, 9, 1]) 1
  checkEq "boundi low" (ElkMath.boundi 1 3 5) 3
  checkEq "boundi high" (ElkMath.boundi 9 3 5) 5
  checkEq "boundi mid" (ElkMath.boundi 4 3 5) 4
  checkFloat "boundd low" (ElkMath.boundd 1.0 3.0 5.0) 3.0
  checkFloat "boundd high" (ElkMath.boundd 9.0 3.0 5.0) 5.0
  checkEq "signum neg" (ElkMath.signum (-2.5)) (-1)
  checkEq "signum pos" (ElkMath.signum 2.5) 1
  checkEq "signum zero" (ElkMath.signum 0.0) 0

def elkMathGeometry : Suite := suite "core.math.ElkMath.geometry" do
  let c := ElkMath.clipVector (kv 10.0 2.0) 4.0 4.0
  checkFloat "clipVector x" c.x 2.0
  checkFloat "clipVector y" c.y 0.4
  let c2 := ElkMath.clipVector (kv 1.0 1.0) 4.0 4.0
  checkFloat "clipVector unchanged x" c2.x 1.0
  let r1 := ElkRectangle.ofValues 0.0 0.0 10.0 10.0
  let r2 := ElkRectangle.ofValues 20.0 0.0 10.0 10.0
  checkFloat "shortestDistance horizontal" (ElkMath.shortestDistance r1 r2) 10.0
  let r3 := ElkRectangle.ofValues 20.0 20.0 10.0 10.0
  checkFloat "shortestDistance diagonal" (ElkMath.shortestDistance r1 r3) (Float.sqrt 200.0)
  let r4 := ElkRectangle.ofValues 5.0 5.0 10.0 10.0
  checkFloat "shortestDistance overlap" (ElkMath.shortestDistance r1 r4) (-(Float.sqrt 50.0))
  checkEq "intersects2 crossing"
    (ElkMath.intersects2 (kv 0.0 0.0) (kv 10.0 10.0) (kv 0.0 10.0) (kv 10.0 (-10.0)) |>.map (·.x))
    (some 5.0)
  check "intersects2 parallel" (ElkMath.intersects2 (kv 0.0 0.0) (kv 10.0 0.0) (kv 0.0 5.0) (kv 10.0 0.0)).isNone
  checkFloat "traceRays" (ElkMath.traceRays (kv 0.0 0.0) (kv 10.0 0.0) (kv 2.0 5.0) (kv 8.0 5.0) (kv 0.0 (-10.0))) 5.0
  checkFloat "distance" (ElkMath.distance (kv 0.0 0.0) (kv 10.0 0.0) (kv 2.0 5.0) (kv 8.0 5.0) (kv 0.0 (-10.0))) 5.0
  checkEq "fuzzyCompare lt" (ElkMath.fuzzyCompare 0.0 1.0 0.1) (-1)
  checkEq "fuzzyCompare eq" (ElkMath.fuzzyCompare 1.0 1.05 0.1) 0
  check "fuzzyEquals" (ElkMath.fuzzyEquals 1.0 1.05 0.1)

private def vertical : BezierSpline :=
  BezierSpline.empty.addCurvePoints (kv 50.0 0.0) (kv 50.0 20.0) (kv 50.0 40.0) (kv 50.0 50.0)

private def horizontal : BezierSpline :=
  BezierSpline.empty.addCurvePoints (kv 0.0 50.0) (kv 10.0 50.0) (kv 20.0 50.0) (kv 30.0 50.0)

def bezierSplineSuite : Suite := suite "core.math.BezierSpline" do
  checkFloat "vertical start x" vertical.startPoint.x 50.0
  checkFloat "vertical start y" vertical.startPoint.y 0.0
  checkFloat "horizontal start y" horizontal.startPoint.y 50.0
  checkFloat "horizontal start x" horizontal.startPoint.x 0.0
  checkFloat "vertical end x" vertical.endPoint.x 50.0
  checkFloat "vertical end y" vertical.endPoint.y 50.0
  checkFloat "horizontal end x" horizontal.endPoint.x 30.0
  checkFloat "horizontal end y" horizontal.endPoint.y 50.0
  check "vertical inner x" (vertical.innerPoints.all fun v => (50.0 - v.x).abs < 1e-8)
  check "horizontal inner y" (horizontal.innerPoints.all fun v => (50.0 - v.y).abs < 1e-8)
  checkEq "inner count" vertical.innerPoints.size 2
  check "vertical base x" (vertical.basePoints.all fun v => (50.0 - v.x).abs < 1e-8)
  check "horizontal base y" (horizontal.basePoints.all fun v => (50.0 - v.y).abs < 1e-8)
  checkEq "base count" horizontal.basePoints.size 2
  check "vertical polyline x" ((vertical.polylineApprx 50).all fun v => (50.0 - v.x).abs < 1e-8)
  check "horizontal polyline y" ((horizontal.polylineApprx 50).all fun v => (50.0 - v.y).abs < 1e-8)
  checkEq "polyline count" (horizontal.polylineApprx 50).size 51
  let two := horizontal.addSpline vertical true
  checkEq "addSpline curves" two.curves.size 2
  checkFloat "addSpline beginning start" two.startPoint.x 50.0
  checkFloat "addSpline end" (horizontal.addSpline vertical false).endPoint.y 50.0
  checkEq "inner count two curves" two.innerPoints.size 5
  check "empty inner" (BezierSpline.empty.innerPoints.isEmpty)
  check "empty polyline" ((BezierSpline.empty.polylineApprx 10).isEmpty)

def cubicSplineSuite : Suite := suite "core.math.CubicSplineInterpolator" do
  let v0 := kv 5.0 50.0
  let spline := CubicSplineInterpolator.calculateClosedBezierSpline
    #[v0, kv 10.0 70.0, kv 30.0 100.0, kv 60.0 70.0, kv 70.0 40.0]
  checkEq "closed end equals start" spline.endPoint v0
  checkEq "closed curve count" spline.curves.size 5
  let sh := CubicSplineInterpolator.calculateClosedBezierSpline
    #[kv 5.0 50.0, kv 10.0 50.0, kv 30.0 50.0, kv 60.0 50.0, kv 70.0 50.0]
  checkFloat "horizontal start y" sh.startPoint.y 50.0
  checkFloat "horizontal end y" sh.endPoint.y 50.0
  check "horizontal inner y" (sh.innerPoints.all fun v => (v.y - 50.0).abs < 1e-9)
  let sv := CubicSplineInterpolator.calculateClosedBezierSpline
    #[kv 100.0 10.0, kv 100.0 50.0, kv 100.0 100.0, kv 100.0 120.0, kv 100.0 200.0]
  checkFloat "vertical start x" sv.startPoint.x 100.0
  checkFloat "vertical end x" sv.endPoint.x 100.0
  check "vertical inner x" (sv.innerPoints.all fun v => (v.x - 100.0).abs < 1e-9)
  -- open splines via the ISplineInterpolator structure
  let pts := #[kv 0.0 0.0, kv 10.0 0.0, kv 20.0 0.0, kv 30.0 0.0]
  let open_ := CubicSplineInterpolator.interpolator.interpolatePoints pts
  checkEq "open curve count" open_.curves.size 3
  checkFloat "open end x" open_.endPoint.x 30.0
  check "open collinear y" (open_.innerPoints.all fun v => v.y.abs < 1e-9)
  let tang := CubicSplineInterpolator.interpolator.interpolatePointsWithTangents pts
    (kv 1.0 0.0) (kv 1.0 0.0) true
  checkEq "tangent curve count" tang.curves.size 3
  check "empty closed" (CubicSplineInterpolator.calculateClosedBezierSpline #[]).curves.isEmpty
  check "single open" (CubicSplineInterpolator.interpolator.interpolatePoints #[v0]).curves.isEmpty
  checkEq "two points open" (CubicSplineInterpolator.interpolator.interpolatePoints #[v0, kv 15.0 50.0]).curves.size 1

def kvectorSuite : Suite := suite "core.math.KVector" do
  checkEq "equals" (kv 10.0 10.0) (kv 10.0 10.0)
  let k1 := kv 12.0 70.0
  let k2 := kv 15.0 17.0
  checkEq "add and sub" ((k1.add k2).sub k2) k1
  let a := (k1.add k1).add k1
  checkEq "scale" a (k1.scale 3.0)
  checkEq "translate" ((kv 10.0 30.0).addValues 40.0 20.0) (kv 50.0 50.0)
  checkEq "normalize x" (kv 2.0 0.0).normalize (kv 1.0 0.0)
  checkEq "normalize y" (kv 0.0 2.0).normalize (kv 0.0 1.0)
  checkFloat "degrees 0" (kv 10.0 0.0).toDegrees 0.0 0.00001
  checkFloat "degrees 45" (kv 10.0 10.0).toDegrees 45.0 0.00001
  checkFloat "degrees 90" (kv 0.0 10.0).toDegrees 90.0 0.00001
  checkFloat "degrees 135" (kv (-10.0) 10.0).toDegrees 135.0 0.00001
  checkFloat "degrees 180" (kv (-10.0) 0.0).toDegrees 180.0 0.00001
  checkFloat "degrees 225" (kv (-10.0) (-10.0)).toDegrees 225.0 0.00001
  checkFloat "degrees 270" (kv 0.0 (-10.0)).toDegrees 270.0 0.00001
  checkFloat "degrees 315" (kv 10.0 (-10.0)).toDegrees 315.0 0.00001
  checkEq "distance zero" ((kv 5.0 50.0).distance (kv 5.0 50.0)) 0.0
  checkEq "distance 30" ((kv 0.0 20.0).distance (kv 0.0 50.0)) 30.0
  let expected := kv 5.0 50.0
  for s in ["(5,50)", "{5,50}", "[5,50]", "{(5,50)}", "[(5,50)]", "[{5,50}]"] do
    match KVector.parse s with
    | .ok v => checkEq s!"parse {s}" v expected
    | .error e => check s!"parse {s}: {e}" false
  checkEq "bound inside" ((kv 30.0 30.0).bound 10.0 10.0 40.0 40.0) (kv 30.0 30.0)
  checkEq "bound clamps" ((kv 30.0 30.0).bound 40.0 40.0 60.0 60.0) (kv 40.0 40.0)

def kvectorChainSuite : Suite := suite "core.math.KVectorChain" do
  let v0 := kv 5.0 50.0
  let v1 := kv 10.0 50.0
  let v2 := kv 30.0 50.0
  match KVectorChain.parse "{(5,50),(10,50),(30,50)}" with
  | .ok kvc =>
    checkEq "parse v0" kvc[0]! v0
    checkEq "parse v1" kvc[1]! v1
    checkEq "parse v2" kvc[2]! v2
  | .error e => check s!"parse: {e}" false
  match KVectorChain.parse "{(5,50),(10,50),(30,)}" with
  | .ok kvc =>
    checkEq "partial v0" kvc[0]! v0
    checkEq "partial v1" kvc[1]! v1
    checkEq "partial size" kvc.size 2
  | .error e => check s!"parse partial: {e}" false
  match KVectorChain.parse "{(5; 50 ], [10 , 50 ),(30,,,) }" with
  | .ok kvc =>
    checkEq "mixed v0" kvc[0]! v0
    checkEq "mixed v1" kvc[1]! v1
    checkEq "mixed size" kvc.size 2
  | .error e => check s!"parse mixed: {e}" false
  match KVectorChain.parse "{(5,a),(10,50),(30,50)}" with
  | .ok _ => check "illegal argument" false
  | .error e => check "illegal argument message" ((e.splitOn "expected format").length > 1)
  match KVectorChain.parse "{(10,50),(10,50),(10,50)}" with
  | .ok kvc => checkEq "length zero" kvc.totalLength 0.0
  | .error e => check s!"parse length: {e}" false
  match KVectorChain.parse "{(10,0),(10,20),(10,30)}" with
  | .ok kvc => checkEq "length 30" kvc.totalLength 30.0
  | .error e => check s!"parse length2: {e}" false
  let kvc := KVectorChain.ofArray #[v0, v1, v2]
  checkEq "pointOnLine 0" (kvc.pointOnLine 0.0) v0
  checkEq "pointOnLine 5" (kvc.pointOnLine 5.0) v1
  checkEq "pointOnLine 40" (kvc.pointOnLine 40.0) v2

def suites : Array Tests.Suite :=
  #[elkMathContains, elkMathIntersects, elkMathFactorial, elkMathPow, elkMathBezier,
    elkMathAggregates, elkMathGeometry, bezierSplineSuite, cubicSplineSuite,
    kvectorSuite, kvectorChainSuite]

end Tests.Core.Math
