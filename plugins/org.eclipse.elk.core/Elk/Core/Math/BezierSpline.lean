import Elk.Core.Math.ElkMath
/-!
# `org.eclipse.elk.core.math.BezierSpline`

A cubic Bezier spline: a sequence of Bezier curves. The Java class is mutable;
here every "add" function returns the updated spline. `BezierCurve` is the
nested class `BezierSpline.BezierCurve`.
-/
namespace Elk.Core.Math

/-- `BezierSpline.BezierCurve`: a cubic Bezier curve. -/
structure BezierCurve where
  start : KVector
  firstControl : KVector
  secondControl : KVector
  «end» : KVector
  deriving Repr, Inhabited

namespace BezierCurve

/-- `asVectorList()`. -/
def asVectorList (c : BezierCurve) : Array KVector :=
  #[c.start, c.firstControl, c.secondControl, c.«end»]

/-- `asArray()`. -/
def asArray (c : BezierCurve) : Array KVector := c.asVectorList

end BezierCurve

/-- `org.eclipse.elk.core.math.BezierSpline`. -/
structure BezierSpline where
  curves : Array BezierCurve := #[]
  deriving Repr, Inhabited

namespace BezierSpline

/-- `new BezierSpline()`. -/
def empty : BezierSpline := {}

/-- `addCurve(curve)`. -/
def addCurve (s : BezierSpline) (curve : BezierCurve) : BezierSpline :=
  { s with curves := s.curves.push curve }

/-- `addBezierSpline(spline, beginning)`: prepend or append the curves of `spline`. -/
def addSpline (s : BezierSpline) (spline : BezierSpline) (beginning : Bool) : BezierSpline :=
  if beginning then { s with curves := spline.curves ++ s.curves }
  else { s with curves := s.curves ++ spline.curves }

/-- `addCurve(start, first, second, end)`. -/
def addCurvePoints (s : BezierSpline) (start first second «end» : KVector) : BezierSpline :=
  s.addCurve ⟨start, first, second, «end»⟩

/-- `getStartPoint()` (Rust panics on an empty spline; the port returns the zero vector). -/
def startPoint (s : BezierSpline) : KVector :=
  match s.curves[0]? with
  | some c => c.start
  | none => default

/-- `getEndPoint()` (Rust panics on an empty spline; the port returns the zero vector). -/
def endPoint (s : BezierSpline) : KVector :=
  match s.curves.back? with
  | some c => c.«end»
  | none => default

/-- `getInnerPoints()`: control points and inner base points. -/
def innerPoints (s : BezierSpline) : Array KVector := Id.run do
  let mut points : Array KVector := #[]
  for idx in [0:s.curves.size] do
    let curve := s.curves[idx]!
    points := points.push curve.firstControl
    points := points.push curve.secondControl
    if idx + 1 < s.curves.size then
      points := points.push curve.«end»
  return points

/-- `getBasePoints()`: start of the first curve followed by all curve end points. -/
def basePoints (s : BezierSpline) : Array KVector := Id.run do
  match s.curves[0]? with
  | none => return #[]
  | some first =>
    let mut points : Array KVector := #[first.start]
    for curve in s.curves do
      points := points.push curve.«end»
    return points

/-- `getPolylineApprx(accuracy)`. -/
def polylineApprx (s : BezierSpline) (accuracy : Nat) : Array KVector := Id.run do
  match s.curves[0]? with
  | none => return #[]
  | some first =>
    let mut apprx : Array KVector := #[first.start]
    for curve in s.curves do
      apprx := apprx ++ ElkMath.approximateBezierSegment accuracy curve.asArray
    return apprx

instance : ToString BezierSpline :=
  ⟨fun s => s.curves.foldl (fun acc c =>
    acc ++ s!"{c.start} -> {c.firstControl} -> {c.secondControl} -> {c.«end»}\n") ""⟩

end BezierSpline

end Elk.Core.Math
