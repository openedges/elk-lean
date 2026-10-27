import Elk.Core.Math.SplineInterpolator
/-!
# `org.eclipse.elk.core.math.CubicSplineInterpolator`

Interpolates points with cubic Bezier splines (closed and open variants).
-/
namespace Elk.Core.Math

namespace CubicSplineInterpolator

/-- `INTERP_COEF_EVEN`. -/
def INTERP_COEF_EVEN : Array (Array Float) :=
  #[#[0.25, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
    #[0.2677, -0.0667, 0.0, 0.0, 0.0, 0.0, 0.0],
    #[0.2679, -0.0714, 0.0179, 0.0, 0.0, 0.0, 0.0],
    #[0.2679, -0.0718, 0.0191, -0.0048, 0.0, 0.0, 0.0],
    #[0.2679, -0.0718, 0.0192, -0.0051, 0.0013, 0.0, 0.0],
    #[0.2679, -0.0718, 0.0192, -0.0052, 0.0014, -0.0003, 0.0],
    #[0.2679, -0.0718, 0.0192, -0.0052, 0.0014, -0.0004, 0.0001]]

/-- `INTERP_COEF_ODD`. -/
def INTERP_COEF_ODD : Array (Array Float) :=
  #[#[0.3333, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
    #[0.2727, -0.0909, 0.0, 0.0, 0.0, 0.0, 0.0],
    #[0.2683, -0.0732, 0.0244, 0.0, 0.0, 0.0, 0.0],
    #[0.2680, -0.0719, 0.0196, -0.0065, 0.0, 0.0, 0.0],
    #[0.2680, -0.0718, 0.0193, -0.0053, 0.0018, 0.0, 0.0],
    #[0.2679, -0.0718, 0.0192, -0.0052, 0.0014, -0.0005, 0.0],
    #[0.2679, -0.0718, 0.0192, -0.0052, 0.0014, -0.0004, 0.0001]]

/-- `MAX_K`. -/
def MAX_K : Nat := 7
/-- `TANGENT_SCALE`. -/
def TANGENT_SCALE : Float := 0.25

/-- `calculateClosedBezierSpline(points)`. (The even/odd table selection is
kept exactly as in the Rust port.) -/
def calculateClosedBezierSpline (points : Array KVector) : BezierSpline := Id.run do
  let mut spline : BezierSpline := {}
  let n := points.size
  if n == 0 then return spline
  let even := n % 2 == 0
  let mut m := if even then (n - 2) / 2 else (n - 1) / 2
  if m > MAX_K then m := MAX_K
  let mut d : Array KVector := Array.replicate n KVector.zero
  for i in [0:n] do
    let mut dx := 0.0
    let mut dy := 0.0
    for k0 in [0:m] do
      let k := k0 + 1
      let a := if even then INTERP_COEF_ODD[m - 1]![k - 1]!
               else INTERP_COEF_EVEN[m - 1]![k - 1]!
      let pk := points[(i + k) % n]!
      let mk := points[(i + n - k) % n]!
      dx := dx + a * (pk.x - mk.x)
      dy := dy + a * (pk.y - mk.y)
    d := d.set! i ⟨dx, dy⟩
  for i in [0:n] do
    let bend1 := points[i]! + d[i]!
    let bend2 := points[(i + 1) % n]! - d[(i + 1) % n]!
    spline := spline.addCurvePoints points[i]! bend1 bend2 points[(i + 1) % n]!
  return spline

/-- `calculateOpenBezierSpline(points, startTan, endTan, tangentScale)`. -/
def calculateOpenBezierSpline (points : Array KVector) (startTan endTan : KVector)
    (tangentScale : Bool) : BezierSpline := Id.run do
  let mut spline : BezierSpline := {}
  if points.size < 2 then return spline
  let n := points.size - 1
  let mut t : Array KVector := Array.replicate (2 * n) KVector.zero
  let mut d : Array KVector := Array.replicate (n + 1) KVector.zero
  let mut startScale := 1.0
  let mut endScale := 1.0
  if tangentScale then
    if points.size == 2 then
      startScale := points[0]!.distance points[1]! * TANGENT_SCALE
      endScale := startScale
    else
      startScale := points[0]!.distance points[1]! * TANGENT_SCALE
      endScale := points[n - 1]!.distance points[n]! * TANGENT_SCALE
  d := d.set! 0 (startTan.scale startScale)
  d := d.set! n (endTan.scale endScale)
  t := t.set! 0 (points[0]! + d[0]!)
  t := t.set! n (points[n]! - d[n]!)
  for i in [1:n] do
    t := t.set! i points[i]!
    t := t.set! (2 * n - i) points[i]!
  let m := min (n - 1) MAX_K
  for i in [1:n] do
    let mut dx := 0.0
    let mut dy := 0.0
    for k0 in [0:m] do
      let k := k0 + 1
      let a := INTERP_COEF_EVEN[m - 1]![k - 1]!
      let tp := t[i + k]!
      let tm := t[Int.natAbs ((i : Int) - (k : Int))]!
      dx := dx + a * (tp.x - tm.x)
      dy := dy + a * (tp.y - tm.y)
    d := d.set! i ⟨dx, dy⟩
  for i in [0:n] do
    let bend1 := points[i]! + d[i]!
    let bend2 := points[i + 1]! - d[i + 1]!
    spline := spline.addCurvePoints points[i]! bend1 bend2 points[i + 1]!
  return spline

/-- `calculateOpenBezierSpline(points)`: tangents from the first/last segment. -/
def calculateOpenBezierSplineDefault (points : Array KVector) : BezierSpline :=
  if points.size < 2 then {}
  else
    let startVec := (points[1]! - points[0]!).normalize
    let endVec := (points[points.size - 2]! - points[points.size - 1]!).normalize
    calculateOpenBezierSpline points startVec endVec false

/-- The `ISplineInterpolator` implementation of `CubicSplineInterpolator`. -/
def interpolator : SplineInterpolator where
  interpolatePoints := calculateOpenBezierSplineDefault
  interpolatePointsWithTangents := calculateOpenBezierSpline

end CubicSplineInterpolator

end Elk.Core.Math
