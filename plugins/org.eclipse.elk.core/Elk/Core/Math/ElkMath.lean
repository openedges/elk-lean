import Elk.Core.Math.KVector
import Elk.Core.Math.KVectorChain
import Elk.Core.Math.ElkRectangle
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.core.math.ElkMath`

Mathematical helper functions: factorials, binomial coefficients, integer
powers, Bezier curve approximation and distance, max/min/average/bound
families, vector clipping, line/rectangle intersection and containment tests.

Port of the elk-rs `elk_math.rs`. Differences to the Rust API:
* the trait-based overloads `intersects(...)` / `contains(...)` are separately
  named functions (`intersectsRectPath`, `intersectsRectLine`, `intersectsLines`,
  `containsRectPath`, `containsRectLine`, `containsRectPoint`);
* `panic!` calls become `Except String` results (`factl`, `factd`,
  `binomiall`, `binomiald`);
* mutating vector arguments (`clipVector`) are returned as new values;
* fixed-size Rust arrays are `Array` values of the same length;
* `f32` arithmetic is emulated with `Float.toF32` after every operation.
-/
namespace Elk.Core.Math

open Elk.Core.Util

namespace ElkMath

/-- `FACT_TABLE`: the factorials `0!` … `20!`. -/
def FACT_TABLE : Array Int :=
  #[1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800, 39916800, 479001600,
    6227020800, 87178291200, 1307674368000, 20922789888000, 355687428096000,
    6402373705728000, 121645100408832000, 2432902008176640000]

/-- `W_DEGREE`: degree of the Bezier form used for root finding. -/
def W_DEGREE : Nat := 5
/-- `DEGREE`: degree of the cubic Bezier segments. -/
def DEGREE : Nat := 3
/-- `MAXDEPTH`: maximum recursion depth of the root finder. -/
def MAXDEPTH : Nat := 64
/-- `EPSILON` = `1 / 2^(MAXDEPTH + 1)`. -/
def EPSILON : Float := 1.0 / 36893488147419103232.0
/-- `DOUBLE_EQ_EPSILON`. -/
def DOUBLE_EQ_EPSILON : Float := 0.00001

/-- `ZERO_VECTOR`. -/
def ZERO_VECTOR : KVector := ⟨0.0, 0.0⟩

/-- `CUBIC_Z`: precomputed z-table for cubic Bezier root finding. -/
def CUBIC_Z : Array (Array Float) :=
  #[#[1.0, 0.6, 0.3, 0.1],
    #[0.4, 0.6, 0.6, 0.4],
    #[0.1, 0.3, 0.6, 1.0]]

/-- `f32::MAX`. -/
def F32_MAX : Float := 3.4028234663852886e38

/-- `ElkMath.factl(int)`: factorial as a long (`0 ≤ x ≤ 20`). -/
def factl (x : Int) : Except String Int :=
  if x < 0 || x >= FACT_TABLE.size then
    throw s!"The input must be between 0 and {FACT_TABLE.size}"
  else
    return FACT_TABLE[x.toNat]!

/-- The squaring loop of `powd` (`while exp > 0`): a tail-recursive function so that `result` and
`base` stay unboxed. -/
private partial def powdLoop (result base : Float) (exp : Nat) : Float :=
  if exp == 0 then result
  else if exp % 2 == 0 then powdLoop result (base * base) (exp / 2)
  else powdLoop (result * base) base (exp - 1)

/-- `ElkMath.powd(double, int)`: integer power by squaring. -/
def powd (a : Float) (b : Int) : Float :=
  let result := powdLoop 1.0 a b.natAbs
  if b < 0 then 1.0 / result else result

/-- `ElkMath.powf(float, int)`: integer power by squaring in single precision. -/
def powf (a : Float) (b : Int) : Float := Id.run do
  let mut result := 1.0
  let mut base := Float.toF32 a
  let mut exp : Int := if b >= 0 then b else -b
  while exp > 0 do
    if Int.tmod exp 2 == 0 then
      base := Float.toF32 (base * base)
      exp := Int.tdiv exp 2
    else
      result := Float.toF32 (result * base)
      exp := exp - 1
  return if b < 0 then Float.toF32 (1.0 / result) else result

/-- Unchecked `factd` for `x ≥ 0`. -/
private def factdU (x : Int) : Float :=
  if x < FACT_TABLE.size then
    Float.ofInt FACT_TABLE[x.toNat]!
  else
    let xf := Float.ofInt x
    let pow := powf (Float.toF32 xf) x
    Float.sqrt (2.0 * Float.pi * xf) * (pow / powd Float.e x)

/-- `ElkMath.factd(int)`: factorial as a double (Stirling approximation for `x > 20`). -/
def factd (x : Int) : Except String Float :=
  if x < 0 then throw "The input must be positive" else return factdU x

/-- `ElkMath.binomiall(int, int)`: binomial coefficient as a long. -/
partial def binomiall (n k : Int) : Except String Int := do
  if n < 0 || k < 0 then throw "k and n must be positive"
  else if k > n then throw "k must be smaller than n"
  else if k == 0 || k == n then return 1
  else if n == 0 then return 0
  else if n < FACT_TABLE.size then
    return (← factl n) / ((← factl k) * (← factl (n - k)))
  else
    return (← binomiall (n - 1) (k - 1)) + (← binomiall (n - 1) k)

/-- Unchecked `binomiald` for `0 ≤ k ≤ n`. -/
private def binomialdU (n k : Int) : Float :=
  if k == 0 || k == n then 1.0
  else if n == 0 then 0.0
  else factdU n / (factdU k * factdU (n - k))

/-- `ElkMath.binomiald(int, int)`: binomial coefficient as a double. -/
def binomiald (n k : Int) : Except String Float :=
  if n < 0 || k < 0 then throw "k and n must be positive"
  else if k > n then throw "k must be smaller than n"
  else return binomialdU n k

/-- `ElkMath.getPointOnBezierSegment(t, controlPoints)`: point at parameter `t`
of the Bezier curve with the given control points. -/
def getPointOnBezierSegment (t : Float) (controlPoints : Array KVector) : KVector :=
  if controlPoints.isEmpty then KVector.zero
  else bezierPointFrom t controlPoints (controlPoints.size - 1) 0 0.0 0.0
where
  /-- The sum over the control points `j, j + 1, …` (a tail-recursive loop: the sums stay unboxed). -/
  bezierPointFrom (t : Float) (controlPoints : Array KVector) (n j : Nat) (px py : Float) : KVector :=
    if h : j < controlPoints.size then
      let p := controlPoints[j]
      let factor := binomialdU n j * powd (1.0 - t) (Int.ofNat (n - j)) * powd t j
      bezierPointFrom t controlPoints n (j + 1) (px + p.x * factor) (py + p.y * factor)
    else ⟨px, py⟩
  termination_by controlPoints.size - j

/-- `ElkMath.approximateBezierSegment(resultSize, controlPoints)`. -/
def approximateBezierSegment (resultSize : Nat) (controlPoints : Array KVector) : Array KVector :=
  if resultSize == 0 || controlPoints.isEmpty then #[]
  else approximateFrom controlPoints (1.0 / resultSize.toFloat) resultSize 0.0 (Array.mkEmpty resultSize)
where
  /-- The remaining `k` points from parameter `t + dt` on (a tail-recursive loop: `t` stays unboxed). -/
  approximateFrom (controlPoints : Array KVector) (dt : Float) (k : Nat) (t : Float) (result : Array KVector) :
      Array KVector :=
    match k with
    | 0 => result
    | k + 1 =>
      let t := t + dt
      approximateFrom controlPoints dt k t (result.push (getPointOnBezierSegment t controlPoints))

/-- `ElkMath.approximateBezierSegment(controlPoints)`: uses `size + 1` points. -/
def approximateBezierSegmentDefault (controlPoints : Array KVector) : Array KVector :=
  approximateBezierSegment (controlPoints.size + 1) controlPoints

/-- `ElkMath.approximateBezierSpline(controlPoints)`. -/
def approximateBezierSpline (controlPoints : KVectorChain) : KVectorChain := Id.run do
  let count := controlPoints.size
  let mut spline : KVectorChain := #[]
  if count == 0 then return spline
  let mut index := 1
  let mut currentPoint := controlPoints[0]!
  spline := spline.push currentPoint
  while index < count do
    let remaining := count - index
    if remaining == 1 then
      spline := spline.push controlPoints[index]!
      break
    else if remaining == 2 then
      let c1 := controlPoints[index]!
      let c2 := controlPoints[index + 1]!
      spline := spline ++ approximateBezierSegmentDefault #[currentPoint, c1, c2]
      break
    else
      let c1 := controlPoints[index]!
      let c2 := controlPoints[index + 1]!
      let nextPoint := controlPoints[index + 2]!
      spline := spline ++ approximateBezierSegmentDefault #[currentPoint, c1, c2, nextPoint]
      currentPoint := nextPoint
      index := index + 3
  return spline

/-- Private `bezier(c, degree, t, left, right)`: de Casteljau evaluation. Returns
the point, the left control polygon and the right control polygon. -/
def bezier (c : Array KVector) (degree : Nat) (t : Float) :
    KVector × Array KVector × Array KVector := Id.run do
  let mut p : Array (Array KVector) := #[c.extract 0 (degree + 1)]
  for i in [1:degree + 1] do
    let prev := p[i - 1]!
    let mut row : Array KVector := #[]
    for j in [0:degree + 1 - i] do
      row := row.push ⟨(1.0 - t) * prev[j]!.x + t * prev[j + 1]!.x,
                       (1.0 - t) * prev[j]!.y + t * prev[j + 1]!.y⟩
    p := p.push row
  let mut left : Array KVector := #[]
  let mut right : Array KVector := #[]
  for j in [0:degree + 1] do
    left := left.push p[j]![0]!
    right := right.push p[degree - j]![j]!
  return (p[degree]![0]!, left, right)

/-- Private `convertToBezierForm(v, pa)`: Bezier form (degree 5) of the distance polynomial. -/
def convertToBezierForm (v : Array KVector) (pa : KVector) : Array KVector := Id.run do
  let mut c : Array KVector := #[]
  for i in [0:DEGREE + 1] do
    c := c.push ⟨v[i]!.x - pa.x, v[i]!.y - pa.y⟩
  let s := DEGREE.toFloat
  let mut d : Array KVector := #[]
  for i in [0:DEGREE] do
    d := d.push ⟨s * (v[i + 1]!.x - v[i]!.x), s * (v[i + 1]!.y - v[i]!.y)⟩
  let mut cdTable : Array (Array Float) := #[]
  for row in [0:DEGREE] do
    let mut r : Array Float := #[]
    for column in [0:DEGREE + 1] do
      r := r.push (d[row]!.x * c[column]!.x + d[row]!.y * c[column]!.y)
    cdTable := cdTable.push r
  let mut w : Array KVector := #[]
  for i in [0:W_DEGREE + 1] do
    w := w.push ⟨i.toFloat / W_DEGREE.toFloat, 0.0⟩
  let n := DEGREE
  let m := DEGREE - 1
  for k in [0:n + m + 1] do
    let lb := k - m
    let ub := if k <= n then k else n
    for i in [lb:ub + 1] do
      let j := k - i
      let cur := w[i + j]!
      w := w.set! (i + j) { cur with y := cur.y + cdTable[j]![i]! * CUBIC_Z[j]![i]! }
  return w

/-- Private `crossingCount(v, degree)`: number of sign changes of the y-coordinates. -/
def crossingCount (v : Array KVector) (degree : Nat) : Nat := Id.run do
  let mut nCrossings := 0
  let mut sign : Int := if v[0]!.y < 0.0 then -1 else 1
  let mut oldSign := sign
  for i in [1:degree + 1] do
    sign := if v[i]!.y < 0.0 then -1 else 1
    if sign != oldSign then nCrossings := nCrossings + 1
    oldSign := sign
  return nCrossings

/-- Private `controlPolygonFlatEnough(v, degree)`. -/
def controlPolygonFlatEnough (v : Array KVector) (degree : Nat) : Bool := Id.run do
  let a := v[0]!.y - v[degree]!.y
  let b := v[degree]!.x - v[0]!.x
  let c := v[0]!.x * v[degree]!.y - v[degree]!.x * v[0]!.y
  let abSquared := a * a + b * b
  let mut distance : Array Float := Array.replicate (W_DEGREE + 1) 0.0
  for i in [1:degree] do
    let mut di := a * v[i]!.x + b * v[i]!.y + c
    if di > 0.0 then di := (di * di) / abSquared
    if di < 0.0 then di := -((di * di) / abSquared)
    distance := distance.set! i di
  let mut maxAbove := 0.0
  let mut maxBelow := 0.0
  for i in [1:degree] do
    let value := distance[i]!
    if value < 0.0 then maxBelow := fmin maxBelow value
    if value > 0.0 then maxAbove := fmax maxAbove value
  let a1 := 0.0
  let b1 := 1.0
  let c1 := 0.0
  let a2 := a
  let b2 := b
  let c2 := c + maxAbove
  let det := a1 * b2 - a2 * b1
  let dInv := 1.0 / det
  let intercept1 := (b1 * c2 - b2 * c1) * dInv
  let c2' := c + maxBelow
  let det' := a1 * b2 - a2 * b1
  let dInv' := 1.0 / det'
  let intercept2 := (b1 * c2' - b2 * c1) * dInv'
  let leftIntercept := fmin intercept1 intercept2
  let rightIntercept := fmax intercept1 intercept2
  let error := (rightIntercept - leftIntercept) / 2.0
  return error < EPSILON

/-- Private `computeXIntercept(v, degree)`. -/
def computeXIntercept (v : Array KVector) (degree : Nat) : Float :=
  let xnm := v[degree]!.x - v[0]!.x
  let ynm := v[degree]!.y - v[0]!.y
  let xmk := v[0]!.x
  let ymk := v[0]!.y
  let detInv := -1.0 / ynm
  (xnm * ymk - ynm * xmk) * detInv

/-- Private `findRoots(w, degree, t, depth)`: roots of the Bezier-form polynomial
(the Rust version fills `t` and returns the count; here the roots are returned). -/
partial def findRoots (w : Array KVector) (degree depth : Nat) : Array Float :=
  let cc := crossingCount w degree
  if cc == 0 then #[]
  else if cc == 1 && depth >= MAXDEPTH then
    #[(w[0]!.x + w[W_DEGREE]!.x) / 2.0]
  else if cc == 1 && controlPolygonFlatEnough w degree then
    #[computeXIntercept w degree]
  else
    let (_, left, right) := bezier w degree 0.5
    findRoots left degree (depth + 1) ++ findRoots right degree (depth + 1)

/-- `ElkMath.distanceFromBezierSegment(start, c1, c2, end, needle)`. -/
def distanceFromBezierSegment (start c1 c2 «end» needle : KVector) : Float := Id.run do
  let v := #[start, c1, c2, «end»]
  let w := convertToBezierForm v needle
  let tCandidates := findRoots w W_DEGREE 0
  let mut minDistance := needle.distance start
  let mut t := 0.0
  for candidate in tCandidates do
    let (p, _, _) := bezier v DEGREE candidate
    let distance := needle.distance p
    if distance < minDistance then
      minDistance := distance
      t := candidate
  let distance := needle.distance «end»
  if distance < minDistance then
    t := 1.0
  let (pn, _, _) := bezier v DEGREE t
  return Float.sqrt (pn.distance needle)

/-- `ElkMath.max(int...)`. -/
def maxi (values : Array Int) : Int :=
  values.foldl (fun m v => if v > m then v else m) (-2147483648)

/-- `ElkMath.min(int...)`. -/
def mini (values : Array Int) : Int :=
  values.foldl (fun m v => if v < m then v else m) 2147483647

/-- `ElkMath.average(int...)` (32-bit wrapping sum, truncating division). -/
def averagei (values : Array Int) : Int :=
  let sum := values.foldl (fun a v => Int.wrap32 (a + v)) 0
  Int.tdiv sum values.size

/-- `ElkMath.max(long...)` (the reference starts from `Integer.MIN_VALUE`). -/
def maxl (values : Array Int) : Int :=
  values.foldl (fun m v => if v > m then v else m) (-2147483648)

/-- `ElkMath.min(long...)` (the reference starts from `Integer.MAX_VALUE`). -/
def minl (values : Array Int) : Int :=
  values.foldl (fun m v => if v < m then v else m) 2147483647

/-- `ElkMath.average(long...)`. -/
def averagel (values : Array Int) : Int :=
  Int.tdiv (values.foldl (· + ·) 0) values.size

/-- `ElkMath.max(float...)`; values are single-precision floats. -/
def maxf (values : Array Float) : Float :=
  values.foldl (fun m v => if v > m then v else m) (-F32_MAX)

/-- `ElkMath.min(float...)`. -/
def minf (values : Array Float) : Float :=
  values.foldl (fun m v => if v < m then v else m) F32_MAX

/-- `ElkMath.average(float...)` with single-precision accumulation. -/
def averagef (values : Array Float) : Float :=
  let sum := values.foldl (fun a v => Float.toF32 (a + v)) 0.0
  Float.toF32 (sum / Float.toF32 values.size.toFloat)

/-- `ElkMath.max(double...)`. -/
def maxd (values : Array Float) : Float :=
  values.foldl (fun m v => if v > m then v else m) Float.minValue

/-- `ElkMath.min(double...)`. -/
def mind (values : Array Float) : Float :=
  values.foldl (fun m v => if v < m then v else m) Float.maxValue

/-- `ElkMath.average(double...)`. -/
def averaged (values : Array Float) : Float :=
  values.foldl (· + ·) 0.0 / values.size.toFloat

/-- `ElkMath.bound(int, int, int)`. -/
def boundi (x lower upper : Int) : Int :=
  if x <= lower then lower else if x >= upper then upper else x

/-- `ElkMath.bound(long, long, long)`. -/
def boundl (x lower upper : Int) : Int := boundi x lower upper

/-- `ElkMath.bound(float, float, float)`. -/
def boundf (x lower upper : Float) : Float :=
  if x <= lower then lower else if x >= upper then upper else x

/-- `ElkMath.bound(double, double, double)`. -/
def boundd (x lower upper : Float) : Float := boundf x lower upper

/-- `ElkMath.clipVector(v, width, height)`: scales `v` so that it lies in the
box of the given size centered at the origin; returns the new vector. -/
def clipVector (v : KVector) (width height : Float) : KVector :=
  let wh := width / 2.0
  let hh := height / 2.0
  let absx := v.x.abs
  let absy := v.y.abs
  let xscale := if absx > wh then wh / absx else 1.0
  let yscale := if absy > hh then hh / absy else 1.0
  v.scale (fmin xscale yscale)

/-- `ElkMath.signum(double)`. -/
def signum (x : Float) : Int :=
  if x < 0.0 then -1 else if x > 0.0 then 1 else 0

/-- `ElkMath.fuzzyEquals(a, b, eps)`. -/
def fuzzyEquals (a b eps : Float) : Bool := (a - b).abs <= eps

/-- `ElkMath.fuzzyCompare(a, b, eps)`. -/
def fuzzyCompare (a b eps : Float) : Int :=
  if a < b - eps then -1 else if a > b + eps then 1 else 0

/-- `ElkMath.contains(rect, p)`: strict containment of a point. -/
def containsRectPoint (rect : ElkRectangle) (p : KVector) : Bool :=
  let minX := rect.x
  let maxX := rect.x + rect.width
  let minY := rect.y
  let maxY := rect.y + rect.height
  (p.x > minX && p.x < maxX) && (p.y > minY && p.y < maxY)

/-- `ElkMath.contains(rect, p1, p2)`: both end points inside. -/
def containsRectLine (rect : ElkRectangle) (p1 p2 : KVector) : Bool :=
  containsRectPoint rect p1 && containsRectPoint rect p2

/-- `ElkMath.contains(rect, path)`: all segments of the closed path inside. -/
def containsRectPath (rect : ElkRectangle) (path : KVectorChain) : Bool := Id.run do
  if path.size < 2 then return false
  let first := path[0]!
  let mut p1 := first
  for i in [1:path.size] do
    let p2 := path[i]!
    if !containsRectLine rect p1 p2 then return false
    p1 := p2
  return containsRectLine rect p1 first

/-- `ElkMath.intersects(l11, l12, l21, l22)`: proper intersection of two segments. -/
def intersectsLines (l11 l12 l21 l22 : KVector) : Bool :=
  let u0 := l11
  let v0 := l12 - l11
  let u1 := l21
  let v1 := l22 - l21
  let x00 := u0.x
  let y00 := u0.y
  let x10 := u1.x
  let y10 := u1.y
  let x01 := v0.x
  let y01 := v0.y
  let x11 := v1.x
  let y11 := v1.y
  let d := x11 * y01 - x01 * y11
  if fuzzyEquals 0.0 d DOUBLE_EQ_EPSILON then false
  else
    let s := (1.0 / d) * ((x00 - x10) * y01 - (y00 - y10) * x01)
    let t := (1.0 / d) * -(-(x00 - x10) * y11 + (y00 - y10) * x11)
    fuzzyCompare 0.0 s DOUBLE_EQ_EPSILON < 0
      && fuzzyCompare s 1.0 DOUBLE_EQ_EPSILON < 0
      && fuzzyCompare 0.0 t DOUBLE_EQ_EPSILON < 0
      && fuzzyCompare t 1.0 DOUBLE_EQ_EPSILON < 0

/-- `ElkMath.intersects(rect, p1, p2)`: the segment crosses the rectangle border. -/
def intersectsRectLine (rect : ElkRectangle) (p1 p2 : KVector) : Bool :=
  if containsRectLine rect p1 p2 then false
  else
    let topLeft := rect.topLeft
    let topRight := rect.topRight
    let bottomRight := rect.bottomRight
    let bottomLeft := rect.bottomLeft
    intersectsLines topLeft topRight p1 p2
      || intersectsLines topRight bottomRight p1 p2
      || intersectsLines bottomRight bottomLeft p1 p2
      || intersectsLines bottomLeft topLeft p1 p2

/-- `ElkMath.intersects(rect, path)`: the closed path crosses the rectangle border. -/
def intersectsRectPath (rect : ElkRectangle) (path : KVectorChain) : Bool := Id.run do
  if path.size < 2 then return false
  let first := path[0]!
  let mut p1 := first
  for i in [1:path.size] do
    let p2 := path[i]!
    if intersectsRectLine rect p1 p2 then return true
    p1 := p2
  return intersectsRectLine rect p1 first

/-- `ElkMath.intersects2(p, r, q, s)`: intersection point of the rays `p + t r`
and `q + u s` (restricted to `t, u ∈ [0, 1]`), if any. -/
def intersects2 (p r q s : KVector) : Option KVector :=
  let pq := q - p
  let pqXr := KVector.crossProduct pq r
  let rXs := KVector.crossProduct r s
  let t := KVector.crossProduct pq s / rXs
  let u := pqXr / rXs
  if rXs == 0.0 then
    if pqXr == 0.0 then
      let center := q + s.scale 0.5
      let d1 := p.distance center
      let pPlusR := p + r
      let d2 := pPlusR.distance center
      let l := s.length * 0.5
      if d1 < d2 && d1 <= l then some p
      else if d2 <= l then some pPlusR
      else none
    else none
  else if 0.0 <= t && t <= 1.0 && 0.0 <= u && u <= 1.0 then
    some (p + r.scale t)
  else none

/-- `ElkMath.traceRays(a1, a2, b1, b2, v)`: distance from the segment `b` to the
segment `a` along direction `v`. -/
def traceRays (a1 a2 b1 b2 v : KVector) : Float := Id.run do
  let mut result := Float.posInf
  let mut endpointHit := false
  let b1PlusV := b1 + v
  let bDir := b2 - b1
  let aDir := a2 - a1
  let edgeCase :=
    match intersects2 a1 aDir b1PlusV bDir with
    | some point => !(point.equalsFuzzily a1 || point.equalsFuzzily a2)
    | none => false
  match intersects2 a1 aDir b1 v with
  | some point =>
    if point.equalsFuzzily a1 == point.equalsFuzzily a2 || edgeCase then
      result := fmin result (point - b1).length
    else
      endpointHit := true
  | none => pure ()
  match intersects2 a1 aDir b2 v with
  | some point =>
    if endpointHit || point.equalsFuzzily a1 == point.equalsFuzzily a2 || edgeCase then
      result := fmin result (point - b2).length
  | none => pure ()
  return result

/-- `ElkMath.distance(a1, a2, b1, b2, v)`: distance between two segments along `v`. -/
def distance (a1 a2 b1 b2 v : KVector) : Float :=
  fmin (traceRays a1 a2 b1 b2 v) (traceRays b1 b2 a1 a2 v.negate)

/-- `ElkMath.shortestDistance(r1, r2)`: signed shortest distance between two rectangles
(negative if they overlap). -/
def shortestDistance (r1 r2 : ElkRectangle) : Float :=
  let rightDist := r2.x - (r1.x + r1.width)
  let leftDist := r1.x - (r2.x + r2.width)
  let topDist := r1.y - (r2.y + r2.height)
  let bottomDist := r2.y - (r1.y + r1.height)
  let horzDist := fmax leftDist rightDist
  let vertDist := fmax topDist bottomDist
  if (fuzzyCompare horzDist 0.0 DOUBLE_EQ_EPSILON >= 0)
      != (fuzzyCompare vertDist 0.0 DOUBLE_EQ_EPSILON >= 0) then
    fmax vertDist horzDist
  else if fuzzyCompare horzDist 0.0 DOUBLE_EQ_EPSILON > 0 then
    Float.sqrt (vertDist * vertDist + horzDist * horzDist)
  else
    -(Float.sqrt (vertDist * vertDist + horzDist * horzDist))

end ElkMath

end Elk.Core.Math
