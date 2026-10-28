import Elk.Alg.Layered.Graph
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.layered.p5edges.splines.SplinesMath`

Port of elk-rs `p5edges/splines/splines_math.rs`: mathematics utility functions used by the
spline routing. Port-based helpers take the `LGraphArena` (Rust locks the `LPortRef`).

Two Rust primitives without a Lean counterpart are reproduced here: `fmodRust` (Rust `f64 % f64`,
the exact C `fmod`) and `formatFixed1` (Rust `format!("{:.1}", x)`: exact decimal rounding, ties
to even).
-/
namespace Elk.Alg.Layered.P5Edges.Splines

open Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph

namespace SplinesMath

/-- `EPSILON` (`0.00000001`): differences below this value are treated as zero. -/
def EPSILON : Float := 0.00000001
/-- `HALF_PI` (`PI / 2`). -/
def HALF_PI : Float := Float.pi / 2.0
/-- `QUATER_PI` (`HALF_PI / 2`). -/
def QUATER_PI : Float := HALF_PI / 2.0
/-- `THREE_HALF_PI` (`HALF_PI + HALF_PI + HALF_PI`). -/
def THREE_HALF_PI : Float := HALF_PI + HALF_PI + HALF_PI
/-- `TWO_PI` (`2 * PI`). -/
def TWO_PI : Float := 2.0 * Float.pi
/-- `THREE` (`3`). -/
def THREE : Float := 3.0

/-- Rust `x % y` on `f64` (C `fmod`): the exact remainder with the sign of `x`. Computed by
repeatedly subtracting `|y| * 2^k` (each subtraction is exact by Sterbenz' lemma). -/
def fmodRust (x y : Float) : Float := Id.run do
  if x.isNaN || y.isNaN || x.isInf || y == 0.0 then return Float.nan
  if y.isInf then return x
  let ax := x.abs
  let ay := y.abs
  if ax < ay then return x
  let mut r := ax
  while r >= ay do
    let mut d := ay
    while d * 2.0 <= r do
      d := d * 2.0
    r := r - d
  return if x < 0.0 then -r else r

/-- `round_half_even(m * 2^e * 10)` for the decomposed finite double `m * 2^e`. -/
private def scaledTenthsHalfEven (m : Nat) (e : Int) : Nat :=
  if e >= 0 then m * 10 * 2 ^ e.toNat
  else
    let den := 2 ^ (-e).toNat
    let num := m * 10
    let quo := num / den
    let rem := num % den
    if 2 * rem > den then quo + 1
    else if 2 * rem == den then (if quo % 2 == 1 then quo + 1 else quo)
    else quo

/-- Rust `format!("{:.1}", x)`: the exact binary value rounded half to even to one decimal place
(the minus sign is kept for `-0.0` and small negative values; `NaN`, `inf`, `-inf`). -/
def formatFixed1 (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x > 0.0 then "inf" else "-inf")
  else
    let bits := x.toBits
    let negative := (bits >>> 63) == 1
    let expBits := ((bits >>> 52) &&& 0x7FF).toNat
    let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
    let q := if expBits == 0 then scaledTenthsHalfEven frac (-1074)
      else scaledTenthsHalfEven (frac + 4503599627370496) ((expBits : Int) - 1075)
    let body := s!"{q / 10}.{q % 10}"
    if negative then "-" ++ body else body

/-- `intersect(pt1, pt2, pt3, pt4)`: intersection of the lines `pt1–pt2` and `pt3–pt4`; `none` for
(nearly) parallel lines. -/
def intersect (pt1 pt2 pt3 pt4 : KVector) : Option KVector :=
  let x1 := pt1.x
  let y1 := pt1.y
  let x2 := pt2.x
  let y2 := pt2.y
  let x3 := pt3.x
  let y3 := pt3.y
  let x4 := pt4.x
  let y4 := pt4.y
  let divisor := (x1 - x2) * (y3 - y4) - (y1 - y2) * (x3 - x4)
  if divisor.abs < EPSILON then none
  else
    let first := x1 * y2 - y1 * x2
    let second := x3 * y4 - y3 * x4
    let newX := (first * (x3 - x4) - second * (x1 - x2)) / divisor
    let newY := (first * (y3 - y4) - second * (y1 - y2)) / divisor
    some ⟨newX, newY⟩

/-- `intersect(pt1, pt2, dirPt1, dirPt2)` (Rust `intersect_dir`): intersection of the lines through
`pt1`/`pt2` with the given directions (radians). -/
def intersectDir (pt1 pt2 : KVector) (dirPt1 dirPt2 : Float) : Option KVector :=
  let pt1Dir := KVector.fromAngle dirPt1 + pt1
  let pt2Dir := KVector.fromAngle dirPt2 + pt2
  intersect pt1 pt1Dir pt2 pt2Dir

/-- `innerAngle(vec1, vec2)` (Rust `inner_angle_vec`): the angle between two vectors. -/
def innerAngleVec (vec1 vec2 : KVector) : Float :=
  Float.acos ((vec1.x * vec2.x + vec1.y * vec2.y) / (vec1.length * vec2.length))

/-- `innerAngle(dir1, dir2)`: `|dir1 - dir2| % PI`. -/
def innerAngle (dir1 dir2 : Float) : Float :=
  let retval := (dir1 - dir2).abs
  fmodRust retval Float.pi

/-- `convertKVectorToString(vector)`: `(x,y)` with one decimal each, `(null)` for `none`. -/
def convertKVectorToString (vector : Option KVector) : String :=
  match vector with
  | none => "(null)"
  | some v => s!"({formatFixed1 v.x},{formatFixed1 v.y})"

/-- `convertKVectorToString(list)` (Rust `convert_kvector_slice_to_string`): the vectors joined by
`", "`, `(null)` for an empty list. -/
def convertKVectorSliceToString (list : Array KVector) : String :=
  if list.isEmpty then "(null)"
  else ", ".intercalate (list.toList.map fun v => convertKVectorToString (some v))

/-- `lengthToOrthogonal(direction, point)`. -/
def lengthToOrthogonal (direction : Float) (point : KVector) : Float := Id.run do
  let mut angle := innerAngle direction point.toRadians
  let mut factor := 1.0
  if angle > HALF_PI then
    factor := -1.0
    angle := angle - QUATER_PI
  return factor * Float.cos angle * point.length

/-- `portSideToDirection(side)`: the outward direction (radians) of a port side. -/
def portSideToDirection (side : PortSide) : Float :=
  match side with
  | .north => THREE_HALF_PI
  | .east => 0.0
  | .south => HALF_PI
  | .west => Float.pi
  | .undefined => 0.0

/-- `distPortToNodeEdge(port, side)`: distance of the port anchor (relative to its node) to the
given node border. -/
def distPortToNodeEdge (a : LGraphArena) (port : LPortId) (side : PortSide) : Float :=
  let pt := a.port port
  let nodeSize : KVector := match pt.owner with
    | some n => (a.node n).size
    | none => {}
  let portPos := pt.position + pt.anchor
  match side with
  | .north => -portPos.y
  | .east => -portPos.x + nodeSize.x
  | .south => -portPos.y + nodeSize.y
  | .west => -portPos.x
  | .undefined => 0.0

/-- `isBetween(int value, int boundary0, int boundary1)` (Rust `is_between_int`). -/
def isBetweenInt (value boundary0 boundary1 : Int) : Bool :=
  if value < boundary0 then boundary1 <= value
  else value <= boundary1 || value == boundary0

/-- `isBetween(value, boundary0, boundary1)`: whether `value` lies between the boundaries
(either order), with an `EPSILON` tolerance. -/
@[inline] def isBetween (value boundary0 boundary1 : Float) : Bool :=
  if (boundary0 - value).abs < EPSILON || (boundary1 - value).abs < EPSILON then true
  else if (boundary0 - value) > EPSILON then (value - boundary1) > EPSILON
  else (boundary1 - value) > EPSILON

/-- `getMarginOnPortSide(node, side)`. -/
def getMarginOnPortSide (a : LGraphArena) (node : LNodeId) (side : PortSide) : Float :=
  let margin := (a.node node).margin
  match side with
  | .north => margin.top
  | .east => margin.right
  | .south => margin.bottom
  | .west => margin.left
  | .undefined => 0.0

end SplinesMath

end Elk.Alg.Layered.P5Edges.Splines
