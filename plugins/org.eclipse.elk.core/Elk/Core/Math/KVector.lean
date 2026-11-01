import Elk.Core.Util.Java
import Elk.Core.Util.JavaHashSet
import Elk.Core.Util.Random
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.core.math.KVector`

Immutable two-dimensional vector. The Java class mutates in place
(`v.add(w)` returns `v`); the Lean port is value based, so every
"mutating" method returns the new vector and callers rebind.

The trigonometric methods use the reference JVM's functions (`Math.sin`/`Math.cos`: HotSpot
aarch64 stubs, `Math.asin`/`Math.acos`: fdlibm; `Elk.Core.Util.Java`), not the C library.
-/

namespace Elk.Core.Math

open Elk.Core.Util

structure KVector where
  x : Float := 0
  y : Float := 0
  deriving Repr, Inhabited

namespace KVector

/-- Fuzzyness used by `equalsFuzzily`. -/
def DEFAULT_FUZZYNESS : Float := 0.05

@[inline] def zero : KVector := {}

@[inline] def mk' (x y : Float) : KVector := ⟨x, y⟩

/-- `new KVector(start, end)`: the vector from `start` to `end`. -/
@[inline] def fromPoints (start «end» : KVector) : KVector := ⟨«end».x - start.x, «end».y - start.y⟩

/-- `new KVector(angle)`: unit vector of the given angle (radians; `Math.cos`, `Math.sin`). -/
def fromAngle (angle : Float) : KVector := ⟨javaCos angle, javaSin angle⟩

/-- Java `equals`: exact comparison of both coordinates (`==` on doubles). -/
instance : BEq KVector := ⟨fun a b => a.x == b.x && a.y == b.y⟩

instance : Hashable KVector := ⟨fun v => mixHash (hash v.x.toBits) (hash v.y.toBits)⟩

/-- Bitwise equal coordinates (the identity stand-in of `JavaHashCode.javaSame`). -/
@[inline] def sameBits (a b : KVector) : Bool := a.x.toBits == b.x.toBits && a.y.toBits == b.y.toBits

/-- Java `hashCode()`: `Double.hashCode(x) + Integer.reverse(Double.hashCode(y))` (`int` wrap). -/
instance : JavaHashCode KVector where
  javaHashCode v := v.x.javaHashCode + v.y.javaHashCode.javaReverse
  javaSame := sameBits

/-- Java/Rust `toString`: `(x,y)` with Rust `Display` number formatting. -/
instance : ToString KVector := ⟨fun v => s!"({Float.toRustDisplay v.x},{Float.toRustDisplay v.y})"⟩

def equalsFuzzilyWith (a b : KVector) (fuzzyness : Float) : Bool :=
  (a.x - b.x).abs <= fuzzyness && (a.y - b.y).abs <= fuzzyness

def equalsFuzzily (a b : KVector) : Bool := a.equalsFuzzilyWith b DEFAULT_FUZZYNESS

@[inline] def length (v : KVector) : Float := Float.sqrt (v.x * v.x + v.y * v.y)

@[inline] def squareLength (v : KVector) : Float := v.x * v.x + v.y * v.y

@[inline] def add (a b : KVector) : KVector := ⟨a.x + b.x, a.y + b.y⟩
@[inline] def addValues (a : KVector) (dx dy : Float) : KVector := ⟨a.x + dx, a.y + dy⟩
@[inline] def sub (a b : KVector) : KVector := ⟨a.x - b.x, a.y - b.y⟩
@[inline] def subValues (a : KVector) (dx dy : Float) : KVector := ⟨a.x - dx, a.y - dy⟩
/-- `KVector.diff(v1, v2)` = `v1 - v2`. -/
@[inline] def diff (a b : KVector) : KVector := sub a b
@[inline] def scale (v : KVector) (s : Float) : KVector := ⟨v.x * s, v.y * s⟩
@[inline] def scaleValues (v : KVector) (sx sy : Float) : KVector := ⟨v.x * sx, v.y * sy⟩
@[inline] def negate (v : KVector) : KVector := ⟨-v.x, -v.y⟩

instance : Add KVector := ⟨add⟩
instance : Sub KVector := ⟨sub⟩
instance : Neg KVector := ⟨negate⟩
instance : HMul KVector Float KVector := ⟨scale⟩

/-- `KVector.sum(...)`. -/
def sum (vs : Array KVector) : KVector := vs.foldl add zero

/-- `normalize`: unit length, or unchanged if the length is zero. -/
def normalize (v : KVector) : KVector :=
  let l := v.length
  if l > 0.0 then ⟨v.x / l, v.y / l⟩ else v

def scaleToLength (v : KVector) (l : Float) : KVector := (v.normalize).scale l

/-- `toRadians`: the angle of the vector in `[0, 2π)` (`Math.asin`). -/
def toRadians (v : KVector) : Float :=
  let l := v.length
  if v.x >= fl0p0 && v.y >= fl0p0 then javaAsin (v.y / l)
  else if v.x < fl0p0 then Float.pi - javaAsin (v.y / l)
  else fl2p0 * Float.pi + javaAsin (v.y / l)

def toDegrees (v : KVector) : Float := Float.toDegrees v.toRadians

@[inline] def distance (a b : KVector) : Float :=
  let dx := a.x - b.x
  let dy := a.y - b.y
  Float.sqrt (dx * dx + dy * dy)

@[inline] def dotProduct (a b : KVector) : Float := a.x * b.x + a.y * b.y

@[inline] def crossProduct (v w : KVector) : Float := v.x * w.y - v.y * w.x

/-- `rotate(angle)`: anti-clockwise rotation (`Math.cos`, `Math.sin`). -/
def rotate (v : KVector) (angle : Float) : KVector :=
  let c := javaCos angle
  let s := javaSin angle
  ⟨v.x * c - v.y * s, v.x * s + v.y * c⟩

/-- `angle(other)`: `Math.acos(dot / (|a| · |b|))`. -/
def angle (a b : KVector) : Float := javaAcos (a.dotProduct b / (a.length * b.length))

/-- `bound(lowx, lowy, highx, highy)`: clamps into the rectangle. (Java throws
if `highx < lowx` or `highy < lowy`; the port clamps anyway.) -/
def bound (v : KVector) (lowx lowy highx highy : Float) : KVector :=
  let x := if v.x < lowx then lowx else if v.x > highx then highx else v.x
  let y := if v.y < lowy then lowy else if v.y > highy then highy else v.y
  ⟨x, y⟩

@[inline] def isNaN (v : KVector) : Bool := v.x.isNaN || v.y.isNaN
@[inline] def isInfinite (v : KVector) : Bool := v.x.isInf || v.y.isInf

/-- `wiggle(random, amount)`: random offset in `[-amount/2, amount/2)` per coordinate. -/
def wiggle (v : KVector) (random : Random) (amount : Float) : KVector × Random :=
  let (dx, random) := random.nextDouble
  let (dy, random) := random.nextDouble
  -- Rust/Java: `x += r * amount - amount / 2` (the offset is computed first, then added)
  (⟨v.x + (dx * amount - amount / 2.0), v.y + (dy * amount - amount / 2.0)⟩, random)

private def isDelim (c : Char) (delims : String) : Bool := delims.any (· == c)

/-- `parse`: reads `(x,y)`, `[x;y]`, `x y`-style strings. -/
def parse (s : String) : Except String KVector := do
  let chars := s.toList.toArray
  let mut start := 0
  while start < chars.size && isDelim chars[start]! "([{'\" \t\r\n" do
    start := start + 1
  let mut stop := chars.size
  while stop > 0 && isDelim chars[stop - 1]! ")]}'\" \t\r\n" do
    stop := stop - 1
  if start >= stop then throw "The given string does not contain any numbers."
  let slice := String.ofList (chars.extract start stop).toList
  let tokens := (slice.replace ";" ",").replace "\r" ","
  let tokens := (tokens.replace "\n" ",").splitOn ","
  if tokens.length != 2 then
    throw s!"Exactly two numbers are expected, {tokens.length} were found."
  let px := parseFloat? (tokens[0]!.trimAscii.toString)
  let py := parseFloat? (tokens[1]!.trimAscii.toString)
  match px, py with
  | some x, some y => return ⟨x, y⟩
  | _, _ => throw "The given string contains parts that cannot be parsed as numbers."

end KVector

end Elk.Core.Math
