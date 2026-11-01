import Elk.Core.Math.KVector
/-!
# `org.eclipse.elk.core.math.KVectorChain`

A chain of vectors is an `Array KVector`; the `KVectorChain` namespace adds the
Java API on top of the array operations.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Core.Math

open Elk.Core.Util

abbrev KVectorChain := Array KVector

namespace KVectorChain

@[inline] def empty : KVectorChain := #[]

@[inline] def ofArray (vs : Array KVector) : KVectorChain := vs

@[inline] def size (c : KVectorChain) : Nat := Array.size c

/-- `addFirst`. -/
@[inline] def addFirst (c : KVectorChain) (v : KVector) : KVectorChain := c.insertIdx! 0 v

/-- `add`/`addLast`. -/
@[inline] def addLast (c : KVectorChain) (v : KVector) : KVectorChain := c.push v

@[inline] def addValues (c : KVectorChain) (x y : Float) : KVectorChain := c.push ⟨x, y⟩

/-- `getFirst` (panics on an empty chain in Java; here `default`). -/
@[inline] def first! (c : KVectorChain) : KVector := c[0]!

@[inline] def last! (c : KVectorChain) : KVector := c[c.size - 1]!

@[inline] def first? (c : KVectorChain) : Option KVector := c[0]?

@[inline] def last? (c : KVectorChain) : Option KVector := c.back?

/-- `removeLast`. -/
@[inline] def removeLast (c : KVectorChain) : KVectorChain := c.pop

/-! The per-vector updaters are out of line (PLAN 7.1 items 16, 59): an inlined lambda in
`Array.map` tests the vector's exclusivity before its slot is cleared, so every vector was
reallocated; the `@[noinline]` updater receives the unshared vector and reuses it. -/
@[noinline] private def addValuesTo (dx dy : Float) (v : KVector) : KVector := v.addValues dx dy
-- `o` passed as its coordinates: with two vector arguments the compiler reuses the cell of `o`
-- (shared by all calls) instead of the vector's
@[noinline] private def addTo (ox oy : Float) (v : KVector) : KVector := ⟨v.x + ox, v.y + oy⟩
@[noinline] private def scaleBy (s : Float) (v : KVector) : KVector := v.scale s

/-- `offset(dx, dy)` applied to every vector. -/
def offsetValues (c : KVectorChain) (dx dy : Float) : KVectorChain := c.map (addValuesTo dx dy)

/-- `offset(KVector)`. -/
def offset (c : KVectorChain) (o : KVector) : KVectorChain := c.map (addTo o.x o.y)

/-- `scale`. -/
def scale (c : KVectorChain) (s : Float) : KVectorChain := c.map (scaleBy s)

/-- `KVectorChain.reverse(chain)`. -/
def reverse (c : KVectorChain) : KVectorChain := Array.reverse c

/-- `totalLength`: sum of the segment lengths. -/
def totalLength (c : KVectorChain) : Float := Id.run do
  let mut l := 0.0
  if c.size >= 2 then
    for i in [0:c.size - 1] do
      l := l + c[i]!.distance c[i + 1]!
  return l

def hasNaN (c : KVectorChain) : Bool := c.any (·.isNaN)
def hasInfinite (c : KVectorChain) : Bool := c.any (·.isInfinite)

/-- `pointOnLine(dist)`: the point at the given distance along the chain
(negative distances measure from the end). -/
def pointOnLine (c : KVectorChain) (dist : Float) : KVector := Id.run do
  if c.size == 0 then return default
  if c.size == 1 then return c[0]!
  let absDistance := dist.abs
  let mut distanceSum := fl0p0
  if dist >= fl0p0 then
    for i in [0:c.size - 1] do
      let current := c[i]!
      let next := c[i + 1]!
      let additional := current.distance next
      if additional > fl0p0 then
        let oldSum := distanceSum
        distanceSum := distanceSum + additional
        if distanceSum >= absDistance then
          let relative := (absDistance - oldSum) / additional
          return ((next - current).scale relative) + current
    return c[c.size - 1]!
  else
    let mut i := c.size - 1
    while i >= 1 do
      let current := c[i]!
      let next := c[i - 1]!
      let additional := current.distance next
      if additional > fl0p0 then
        let oldSum := distanceSum
        distanceSum := distanceSum + additional
        if distanceSum >= absDistance then
          let relative := (absDistance - oldSum) / additional
          return ((next - current).scale relative) + current
      i := i - 1
    return c[0]!

/-- `angleOnLine(dist)`: direction angle (radians) of the segment at the distance. -/
def angleOnLine (c : KVectorChain) (dist : Float) : Float := Id.run do
  if c.size < 2 then return fl0p0
  let absDistance := dist.abs
  let mut distanceSum := fl0p0
  if dist >= fl0p0 then
    for i in [0:c.size - 1] do
      let current := c[i]!
      let next := c[i + 1]!
      let additional := current.distance next
      if additional > fl0p0 then
        distanceSum := distanceSum + additional
        if distanceSum >= absDistance then
          return (next - current).toRadians
    return (c[c.size - 1]! - c[c.size - 2]!).toRadians
  else
    let mut i := c.size - 1
    while i >= 1 do
      let current := c[i]!
      let next := c[i - 1]!
      let additional := current.distance next
      if additional > fl0p0 then
        distanceSum := distanceSum + additional
        if distanceSum >= absDistance then
          return (next - current).toRadians
      i := i - 1
    return (c[0]! - c[1]!).toRadians

/-- `parse`: numbers separated by `,;()[]{} \t\n`, taken pairwise. -/
def parse (s : String) : Except String KVectorChain := do
  let delims := ",;()[]{} \t\n"
  let normalized := String.map (fun ch => if delims.any (· == ch) then ' ' else ch) s
  let tokens := normalized.splitOn " "
  let mut result : KVectorChain := #[]
  let mut xy := 0
  let mut x := 0.0
  for tok in tokens do
    let t := tok.trimAscii.toString
    if !t.isEmpty then
      match parseFloat? t with
      | none => throw "The given string does not match the expected format for vectors."
      | some v =>
        if xy % 2 == 0 then x := v else result := result.push ⟨x, v⟩
        xy := xy + 1
  return result

/-- Java/Rust `toString`: `(x1,y1; x2,y2)`. -/
def toJavaString (c : KVectorChain) : String :=
  "(" ++ "; ".intercalate (c.toList.map fun v => s!"{Float.toRustDisplay v.x},{Float.toRustDisplay v.y}") ++ ")"

end KVectorChain

end Elk.Core.Math
