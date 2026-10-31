import Elk.Graph.Properties
import Elk.Alg.Common.Polyomino.Structures.Polyomino
import Elk.Alg.Common.Polyomino.ProfileFill
/-!
# `org.eclipse.elk.alg.common.polyomino.structures.Polyominoes`

The polyominoes to pack, the packing grid and the packing options (elk-rs
`structures/polyominoes.rs`). The grid is `2 * (sum of the polyomino sizes + size of the first
polyomino)` in each dimension, widened (aspect ratio > 1) or heightened (otherwise, Java: also for
`0` and NaN) by the aspect ratio (`ceil`, Java `(int)` cast).
-/
namespace Elk.Alg.Common.Polyomino.Structures

open Elk.Graph

/-- `Polyominoes<P>`. -/
structure Polyominoes (P : Type) where
  /-- `MapPropertyHolder` (packing options, see `PolyominoOptions`). -/
  properties : PropertyMap := {}
  /-- `getPolyominoes()`. -/
  polys : Array P := #[]
  /-- `getGrid()`: the packing grid. -/
  grid : PlanarGrid := {}

namespace Polyominoes

variable {P : Type}

/-- Java `(int) x`: truncation toward zero, saturating to the `int` range, NaN → 0. -/
private def javaInt (x : Float) : Int :=
  let v := x.toInt64.toInt
  if v > 2147483647 then 2147483647 else if v < -2147483648 then -2147483648 else v

/-- The filled polyominoes and the grid size of `new Polyominoes(polys, aspectRatio, fill)`. -/
def prepare [PolyominoLike P] (polys : Array P) (aspectRatio : Float) (fill : Bool) :
    Array P × Nat × Nat := Id.run do
  let mut polyVec : Array P := Array.mkEmpty polys.size
  let mut gridWidth : Nat := 0
  let mut gridHeight : Nat := 0
  for poly in polys do
    let poly := if fill then ProfileFill.fillPolyomino poly else poly
    gridWidth := gridWidth + PolyominoLike.width poly
    gridHeight := gridHeight + PolyominoLike.height poly
    polyVec := polyVec.push poly
  if let some poly := polyVec[0]? then
    gridWidth := gridWidth + PolyominoLike.width poly
    gridHeight := gridHeight + PolyominoLike.height poly
  gridWidth := gridWidth * 2
  gridHeight := gridHeight * 2
  -- Java `(int) Math.ceil(...)` (saturating, NaN → 0); a negative result (negative aspect ratio)
  -- cannot occur with DisCo polyominoes (their heights are then 0) and is clamped to 0
  if aspectRatio > 1.0 then
    gridWidth := (javaInt (gridWidth.toFloat * aspectRatio).ceil).toNat
  else
    gridHeight := (javaInt (gridHeight.toFloat / aspectRatio).ceil).toNat
  return (polyVec, gridWidth, gridHeight)

/-- `new Polyominoes(polys, aspectRatio, fill)`: optionally fills the polyominoes
(`ProfileFill`) and sizes the packing grid. -/
def new [PolyominoLike P] (polys : Array P) (aspectRatio : Float) (fill : Bool) : Polyominoes P :=
  let (polyVec, gridWidth, gridHeight) := prepare polys aspectRatio fill
  { polys := polyVec, grid := PlanarGrid.new gridWidth gridHeight }

/-- Largest grid (64-bit words, 2^31 cells) elk-lean allocates (Java: `-Xmx` dependent). -/
def MAX_GRID_WORDS : Nat := 1 <<< 26

/-- `new Polyominoes(...)` with Java's allocation failures of `new long[height][ceil(width / 32)]`
instead of an allocation that would exhaust the memory (an extreme aspect ratio such as `1e-9` or
`1e9`): `OutOfMemoryError: Requested array size exceeds VM limit` for a dimension of
`Integer.MAX_VALUE - 1` or more, `OutOfMemoryError: Java heap space` above `MAX_GRID_WORDS` words
(the heap limit itself depends on the JVM; the error is Java's text). -/
def newChecked [PolyominoLike P] (polys : Array P) (aspectRatio : Float) (fill : Bool) :
    Except String (Polyominoes P) := do
  let (polyVec, gridWidth, gridHeight) := prepare polys aspectRatio fill
  let words := (gridWidth + 31) / 32
  if gridHeight >= 2147483646 || words >= 2147483646 then
    throw "java.lang.OutOfMemoryError: Requested array size exceeds VM limit"
  if words * gridHeight > MAX_GRID_WORDS then
    throw "java.lang.OutOfMemoryError: Java heap space"
  return { polys := polyVec, grid := PlanarGrid.new gridWidth gridHeight }

/-- `getProperty(property)`. -/
@[inline] def getProperty {α : Type} [PropCodec α] (h : Polyominoes P) (p : Property α) : Option α :=
  h.properties.get p

/-- `setProperty(property, value)` (`none` removes the value). -/
@[inline] def setProperty {α : Type} [PropCodec α] (h : Polyominoes P) (p : Property α)
    (v : Option α) : Polyominoes P :=
  { h with properties := h.properties.setOpt p v }

end Polyominoes

end Elk.Alg.Common.Polyomino.Structures
