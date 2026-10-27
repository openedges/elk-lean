import Elk.Graph.Properties
import Elk.Alg.Common.Polyomino.Structures.Polyomino
import Elk.Alg.Common.Polyomino.ProfileFill
/-!
# `org.eclipse.elk.alg.common.polyomino.structures.Polyominoes`

The polyominoes to pack, the packing grid and the packing options (elk-rs
`structures/polyominoes.rs`). The grid is `2 * (sum of the polyomino sizes + size of the first
polyomino)` in each dimension, widened (aspect ratio > 1) or heightened (0 < aspect ratio <= 1)
by the aspect ratio (`ceil`, saturating cast like Rust `as usize`).
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

/-- `new Polyominoes(polys, aspectRatio, fill)`: optionally fills the polyominoes
(`ProfileFill`) and sizes the packing grid. -/
def new [PolyominoLike P] (polys : Array P) (aspectRatio : Float) (fill : Bool) : Polyominoes P := Id.run do
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
  if aspectRatio > 1.0 then
    gridWidth := (gridWidth.toFloat * aspectRatio).ceil.toUInt64.toNat
  else if aspectRatio > 0.0 then
    gridHeight := (gridHeight.toFloat / aspectRatio).ceil.toUInt64.toNat
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
