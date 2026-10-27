import Elk.Alg.Common.Polyomino.Structures.Polyomino
/-!
# `org.eclipse.elk.alg.common.polyomino.ProfileFill`

Profile fill of a polyomino (elk-rs `profile_fill.rs`): a cell is blocked if it lies strictly
between the first and last blocked cell of its row and of its column. The four profiles are
computed before any cell is changed, so the order of the updates does not matter.
-/
namespace Elk.Alg.Common.Polyomino

open Structures

namespace ProfileFill

/-- `ProfileFill.fillPolyomino(poly)`. -/
def fillPolyomino {P : Type} [PolyominoLike P] (poly : P) : P := Id.run do
  let width := PolyominoLike.width poly
  let height := PolyominoLike.height poly
  let mut northProfile : Array Int := Array.replicate width 0
  let mut southProfile : Array Int := Array.replicate width 0
  let mut eastProfile : Array Int := Array.replicate height 0
  let mut westProfile : Array Int := Array.replicate height 0
  for xi in [0:width] do
    let mut y := 0
    while y < height && !PolyominoLike.isBlocked poly xi y do
      y := y + 1
    northProfile := northProfile.set! xi y
  for xi in [0:width] do
    let mut y : Int := (height : Int) - 1
    while y >= 0 && !PolyominoLike.isBlocked poly xi y.toNat do
      y := y - 1
    southProfile := southProfile.set! xi y
  for yi in [0:height] do
    let mut x := 0
    while x < width && !PolyominoLike.isBlocked poly x yi do
      x := x + 1
    eastProfile := eastProfile.set! yi x
  for yi in [0:height] do
    let mut x : Int := (width : Int) - 1
    while x >= 0 && !PolyominoLike.isBlocked poly x.toNat yi do
      x := x - 1
    westProfile := westProfile.set! yi x
  let mut cells : Array (Nat × Nat) := #[]
  for xi in [0:width] do
    for yi in [0:height] do
      let xI : Int := xi
      let yI : Int := yi
      if xI < westProfile[yi]! && xI > eastProfile[yi]! && yI < southProfile[xi]! &&
          yI > northProfile[xi]! then
        cells := cells.push (xi, yi)
  if cells.isEmpty then return poly
  return PolyominoLike.modifyGrid poly fun g => cells.foldl (fun g (x, y) => g.setBlocked x y) g

end ProfileFill

end Elk.Alg.Common.Polyomino
