import Elk.Alg.Common.Polyomino.Successor
/-!
# `org.eclipse.elk.alg.common.polyomino.SuccessorQuadrantsGeneric`

Restricts a cost function to the quadrants compatible with the extension directions of the
polyomino (elk-rs `successor_quadrants_generic.rs`): extensions only to the north forbid
`y >= 0`, only to the south forbid `y < 0`, only to the east forbid `x < 0`, only to the west
forbid `x >= 0`. Rust caches the quadrants per polyomino (keyed by its address); the cache is
derived from the polyomino alone, so the Lean version recomputes them on every call. The Rust
`HashSet<Direction>` is only queried for membership, so an array of directions is used.
-/
namespace Elk.Alg.Common.Polyomino

open Structures

namespace SuccessorQuadrantsGeneric

/-- Allowed quadrants `(posX, posY, negX, negY)` (Rust `update_quadrants`). -/
def quadrants {P : Type} [PolyominoLike P] (poly : P) : Bool × Bool × Bool × Bool := Id.run do
  let dirs := (PolyominoLike.polyominoExtensions poly).map (·.1)
  let mut posX := true
  let mut posY := true
  let mut negX := true
  let mut negY := true
  let containsPos := dirs.contains .north
  let containsNeg := dirs.contains .south
  if containsPos && !containsNeg then posY := false
  if !containsPos && containsNeg then negY := false
  let containsPos := dirs.contains .east
  let containsNeg := dirs.contains .west
  if containsPos && !containsNeg then negX := false
  if !containsPos && containsNeg then posX := false
  return (posX, posY, negX, negY)

end SuccessorQuadrantsGeneric

/-- `new SuccessorQuadrantsGeneric(costFun)`: applies `costFun` until the result lies in an
allowed quadrant. -/
def SuccessorQuadrantsGeneric {P : Type} [PolyominoLike P] (costFun : SuccessorFunction P) :
    SuccessorFunction P := fun coords poly => Id.run do
  let (posX, posY, negX, negY) := SuccessorQuadrantsGeneric.quadrants poly
  let mut next := costFun coords poly
  repeat
    let (newX, newY) := next
    let mut invalid := false
    if newX < 0 then
      if !negX then invalid := true
    else if !posX then invalid := true
    if newY < 0 then
      if !negY then invalid := true
    else if !posY then invalid := true
    if !invalid then return next
    next := costFun next poly
  return next

end Elk.Alg.Common.Polyomino
