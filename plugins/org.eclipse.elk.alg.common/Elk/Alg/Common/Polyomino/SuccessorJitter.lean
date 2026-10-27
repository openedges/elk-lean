import Elk.Alg.Common.Polyomino.Successor
/-!
# `org.eclipse.elk.alg.common.polyomino.SuccessorJitter`

Spiral-like traversal that jitters between the sides (elk-rs `successor_jitter.rs`).
-/
namespace Elk.Alg.Common.Polyomino

/-- `SuccessorJitter.apply(coords, poly)`. -/
def SuccessorJitter {P : Type} : SuccessorFunction P := fun (x, y) _ =>
  let cost := max (x.natAbs : Int) (y.natAbs : Int)
  if x <= 0 && x == y then (0, y - 1)
  else if x == -cost && y != cost then
    let nextX := if y >= 0 then y + 1 else y
    (nextX, x)
  else (-y, x)

end Elk.Alg.Common.Polyomino
