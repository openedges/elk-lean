import Elk.Alg.Common.Polyomino.Successor
/-!
# `org.eclipse.elk.alg.common.polyomino.SuccessorManhattan`

Traverses the diamonds of equal Manhattan distance around the origin (elk-rs
`successor_manhattan.rs`).
-/
namespace Elk.Alg.Common.Polyomino

/-- `SuccessorManhattan.apply(coords, poly)`. -/
def SuccessorManhattan {P : Type} : SuccessorFunction P := fun (x, y) _ =>
  if x == 0 && y == 0 then (x, y - 1)
  else if x == -1 && y <= 0 then (0, y - 2)
  else if x <= 0 && y > 0 then (x - 1, y - 1)
  else if x >= 0 && y < 0 then (x + 1, y + 1)
  else if x > 0 && y >= 0 then (x - 1, y + 1)
  else (x + 1, y - 1)

end Elk.Alg.Common.Polyomino
