import Elk.Alg.Common.Polyomino.Successor
/-!
# `org.eclipse.elk.alg.common.polyomino.SuccessorLineByLine`

Traverses the square rings around the origin line by line (elk-rs
`successor_line_by_line.rs`).
-/
namespace Elk.Alg.Common.Polyomino

/-- `SuccessorLineByLine.apply(coords, poly)`. -/
def SuccessorLineByLine {P : Type} : SuccessorFunction P := fun (x, y) _ =>
  if x >= 0 && x == y then (-x - 1, -x - 1)
  else if x >= 0 && x == -y then (-x, y + 1)
  else if x.natAbs > y.natAbs then
    if x < 0 then (-x, y) else (-x, y + 1)
  else (x + 1, y)

end Elk.Alg.Common.Polyomino
