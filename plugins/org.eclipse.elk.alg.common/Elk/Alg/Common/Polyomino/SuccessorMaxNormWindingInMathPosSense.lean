import Elk.Alg.Common.Polyomino.Successor
/-!
# `org.eclipse.elk.alg.common.polyomino.SuccessorMaxNormWindingInMathPosSense`

Spiral around the origin along the rings of equal maximum norm, counter-clockwise (elk-rs
`successor_max_norm_winding_in_math_pos_sense.rs`).
-/
namespace Elk.Alg.Common.Polyomino

/-- `SuccessorMaxNormWindingInMathPosSense.apply(coords, poly)`. -/
def SuccessorMaxNormWindingInMathPosSense {P : Type} : SuccessorFunction P := fun (x, y) _ =>
  let cost := max (x.natAbs : Int) (y.natAbs : Int)
  if x < cost && y == -cost then (x + 1, y)
  else if x == cost && y < cost then (x, y + 1)
  else if x >= -cost && y == cost then (x - 1, y)
  else (x, y - 1)

end Elk.Alg.Common.Polyomino
