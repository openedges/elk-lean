import Elk.Alg.Common.Polyomino.Successor
/-!
# `org.eclipse.elk.alg.common.polyomino.SuccessorCombination`

Uses `normalFun` for polyominoes without extensions and `externalFun` otherwise (elk-rs
`successor_combination.rs`).
-/
namespace Elk.Alg.Common.Polyomino

open Structures

/-- `new SuccessorCombination(normalFun, externalFun)`. -/
def SuccessorCombination {P : Type} [PolyominoLike P] (normalFun externalFun : SuccessorFunction P) :
    SuccessorFunction P := fun coords poly =>
  if (PolyominoLike.polyominoExtensions poly).isEmpty then normalFun coords poly
  else externalFun coords poly

end Elk.Alg.Common.Polyomino
