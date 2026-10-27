import Elk.Alg.Common.Compaction.OneD.IConstraintCalculationAlgorithm
import Elk.Alg.Common.Compaction.OneD.CompareFuzzy
/-!
# `org.eclipse.elk.alg.common.compaction.oned.QuadraticConstraintCalculation`

Quadratic constraint calculation (elk-rs `quadratic_constraint_calculation.rs`): every pair
of nodes of different groups whose hitboxes overlap in the orthogonal dimension (including
spacing) gets a constraint from the left node to the right node.
-/
namespace Elk.Alg.Common.Compaction.OneD

open CompactM

namespace QuadraticConstraintCalculation

/-- `QuadraticConstraintCalculation.calculateConstraints(compactor)`. -/
def calculateConstraints : CompactM Unit := do
  let cNodes ← cNodeIds
  for n in cNodes do
    modifyCNode n fun c => { c with constraints := #[] }
  let dir ← direction
  for cNode1 in cNodes do
    for cNode2 in cNodes do
      if cNode1 == cNode2 then continue
      let n1 ← getCNode cNode1
      let n2 ← getCNode cNode2
      let sameGroup :=
        match n1.cGroup, n2.cGroup with
        | some g1, some g2 => g1 == g2
        | _, _ => false
      if sameGroup then continue
      let spacing ←
        if dir.isHorizontal then verticalSpacing cNode1 cNode2 else horizontalSpacing cNode1 cNode2
      let toTheRight := n2.hitbox.x > n1.hitbox.x ||
        (CompareFuzzy.eq n1.hitbox.x n2.hitbox.x && n1.hitbox.width < n2.hitbox.width)
      let overlapLow := CompareFuzzy.gt (n2.hitbox.y + n2.hitbox.height + spacing) n1.hitbox.y
      let overlapHigh := CompareFuzzy.lt n2.hitbox.y (n1.hitbox.y + n1.hitbox.height + spacing)
      if toTheRight && overlapLow && overlapHigh then
        modifyCNode cNode1 fun c => { c with constraints := c.constraints.push cNode2 }

end QuadraticConstraintCalculation

/-- `new QuadraticConstraintCalculation()`. -/
def QuadraticConstraintCalculation : ConstraintCalculationAlgorithm :=
  ⟨QuadraticConstraintCalculation.calculateConstraints⟩

end Elk.Alg.Common.Compaction.OneD
