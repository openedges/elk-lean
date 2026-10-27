import Elk.Graph
import Elk.Core.Math
import Elk.Alg.Radial.Intermediate.Optimization.IEvaluation
/-!
# `org.eclipse.elk.alg.radial.intermediate.optimization.EdgeLengthOptimization`

Port of `edge_length_optimization.rs` (elk-rs): the sum of the lengths of the straight edges from
the root to its direct successors, clipped at the node borders.
-/
namespace Elk.Alg.Radial.Intermediate.Optimization

open Elk.Graph Elk.Core.Math

namespace EdgeLengthOptimization

/-- `evaluate(root)`. -/
def evaluate (root : NodeId) : ElkM Float := do
  let g ← get
  let r := g.node root
  let rootCx := r.x + r.width / 2.0
  let rootCy := r.y + r.height / 2.0
  let mut edgeLength := 0.0
  for edge in ElkGraphUtil.allOutgoingEdges g root do
    let some targetShape := (g.edge edge).targets[0]? | continue
    let some target := ElkGraphUtil.connectableShapeToNode g targetShape | continue
    let t := g.node target
    let targetCx := t.x + t.width / 2.0
    let targetCy := t.y + t.height / 2.0
    let mut vector : KVector := ⟨targetCx - rootCx, targetCy - rootCy⟩
    let sourceClip := ElkMath.clipVector vector r.width r.height
    vector := ⟨vector.x - sourceClip.x, vector.y - sourceClip.y⟩
    let rootX := targetCx - vector.x
    let rootY := targetCy - vector.y
    let targetClip := ElkMath.clipVector vector t.width t.height
    vector := ⟨vector.x - targetClip.x, vector.y - targetClip.y⟩
    let targetX := rootX + vector.x
    let targetY := rootY + vector.y
    let vectorX := targetX - rootX
    let vectorY := targetY - rootY
    edgeLength := edgeLength + Float.sqrt (vectorX * vectorX + vectorY * vectorY)
  return edgeLength

/-- The `IEvaluation` of this class. -/
def evaluation : IEvaluation := { evaluate := evaluate }

end EdgeLengthOptimization

end Elk.Alg.Radial.Intermediate.Optimization
