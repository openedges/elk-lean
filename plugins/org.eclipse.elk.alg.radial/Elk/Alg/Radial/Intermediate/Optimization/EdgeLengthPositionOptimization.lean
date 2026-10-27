import Elk.Graph
import Elk.Core.Options
import Elk.Alg.Radial.Intermediate.Optimization.IEvaluation
/-!
# `org.eclipse.elk.alg.radial.intermediate.optimization.EdgeLengthPositionOptimization`

Port of `edge_length_position_optimization.rs` (elk-rs): the sum of the distances between the
center of every direct successor of the root and the point
`(root.x + position.x + root.width / 2, root.y + position.y + root.height)`, where `position` is
the `POSITION` property of the successor (`(0, 0)` if unset).
-/
namespace Elk.Alg.Radial.Intermediate.Optimization

open Elk.Graph Elk.Core.Options

namespace EdgeLengthPositionOptimization

/-- `evaluate(root)`. -/
def evaluate (root : NodeId) : ElkM Float := do
  let g ← get
  let r := g.node root
  let mut edgeLength := 0.0
  for edge in ElkGraphUtil.allOutgoingEdges g root do
    let some targetShape := (g.edge edge).targets[0]? | continue
    let some target := ElkGraphUtil.connectableShapeToNode g targetShape | continue
    let t := g.node target
    let targetX := t.x + t.width / 2.0
    let targetY := t.y + t.height / 2.0
    let position := (t.props.get CoreOptions.POSITION).getD ⟨0.0, 0.0⟩
    let rootX := r.x + position.x + r.width / 2.0
    let rootY := r.y + position.y + r.height
    let vectorX := targetX - rootX
    let vectorY := targetY - rootY
    edgeLength := edgeLength + Float.sqrt (vectorX * vectorX + vectorY * vectorY)
  return edgeLength

/-- The `IEvaluation` of this class. -/
def evaluation : IEvaluation := { evaluate := evaluate }

end EdgeLengthPositionOptimization

end Elk.Alg.Radial.Intermediate.Optimization
