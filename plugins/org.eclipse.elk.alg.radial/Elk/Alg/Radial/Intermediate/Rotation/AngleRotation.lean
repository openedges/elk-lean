import Elk.Graph
import Elk.Core.Math
import Elk.Core.Util.Java
import Elk.Alg.Radial.InternalProperties
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.Options.RadialOptions
import Elk.Alg.Radial.Intermediate.Rotation.IRadialRotator
/-!
# `org.eclipse.elk.alg.radial.intermediate.rotation.AngleRotation`

Port of `angle_rotation.rs` (elk-rs): rotates the node centers around the origin by the
`ROTATION_TARGET_ANGLE` of the graph; with `ROTATION_COMPUTE_ADDITIONAL_WEDGE_SPACE` the angle is
first corrected so that the wedge between the first and the last outgoing edge of the root is
centered on the target angle. Only the outgoing edges of the root node itself (not of its ports)
are considered; port targets are mapped to their parent node.
-/
namespace Elk.Alg.Radial.Intermediate.Rotation

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Radial.Options

namespace AngleRotation

/-- The node of the first target of an edge (`Node` itself, or the parent of a `Port`). -/
private def targetNodeOf (g : ElkGraph) (edge : EdgeId) : Option NodeId :=
  match (g.edge edge).targets[0]? with
  | some (ConnectableId.node n) => some n
  | some (ConnectableId.port p) => (g.port p).parent
  | none => none

/-- `rotate(graph)`. -/
def rotate (graph : NodeId) : RadialM Unit := do
  let props := (← ElkM.getNode graph).props
  let mut targetAngle := (props.get RadialOptions.ROTATION_TARGET_ANGLE).getD 0.0
  let computeAdditional := (props.get RadialOptions.ROTATION_COMPUTE_ADDITIONAL_WEDGE_SPACE).getD false
  if computeAdditional then
    if let some root ← RadialUtil.rootFromGraph graph then
      let g ← getGraph
      let outgoingEdges := (g.node root).outgoingEdges
      if !outgoingEdges.isEmpty then
        let lastEdge := outgoingEdges.back!
        let firstEdge := outgoingEdges[0]!
        if let (some lastNode, some firstNode) := (targetNodeOf g lastEdge, targetNodeOf g firstEdge) then
          let l := g.node lastNode
          let f := g.node firstNode
          let lastVector : KVector := ⟨l.x + l.width / 2.0, l.y + l.height / 2.0⟩
          let firstVector : KVector := ⟨f.x + f.width / 2.0, f.y + f.height / 2.0⟩
          let mut alpha := targetAngle
          if alpha <= 0.0 then alpha := alpha + 2.0 * Float.pi
          let mut wedgeAngle := lastVector.angle firstVector
          if wedgeAngle <= 0.0 then wedgeAngle := wedgeAngle + 2.0 * Float.pi
          let mut alignmentAngle := Float.atan2 lastVector.y lastVector.x
          if alignmentAngle <= 0.0 then alignmentAngle := alignmentAngle + 2.0 * Float.pi
          targetAngle := Float.pi - (alignmentAngle - alpha + wedgeAngle / 2.0)
  let children := (← ElkM.getNode graph).children
  for node in children do
    let n ← ElkM.getNode node
    let pos := (KVector.mk (n.x + n.width / 2.0) (n.y + n.height / 2.0)).rotate targetAngle
    ElkM.modifyNode node fun m => { m with x := pos.x - n.width / 2.0, y := pos.y - n.height / 2.0 }

/-- The `IRadialRotator` of this class. -/
def rotator : IRadialRotator := { rotate := rotate }

end AngleRotation

end Elk.Alg.Radial.Intermediate.Rotation
