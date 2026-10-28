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
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl2p0 : Float := 2.0

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
  let mut targetAngle := (props.get RadialOptions.ROTATION_TARGET_ANGLE).getD fl0p0
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
          let lastVector : KVector := ⟨l.x + l.width / fl2p0, l.y + l.height / fl2p0⟩
          let firstVector : KVector := ⟨f.x + f.width / fl2p0, f.y + f.height / fl2p0⟩
          let mut alpha := targetAngle
          if alpha <= fl0p0 then alpha := alpha + fl2p0 * Float.pi
          -- Java `KVector.angle`: `Math.acos(dot / (|a| * |b|))` (fdlibm)
          let mut wedgeAngle := javaAcos (lastVector.dotProduct firstVector / (lastVector.length * firstVector.length))
          if wedgeAngle <= fl0p0 then wedgeAngle := wedgeAngle + fl2p0 * Float.pi
          let mut alignmentAngle := javaAtan2 lastVector.y lastVector.x
          if alignmentAngle <= fl0p0 then alignmentAngle := alignmentAngle + fl2p0 * Float.pi
          targetAngle := Float.pi - (alignmentAngle - alpha + wedgeAngle / fl2p0)
  let children := (← ElkM.getNode graph).children
  for node in children do
    let n ← ElkM.getNode node
    -- Java `KVector.rotate` with the reference JVM's `Math.cos`/`Math.sin`
    let v := KVector.mk (n.x + n.width / fl2p0) (n.y + n.height / fl2p0)
    let pos : KVector := ⟨v.x * javaCos targetAngle - v.y * javaSin targetAngle,
      v.x * javaSin targetAngle + v.y * javaCos targetAngle⟩
    ElkM.modifyNode node fun m => { m with x := pos.x - n.width / fl2p0, y := pos.y - n.height / fl2p0 }

/-- The `IRadialRotator` of this class. -/
def rotator : IRadialRotator := { rotate := rotate }

end AngleRotation

end Elk.Alg.Radial.Intermediate.Rotation
