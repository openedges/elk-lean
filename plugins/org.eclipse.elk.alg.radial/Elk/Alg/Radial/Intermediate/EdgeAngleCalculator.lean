import Elk.Graph
import Elk.Core.Alg
import Elk.Core.Math
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.Radial.InternalProperties
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.Options.RadialOptions
/-!
# `org.eclipse.elk.alg.radial.intermediate.EdgeAngleCalculator`

Port of `edge_angle_calculator.rs` (elk-rs): stores the angle of every outgoing edge of the root
(the direction of its first section) as `ROTATION_TARGET_ANGLE` of the edge target (node or port).
Only the outgoing edges of the root node itself (not of its ports) are considered.
-/
namespace Elk.Alg.Radial.Intermediate

open Elk.Graph Elk.Core.Alg Elk.Core.Math Elk.Core.Util Elk.Alg.Radial.Options

namespace EdgeAngleCalculator

/-- `process(graph, progress_monitor)`. -/
def process (graph : NodeId) (_monitor : ProgressMonitor) : RadialM Unit := do
  let some root ← RadialUtil.rootFromGraph graph | return
  let outgoingEdges := (← ElkM.getNode root).outgoingEdges
  for edge in outgoingEdges do
    let e ← ElkM.getEdge edge
    let some sectionId := e.sections[0]? | continue
    let sec ← ElkM.getSection sectionId
    let edgeVector := KVector.fromPoints ⟨sec.startX, sec.startY⟩ ⟨sec.endX, sec.endY⟩
    let angle := Float.atan2 edgeVector.y edgeVector.x
    let some targetShape := e.targets[0]? | continue
    match targetShape with
    | .node node => ElkM.setNodeProp node RadialOptions.ROTATION_TARGET_ANGLE angle
    | .port port => ElkM.modifyPort port fun p => { p with props := p.props.set RadialOptions.ROTATION_TARGET_ANGLE angle }

/-- The processor (`ILayoutProcessor`). -/
def processor : LayoutProcessor RadialM NodeId :=
  { name := "EdgeAngleCalculator", process := process }

end EdgeAngleCalculator

end Elk.Alg.Radial.Intermediate
