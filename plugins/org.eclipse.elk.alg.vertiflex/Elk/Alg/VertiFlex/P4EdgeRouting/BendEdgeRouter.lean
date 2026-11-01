import Elk.Core.Alg
import Elk.Core.Options
import Elk.Core.Util.Java
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.VertiFlex.VertiFlexLayoutPhases
import Elk.Alg.VertiFlex.VertiFlexUtil
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.vertiflex.p4edgerouting.BendEdgeRouter`

Port of `bend_edge_router.rs` (elk-rs): phase 4 of VertiFlex with `EdgeRoutingStrategy.BEND`.
Like the straight router, but an edge gets one bend point `(end_x, bend_height)` when the bend
height computed by the relative x placer (`EDGE_BEND_HEIGHT` of the child) differs from the
default of half the node spacing above the child.
-/

namespace Elk.Alg.VertiFlex.P4EdgeRouting

open Elk.Graph Elk.Core.Alg Elk.Core.Util Elk.Core.Options

namespace BendEdgeRouter

/-- `route_edges(node)`: edges in `all_outgoing_edges` order, depth first. -/
partial def routeEdges (node : NodeId) : VertiFlexM Unit := do
  let edges ← ElkM.withGraph fun g => ElkGraphUtil.allOutgoingEdges g node
  for edge in edges do
    let some target ← VertiFlexUtil.edgeTargetNode edge | continue
    let sec ← VertiFlexUtil.ensureSingleSection edge
    let n ← ElkM.getNode node
    let t ← ElkM.getNode target
    let startX := n.x + n.width / fl2p0
    let startY := n.y + n.height
    let endX := t.x + t.width / fl2p0
    let endY := t.y
    ElkM.modifySection sec fun s =>
      { s with startX := startX, startY := startY, endX := endX, endY := endY, bendPoints := #[] }
    let bendHeight := ((← VertiFlexM.getProps target).edgeBendHeight).getD endY
    let epsilon := fl0p0001
    let parentSpacing ← match t.parent with
      | some parent => do
        pure (((← ElkM.getNode parent).props.get CoreOptions.SPACING_NODE_NODE).getD fl0p0)
      | none => pure fl0p0
    if Float.abs (bendHeight - (endY - parentSpacing / fl2p0)) > epsilon then
      ElkM.modifySection sec fun s => { s with bendPoints := s.bendPoints.push ⟨endX, bendHeight⟩ }
    routeEdges target

/-- `process(graph, progress_monitor)`. -/
def process (graph : NodeId) (monitor : ProgressMonitor) : VertiFlexM Unit := do
  let _ ← monitor.begin "BendEdgeRouter" 1.0
  let hasChildren := !(← ElkM.getNode graph).children.isEmpty
  if hasChildren then
    if let some parent ← VertiFlexUtil.findRoot graph then
      routeEdges parent
  monitor.done

/-- The phase (`ILayoutPhase`) without a processor configuration. -/
def phase : VertiFlexPhase :=
  { name := "BendEdgeRouter"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure none }

end BendEdgeRouter

end Elk.Alg.VertiFlex.P4EdgeRouting
