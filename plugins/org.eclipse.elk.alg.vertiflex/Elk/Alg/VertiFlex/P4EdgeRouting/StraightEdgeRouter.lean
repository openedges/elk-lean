import Elk.Core.Alg
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.VertiFlex.VertiFlexLayoutPhases
import Elk.Alg.VertiFlex.VertiFlexUtil
/-!
# `org.eclipse.elk.alg.vertiflex.p4edgerouting.StraightEdgeRouter`

Port of `straight_edge_router.rs` (elk-rs): phase 4 of VertiFlex with `EdgeRoutingStrategy.STRAIGHT`.
Every tree edge becomes one section from the bottom centre of the parent to the top centre of
the child, without bend points.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl2p0 : Float := 2.0

namespace Elk.Alg.VertiFlex.P4EdgeRouting

open Elk.Graph Elk.Core.Alg Elk.Core.Util

namespace StraightEdgeRouter

/-- `route_edges(node)`: edges in `all_outgoing_edges` order, depth first. -/
partial def routeEdges (node : NodeId) : ElkM Unit := do
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
    routeEdges target

/-- `process(graph, progress_monitor)`. -/
def process (graph : NodeId) (monitor : ProgressMonitor) : VertiFlexM Unit := do
  let _ ← monitor.begin "StraightEdgeRouter" 1.0
  let hasChildren := !(← ElkM.getNode graph).children.isEmpty
  if hasChildren then
    if let some parent ← VertiFlexUtil.findRoot graph then
      routeEdges parent
  monitor.done

/-- The phase (`ILayoutPhase`) without a processor configuration. -/
def phase : VertiFlexPhase :=
  { name := "StraightEdgeRouter"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure none }

end StraightEdgeRouter

end Elk.Alg.VertiFlex.P4EdgeRouting
