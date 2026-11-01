import Elk.Graph
import Elk.Core.Alg
import Elk.Core.Math
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.Radial.InternalProperties
import Elk.Alg.Radial.RadialLayoutPhases
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.Intermediate.IntermediateProcessorStrategy
import Elk.Alg.Radial.P2Routing.IRadialEdgeRouter
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.radial.p2routing.StraightLineEdgeRouter`

Port of `straight_line_edge_router.rs` (elk-rs): phase 2 of the radial layout. Walks the tree
from the root and routes every non-hierarchical outgoing edge as a straight line between the
borders of source and target (each end clipped at the node box with `ElkMath.clipVector`).
The edge section is the first one of the edge (`ElkGraphUtil.firstEdgeSection` with reset and
removal of the other sections). Edges that leave a port are skipped; targets are visited
recursively in edge order (a node reachable twice is routed twice, with the same result).

The Rust geometry cache (`build_node_geom`) is a snapshot of the children taken before routing;
node boxes do not change in this phase, so the live boxes are used.
-/

namespace Elk.Alg.Radial.P2Routing

open Elk.Graph Elk.Core.Alg Elk.Core.Math Elk.Core.Util Elk.Alg.Radial.Intermediate

namespace StraightLineEdgeRouter

/-- `route_edges_cached(node, geom)`. -/
partial def routeEdges (node : NodeId) : ElkM Unit := do
  let edges ← ElkM.withGraph fun g => ElkGraphUtil.allOutgoingEdges g node
  for edge in edges do
    -- read-only snapshot: the geometry of the edge, none if the edge is skipped
    let info ← ElkM.withGraph fun g => Id.run do
      let e := g.edge edge
      let some sourceShape := e.sources[0]? | return none
      if sourceShape.isPort then return none
      let some targetShape := e.targets[0]? | return none
      let some target := ElkGraphUtil.connectableShapeToNode g targetShape | return none
      if ElkGraphUtil.isHierarchicalEdge g edge then return none
      let s := g.node node
      let t := g.node target
      return some (target, s.x + s.width / fl2p0, s.y + s.height / fl2p0, s.width, s.height,
        t.x + t.width / fl2p0, t.y + t.height / fl2p0, t.width, t.height)
    let some (target, sx, sy, nodeWidth, nodeHeight, tx, ty, targetWidth, targetHeight) := info
      | continue
    let mut sourceX := sx
    let mut sourceY := sy
    let mut targetX := tx
    let mut targetY := ty
    let mut vector : KVector := ⟨targetX - sourceX, targetY - sourceY⟩
    let sourceClip := ElkMath.clipVector vector nodeWidth nodeHeight
    vector := ⟨vector.x - sourceClip.x, vector.y - sourceClip.y⟩
    sourceX := targetX - vector.x
    sourceY := targetY - vector.y
    let targetClip := ElkMath.clipVector vector targetWidth targetHeight
    vector := ⟨vector.x - targetClip.x, vector.y - targetClip.y⟩
    targetX := sourceX + vector.x
    targetY := sourceY + vector.y
    let sec ← modifyGet fun g =>
      let (g, s) := ElkGraphUtil.firstEdgeSection g edge true true
      (s, g)
    ElkM.modifySection sec fun s =>
      { s with startX := sourceX, startY := sourceY, endX := targetX, endY := targetY }
    routeEdges target

/-- The `IRadialEdgeRouter` of this class. -/
def router : IRadialEdgeRouter := { routeEdges := routeEdges }

/-- `process(graph, progress_monitor)`. -/
def process (graph : NodeId) (monitor : ProgressMonitor) : RadialM Unit := do
  let _ ← monitor.begin "Straight Line Edge Routing" 1.0
  if ← monitor.isLoggingEnabled then monitor.logGraph "Before"
  if let some root ← RadialUtil.rootFromGraph graph then
    routeEdges root
  if ← monitor.isLoggingEnabled then monitor.logGraph "After"
  monitor.done

/-- The phase (`ILayoutPhase`) with no processor configuration. -/
def phase : LayoutPhase RadialM RadialLayoutPhases NodeId IntermediateProcessorStrategy :=
  { name := "StraightLineEdgeRouter"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure none }

end StraightLineEdgeRouter

end Elk.Alg.Radial.P2Routing
