import Elk.Alg.Common.Geometry.BowyerWatsonTriangulation
import Elk.Alg.Spore.SporePhases
/-!
# `org.eclipse.elk.alg.spore.p1structure.DelaunayTriangulationPhase`

Port of `p1structure/delaunay_triangulation_phase.rs` (elk-rs) and `DelaunayTriangulationPhase.java`:
creates a Delaunay triangulation of the vertices' `originalVertex` positions with
`BowyerWatsonTriangulation` and stores its edges in `Graph.tEdges`. If the graph already has edges
(the scanline overlap check of `OverlapRemovalLayoutProvider` stores some), the triangulation edges
are added to them (`HashSet::extend`: insertion-ordered, duplicates dropped, see
`TEdge.extendUnique`). The SVG debug output is not ported (TODO(debug)).
-/
namespace Elk.Alg.Spore.P1Structure

open Elk.Core.Alg Elk.Core.Util Elk.Alg.Common Elk.Alg.Spore.Graph

namespace DelaunayTriangulationPhase

/-- `process(graph, progressMonitor)`: the Delaunay triangulation phase. -/
def process (_graph : Unit) (monitor : ProgressMonitor) : SporeM Unit := do
  let _ ← monitor.begin "Delaunay triangulation" 1.0
  modify fun g =>
    let vertices := g.vertices.map (·.originalVertex)
    let edges := BowyerWatsonTriangulation.triangulate vertices
    { g with tEdges := some (match g.tEdges with
        | some existing => TEdge.extendUnique existing edges
        | none => edges) }
  monitor.done

/-- The `DelaunayTriangulationPhase` phase (no intermediate processors). -/
def phase : SporePhase :=
  { name := "DelaunayTriangulationPhase", process := process,
    getLayoutProcessorConfiguration := fun _ => noProcessors }

end DelaunayTriangulationPhase

end Elk.Alg.Spore.P1Structure
