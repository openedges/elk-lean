import Elk.Alg.Layered.LayeredPhases
import Elk.Core.Options
/-! # `org.eclipse.elk.alg.layered.p5edges.EdgeRouterFactory`

Maps `EdgeRouting` to the edge router phase: `POLYLINE` → `PolylineEdgeRouter`, `SPLINES` →
`SplineEdgeRouter`, everything else → `OrthogonalEdgeRouter`. The routers register through
`LayeredPhases.registerPhase .p5EdgeRouting (ordinal of the EdgeRouting constant)`. Like the Rust
factory (no enum ordinal), the factory is not cached by the assembler. -/
namespace Elk.Alg.Layered.P5Edges

open Elk.Graph Elk.Core.Options Elk.Alg.Layered

/-- `EdgeRouterFactory.factoryFor(edgeRouting)`. -/
def EdgeRouterFactory.factoryFor (edgeRouting : EdgeRouting) : LayeredPhaseFactory :=
  let routing := match edgeRouting with
    | .polyline => EdgeRouting.polyline
    | .splines => EdgeRouting.splines
    | _ => EdgeRouting.orthogonal
  { key := none
    create := (LayeredPhases.strategyFactory .p5EdgeRouting "EdgeRouting" (ElkEnum.ordinal routing) (ElkEnum.javaName routing)).create }

end Elk.Alg.Layered.P5Edges
