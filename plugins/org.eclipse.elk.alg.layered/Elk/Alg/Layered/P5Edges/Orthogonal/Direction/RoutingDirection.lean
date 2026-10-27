import Elk.Graph
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.direction.RoutingDirection`

Port of elk-rs `p5edges/orthogonal/direction/routing_direction.rs`: the direction in which the
`OrthogonalRoutingGenerator` routes edges (west to east for the main edge router, north to south /
south to north for the external north/south port edges of the hierarchical port router).
-/
namespace Elk.Alg.Layered.P5Edges.Orthogonal.Direction

/-- `RoutingDirection` (Java ordinal order: `WEST_TO_EAST`, `NORTH_TO_SOUTH`, `SOUTH_TO_NORTH`). -/
elk_enum RoutingDirection := westToEast northToSouth southToNorth

end Elk.Alg.Layered.P5Edges.Orthogonal.Direction
