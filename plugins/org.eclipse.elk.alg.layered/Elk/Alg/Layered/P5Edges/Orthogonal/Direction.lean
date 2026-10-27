import Elk.Alg.Layered.P5Edges.Orthogonal.Direction.RoutingDirection
import Elk.Alg.Layered.P5Edges.Orthogonal.Direction.BaseRoutingDirectionStrategy
import Elk.Alg.Layered.P5Edges.Orthogonal.Direction.WestToEastRoutingStrategy
import Elk.Alg.Layered.P5Edges.Orthogonal.Direction.NorthToSouthRoutingStrategy
import Elk.Alg.Layered.P5Edges.Orthogonal.Direction.SouthToNorthRoutingStrategy
/-!
# `org.eclipse.elk.alg.layered.p5edges.orthogonal.direction`

Aggregator of the routing direction strategies, plus the factory
`BaseRoutingDirectionStrategy.forRoutingDirection` (a static method of the Java base class; it needs
the three implementations, which import the base module).
-/
namespace Elk.Alg.Layered.P5Edges.Orthogonal.Direction

/-- `BaseRoutingDirectionStrategy.forRoutingDirection(direction)` (Rust
`RoutingDirectionStrategy::for_routing_direction`). -/
def BaseRoutingDirectionStrategy.forRoutingDirection : RoutingDirection → BaseRoutingDirectionStrategy
  | .westToEast => WestToEastRoutingStrategy.strategy
  | .northToSouth => NorthToSouthRoutingStrategy.strategy
  | .southToNorth => SouthToNorthRoutingStrategy.strategy

end Elk.Alg.Layered.P5Edges.Orthogonal.Direction
