import Elk.Alg.Layered.Graph
/-!
# `org.eclipse.elk.alg.layered.p3order.counting.CrossMinUtil`

elk-rs `cross_min_util.rs`.
-/
namespace Elk.Alg.Layered.P3Order.Counting

open Elk.Core.Options Elk.Alg.Layered.Graph

namespace CrossMinUtil

/-- `inNorthSouthEastWestOrder(node, side)`: the node's ports on `side` (`getPortSideView`)
ordered north→south on the east/west sides and west→east on the north/south sides, i.e.
`EAST`/`NORTH` as stored, `SOUTH`/`WEST` reversed; `UNDEFINED` yields no ports. -/
def inNorthSouthEastWestOrder (a : LGraphArena) (node : LNodeId) (side : PortSide) : Array LPortId :=
  match side with
  | .east | .north => a.nodePortSideView node side
  | .south | .west => (a.nodePortSideView node side).reverse
  | .undefined => #[]

end CrossMinUtil

end Elk.Alg.Layered.P3Order.Counting
