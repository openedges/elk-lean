import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.disco.graph.DCDirection`

Direction of an edge extension (elk-rs `graph/dc_direction.rs`). Declaration order = Java ordinal
order.
-/
namespace Elk.Alg.Disco.Graph

/-- `org.eclipse.elk.alg.disco.graph.DCDirection`. -/
elk_enum DCDirection := north east south west

namespace DCDirection

/-- `DCDirection.isHorizontal()`: `EAST` and `WEST`. -/
def isHorizontal : DCDirection → Bool
  | .east | .west => true
  | _ => false

end DCDirection

end Elk.Alg.Disco.Graph
