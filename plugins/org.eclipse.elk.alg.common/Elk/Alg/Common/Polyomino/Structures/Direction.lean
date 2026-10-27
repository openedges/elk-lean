import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.common.polyomino.structures.Direction`

The four cardinal directions of polyomino extensions (elk-rs `structures/direction.rs`). Not
to be confused with the core layout `Elk.Core.Options.Direction`.
-/
namespace Elk.Alg.Common.Polyomino.Structures

/-- `org.eclipse.elk.alg.common.polyomino.structures.Direction`. -/
elk_enum Direction := north east south west

namespace Direction

/-- `Direction.isHorizontal()`: `EAST` and `WEST`. -/
def isHorizontal : Direction → Bool
  | .east | .west => true
  | _ => false

end Direction

end Elk.Alg.Common.Polyomino.Structures
