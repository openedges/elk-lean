import Elk.Graph.Enum
/-!
# `org.eclipse.elk.core.options.Direction`
-/
namespace Elk.Core.Options

/-- `org.eclipse.elk.core.options.Direction`: main layout direction. -/
elk_enum Direction := undefined right left down up

namespace Direction

/-- `Direction.isHorizontal()`. -/
def isHorizontal : Direction → Bool
  | .left | .right => true
  | _ => false

/-- `Direction.isVertical()`. -/
def isVertical : Direction → Bool
  | .up | .down => true
  | _ => false

/-- `Direction.opposite()`. -/
def opposite : Direction → Direction
  | .left => .right
  | .right => .left
  | .up => .down
  | .down => .up
  | .undefined => .undefined

end Direction

end Elk.Core.Options
