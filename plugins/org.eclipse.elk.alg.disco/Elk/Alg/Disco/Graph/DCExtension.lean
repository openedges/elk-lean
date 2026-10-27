import Elk.Core.Math.ElkRectangle
import Elk.Alg.Disco.Graph.DCDirection
/-!
# `org.eclipse.elk.alg.disco.graph.DCExtension`

An extension of a `DCElement`: an edge segment that leads from the element to the border of the
parent graph (elk-rs `graph/dc_extension.rs`).
-/
namespace Elk.Alg.Disco.Graph

open Elk.Core.Math

/-- `DCExtension`: direction, offset relative to the upper left corner of the element and width. -/
structure DCExtension where
  /-- `getDirection()`. -/
  direction : DCDirection
  /-- `getOffset()`. -/
  offset : KVector
  /-- `getWidth()`. -/
  width : Float
  deriving Inhabited

namespace DCExtension

/-- `new DCExtension(parentBounds, direction, middlePos, width)`: the offset is
`(-parentBounds.x, -parentBounds.y) + middlePos` shifted by half the width perpendicular to the
direction. -/
def new (parentBounds : ElkRectangle) (direction : DCDirection) (middlePos : KVector)
    (width : Float) : DCExtension :=
  let offset := (KVector.mk' (-parentBounds.x) (-parentBounds.y)).add middlePos
  let halfWidth := width / 2.0
  let offset :=
    if direction.isHorizontal then offset.subValues 0.0 halfWidth
    else offset.subValues halfWidth 0.0
  { direction, offset, width }

end DCExtension

end Elk.Alg.Disco.Graph
