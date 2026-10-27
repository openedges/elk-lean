import Elk.Core.Math.ElkMath
import Elk.Alg.Common.Spore.InternalProperties
import Elk.Alg.Common.Utils.Utils
/-!
# `org.eclipse.elk.alg.common.spore.Node`

A node of the SPOrE graph: the original center position, the current center
position and the node's rectangle (elk-rs `spore/node.rs`). Plain value; the
"mutating" methods return the new node.
-/
namespace Elk.Alg.Common.Spore

open Elk.Core.Util Elk.Core.Math Elk.Alg.Common.Utils

/-- `org.eclipse.elk.alg.common.spore.Node` (Rust `Node`). -/
structure Node where
  /-- The center position the node had when it was created. -/
  originalVertex : KVector
  /-- The current center position. -/
  vertex : KVector
  /-- The node's bounding rectangle. -/
  rect : ElkRectangle
  deriving Repr, Inhabited

namespace Node

/-- `Node::new(vertex, rect)`: `originalVertex = vertex`. -/
@[inline] def new (vertex : KVector) (rect : ElkRectangle) : Node := ⟨vertex, vertex, rect⟩

/-- `translate(v)`: moves the center and the rectangle by `v`. -/
def translate (n : Node) (v : KVector) : Node :=
  { n with vertex := n.vertex + v, rect := { n.rect with x := n.rect.x + v.x, y := n.rect.y + v.y } }

/-- `setCenterPosition(p)`: translates by `p - vertex`. -/
def setCenterPosition (n : Node) (p : KVector) : Node := n.translate (p - n.vertex)

/-- `underlap(other)`: the length of the part of the center connection that lies between
the two rectangles. -/
def underlap (n other : Node) : Float := Id.run do
  let horizontalCenterDistance := (n.rect.center.x - other.rect.center.x).abs
  let verticalCenterDistance := (n.rect.center.y - other.rect.center.y).abs
  let mut hScale := 1.0
  let mut vScale := 1.0
  if horizontalCenterDistance > n.rect.width / 2.0 + other.rect.width / 2.0 then
    let horizontalUnderlap := fmin (n.rect.x - (other.rect.x + other.rect.width)).abs
      (n.rect.x + n.rect.width - other.rect.x).abs
    hScale := 1.0 - horizontalUnderlap / horizontalCenterDistance
  if verticalCenterDistance > n.rect.height / 2.0 + other.rect.height / 2.0 then
    let verticalUnderlap := fmin (n.rect.y - (other.rect.y + other.rect.height)).abs
      (n.rect.y + n.rect.height - other.rect.y).abs
    vScale := 1.0 - verticalUnderlap / verticalCenterDistance
  let scale := fmin hScale vScale
  return (1.0 - scale) * Float.sqrt (horizontalCenterDistance * horizontalCenterDistance
    + verticalCenterDistance * verticalCenterDistance)

/-- `distance(other, v)`: minimal `ElkMath.distance` between the rectangle edges of both
nodes along `v` (`+∞` if none hits). -/
def distance (n other : Node) (v : KVector) : Float := Id.run do
  let mut result := Float.posInf
  for e1 in Utils.getRectEdges n.rect do
    for e2 in Utils.getRectEdges other.rect do
      result := fmin result (ElkMath.distance e1.u e1.v e2.u e2.v v)
  return result

/-- `touches(other)`: the rectangles overlap or touch (fuzzy, `InternalProperties.FUZZINESS`). -/
def touches (n other : Node) : Bool :=
  let f := InternalProperties.FUZZINESS
  InternalProperties.fuzzyCompare n.rect.x (other.rect.x + other.rect.width) f <= 0
    && InternalProperties.fuzzyCompare other.rect.x (n.rect.x + n.rect.width) f <= 0
    && InternalProperties.fuzzyCompare n.rect.y (other.rect.y + other.rect.height) f <= 0
    && InternalProperties.fuzzyCompare other.rect.y (n.rect.y + n.rect.height) f <= 0

end Node

end Elk.Alg.Common.Spore
