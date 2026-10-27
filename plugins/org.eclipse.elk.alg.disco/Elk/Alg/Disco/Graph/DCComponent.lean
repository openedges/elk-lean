import Elk.Core.Math.ElkRectangle
import Elk.Core.Util.Java
import Elk.Alg.Disco.Graph.DCElement
/-!
# `org.eclipse.elk.alg.disco.graph.DCComponent`

A connected component: a set of `DCElement`s with an offset (elk-rs `graph/dc_component.rs`).

Rust caches the bounding rectangle and the minimum corner (`changed`, `update()`) and invalidates
the cache in `set_offset`/`add_element`. The cached values are a pure function of the elements
and the offset (elements are never changed after the component was built), so the Lean port
recomputes them in `update` instead of caching: the results are identical. All functions that
read elements take the element arena `DCGraph.elements`.
-/
namespace Elk.Alg.Disco.Graph

open Elk.Core.Math Elk.Core.Util

/-- `DCComponent`: element ids, offset and debug id (`-1` = unassigned). -/
structure DCComponent where
  /-- `getOffset()`. -/
  offset : KVector := {}
  /-- `getElements()`. -/
  shapes : Array DCElementId := #[]
  /-- `getId()`. -/
  id : Int := -1
  deriving Inhabited

namespace DCComponent

/-- Widens the bounds `(minX, maxX, minY, maxY)` by an extension (Rust
`update_bounds_with_extension`): a horizontal extension widens the y range, a vertical one the x
range. -/
private def updateBoundsWithExtension (ext : DCExtension) (elemBounds : ElkRectangle)
    (minX maxX minY maxY : Float) : Float × Float × Float × Float :=
  if ext.direction.isHorizontal then
    let minPos := elemBounds.y + ext.offset.y
    let maxPos := minPos + ext.width
    (minX, maxX, fmin minY minPos, fmax maxY maxPos)
  else
    let minPos := elemBounds.x + ext.offset.x
    let maxPos := minPos + ext.width
    (fmin minX minPos, fmax maxX maxPos, minY, maxY)

/-- `update()`: the dimensions of the bounding rectangle and the minimum corner
(`min + offset`) of the component, including the element extensions. -/
def update (c : DCComponent) (elements : Array DCElement) : KVector × KVector := Id.run do
  let mut minX := Float.posInf
  let mut maxX := Float.negInf
  let mut minY := Float.posInf
  let mut maxY := Float.negInf
  for id in c.shapes do
    let elem := elements[id.idx]!
    let elemBounds := elem.bounds
    minX := fmin minX elemBounds.x
    maxX := fmax maxX (elemBounds.x + elemBounds.width)
    minY := fmin minY elemBounds.y
    maxY := fmax maxY (elemBounds.y + elemBounds.height)
    for ext in elem.extensions do
      (minX, maxX, minY, maxY) := updateBoundsWithExtension ext elemBounds minX maxX minY maxY
  return (KVector.mk' (maxX - minX) (maxY - minY), KVector.mk' (minX + c.offset.x) (minY + c.offset.y))

/-- `getDimensionsOfBoundingRectangle()`. -/
def dimensionsOfBoundingRectangle (c : DCComponent) (elements : Array DCElement) : KVector :=
  (c.update elements).1

/-- `getMinCorner()`: upper left corner including the current offset. -/
def minCorner (c : DCComponent) (elements : Array DCElement) : KVector :=
  (c.update elements).2

/-- `intersects(rect)`: some element intersects the rectangle. -/
def intersects (c : DCComponent) (elements : Array DCElement) (rect : ElkRectangle) : Bool :=
  c.shapes.any fun id => elements[id.idx]!.intersects rect

/-- `setOffset(offset)`. -/
def setOffset (c : DCComponent) (offset : KVector) : DCComponent := { c with offset }

/-- `addElement(element)`. -/
def addElement (c : DCComponent) (e : DCElementId) : DCComponent :=
  { c with shapes := c.shapes.push e }

/-- `setId(id)`. -/
def setId (c : DCComponent) (id : Int) : DCComponent := { c with id }

end DCComponent

end Elk.Alg.Disco.Graph
