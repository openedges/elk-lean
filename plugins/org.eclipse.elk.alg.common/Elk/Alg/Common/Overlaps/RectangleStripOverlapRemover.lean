import Elk.Graph.ArrayModify
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
import Elk.Alg.Common.Overlaps.OverlapRemovalDirection
import Elk.Alg.Common.Overlaps.GreedyRectangleStripOverlapRemover
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.common.overlaps.RectangleStripOverlapRemover`

Removes overlaps between rectangles that have a fixed position along one of the
two dimensions (elk-rs `overlaps/mod.rs`). A typical use case is to place
labels of northern ports that might not be placed such that there is enough
space for labels. The overlap removal direction, the gap and the start
coordinate are configured through the builder methods.

Rust mutates the caller's rectangles through raw pointers. The Lean remover
copies the rectangles in `addRectangle` and `removeOverlaps` returns the
updated rectangles in insertion order together with the strip size.
-/

namespace Elk.Alg.Common.Overlaps

open Elk.Core.Util Elk.Core.Math

/-- `org.eclipse.elk.alg.common.overlaps.RectangleStripOverlapRemover`. -/
structure RectangleStripOverlapRemover where
  /-- The direction in which overlaps are removed. -/
  overlapRemovalDirection : OverlapRemovalDirection
  /-- Vertical gap (default 5). -/
  gapVertical : Float := fl5p0
  /-- Horizontal gap (default 5). -/
  gapHorizontal : Float := fl5p0
  /-- Coordinate of the first rectangle encountered along the direction (default 0). -/
  startCoordinate : Float := fl0p0
  /-- The strategy (`none` = greedy). -/
  overlapRemovalStrategy : Option IRectangleStripOverlapRemovalStrategy := none
  /-- The rectangle nodes in insertion order (sorted by `removeOverlaps`). -/
  rectangleNodes : Array RectangleNode := #[]
  /-- Copies of the caller's rectangles (Rust raw pointers), in insertion order. -/
  originalRectangles : Array ElkRectangle := #[]
  deriving Inhabited

namespace RectangleStripOverlapRemover

/-- `createForDirection(direction)`. -/
def createForDirection (direction : OverlapRemovalDirection) : RectangleStripOverlapRemover :=
  { overlapRemovalDirection := direction }

/-- `withGap(horizontalGap, verticalGap)`. -/
def withGap (r : RectangleStripOverlapRemover) (horizontalGap verticalGap : Float) :
    RectangleStripOverlapRemover :=
  { r with gapHorizontal := horizontalGap, gapVertical := verticalGap }

/-- `withStartCoordinate(coordinate)`. -/
def withStartCoordinate (r : RectangleStripOverlapRemover) (coordinate : Float) :
    RectangleStripOverlapRemover :=
  { r with startCoordinate := coordinate }

/-- `withOverlapRemovalStrategy(strategy)`. -/
def withOverlapRemovalStrategy (r : RectangleStripOverlapRemover)
    (strategy : IRectangleStripOverlapRemovalStrategy) : RectangleStripOverlapRemover :=
  { r with overlapRemovalStrategy := some strategy }

/-- `getHorizontalGap()`. -/
@[inline] def horizontalGap (r : RectangleStripOverlapRemover) : Float := r.gapHorizontal

/-- `getVerticalGap()`. -/
@[inline] def verticalGap (r : RectangleStripOverlapRemover) : Float := r.gapVertical

/-- Rust `import_rectangle`: `UP`/`DOWN` keep the rectangle as is (Java even shares the
instance; elk-rs copies it, with the same result because `export_rectangle` reads the
strip coordinate before writing), `LEFT`/`RIGHT` swap the axes into
`(y, 0, height, width)`. -/
def importRectangle (r : RectangleStripOverlapRemover) (rectangle : ElkRectangle) : ElkRectangle :=
  match r.overlapRemovalDirection with
  | .up | .down => rectangle
  | .left | .right => ElkRectangle.ofValues rectangle.y 0.0 rectangle.height rectangle.width

/-- `addRectangle(rectangle)`. -/
def addRectangle (r : RectangleStripOverlapRemover) (rectangle : ElkRectangle) :
    RectangleStripOverlapRemover :=
  let node : RectangleNode :=
    { originalIndex := r.originalRectangles.size, rectangle := r.importRectangle rectangle }
  { r with rectangleNodes := r.rectangleNodes.push node,
           originalRectangles := r.originalRectangles.push rectangle }

/-- Rust `export_rectangle`: writes the strip coordinate back into the original rectangle. -/
def exportRectangle (r : RectangleStripOverlapRemover) (node : RectangleNode)
    (original : ElkRectangle) : ElkRectangle :=
  let rect := node.rectangle
  match r.overlapRemovalDirection with
  | .up => { original with y := r.startCoordinate - rect.height - rect.y }
  | .down => { original with y := rect.y + r.startCoordinate }
  | .left => { original with x := r.startCoordinate - rect.height - rect.y }
  | .right => { original with x := r.startCoordinate + rect.y }

/-- Key order of the Rust `BTreeSet<RightBorderKey>`: right border (`total_cmp`), then index. -/
private def rightBorderCmp (a b : Float × Nat) : Ordering :=
  match Float.compareTotal a.1 b.1 with
  | .eq => compare a.2 b.2
  | o => o

/-- A node with an empty overlap list; out of line so that `Array.map` hands it the unshared node
(PLAN 7.1 items 16, 59). -/
@[noinline] private def clearOverlaps (n : RectangleNode) : RectangleNode := { n with overlappingNodes := #[] }

/-- Rust `compute_overlaps`: scanline over the nodes (already sorted by x) that records,
for every pair whose x ranges intersect, each node in the other's `overlappingNodes`. The
active set is kept sorted by `(right border, index)` like the Rust `BTreeSet`. -/
def computeOverlaps (nodes : Array RectangleNode) : Array RectangleNode := Id.run do
  let mut nodes := nodes.map clearOverlaps
  let mut intersecting : Array (Float × Nat) := #[]
  for currentIndex in [0:nodes.size] do
    let some current := nodes[currentIndex]? | continue
    let scanlinePos := current.rectangle.x
    -- read before the updates below: a live `current` would make every update copy the node
    let rightBorder := current.rectangle.x + current.rectangle.width
    while true do
      match intersecting[0]? with
      | some first =>
        if first.1 < scanlinePos then
          intersecting := intersecting.eraseIdxIfInBounds 0
        else break
      | none => break
    for (_, otherIndex) in intersecting do
      nodes := nodes.modifyIn currentIndex fun n =>
        { n with overlappingNodes := n.overlappingNodes.push otherIndex }
      nodes := nodes.modifyIn otherIndex fun n =>
        { n with overlappingNodes := n.overlappingNodes.push currentIndex }
    let key := (rightBorder, currentIndex)
    let pos := (intersecting.findIdx? fun k => rightBorderCmp key k == .lt).getD intersecting.size
    intersecting := intersecting.insertIdxIfInBounds pos key
  return nodes

/-- `removeOverlaps()`: sorts the nodes by x (`total_cmp`, stable), computes overlaps, runs
the strategy (greedy if none was set) and exports the result. Returns the caller's
rectangles (insertion order) with their new coordinates and the strip size. -/
def removeOverlaps (r : RectangleStripOverlapRemover) : Array ElkRectangle × Float := Id.run do
  let strategy := r.overlapRemovalStrategy.getD GreedyRectangleStripOverlapRemover.strategy
  let nodes := stableSort r.rectangleNodes fun a b => Float.compareTotal a.rectangle.x b.rectangle.x
  let nodes := computeOverlaps nodes
  let (nodes, stripSize) := strategy.removeOverlaps r.gapHorizontal r.gapVertical nodes
  let mut originals := r.originalRectangles
  for node in nodes do
    originals := originals.modify node.originalIndex (r.exportRectangle node ·)
  return (originals, stripSize)

end RectangleStripOverlapRemover

end Elk.Alg.Common.Overlaps
