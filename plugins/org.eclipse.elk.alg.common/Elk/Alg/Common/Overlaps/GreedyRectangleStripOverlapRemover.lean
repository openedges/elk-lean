import Elk.Core.Util.Java
import Elk.Core.Util.Sort
import Elk.Alg.Common.Overlaps.IRectangleStripOverlapRemovalStrategy
/-!
# `org.eclipse.elk.alg.common.overlaps.GreedyRectangleStripOverlapRemover`

Removes rectangle overlaps by greedily choosing the smallest y position that
won't cause overlaps. Fast algorithm, but not necessarily optimal in terms of
resulting rectangle strip size (elk-rs `GreedyRectangleStripOverlapRemover`).
-/
namespace Elk.Alg.Common.Overlaps

open Elk.Core.Util

namespace GreedyRectangleStripOverlapRemover

/-- `GreedyRectangleStripOverlapRemover.removeOverlaps(overlapRemover)`: nodes are placed in
order; each node's overlapping, already placed nodes are visited by ascending y
(`total_cmp`, stable) and the node is pushed below every one it would collide with. -/
def removeOverlaps (_horizontalGap verticalGap : Float) (nodes : Array RectangleNode) :
    Array RectangleNode × Float := Id.run do
  let mut nodes := nodes
  let mut alreadyPlaced : Array Bool := Array.replicate nodes.size false
  let mut stripSize : Float := 0.0
  for nodeIndex in [0:nodes.size] do
    let some node := nodes[nodeIndex]? | continue
    let currHeight := node.rectangle.height
    let keyed : Array (Nat × Float) := node.overlappingNodes.map fun i =>
      (i, (nodes[i]?.map (·.rectangle.y)).getD 0.0)
    let overlaps := (stableSort keyed fun a b => Float.compareTotal a.2 b.2).map (·.1)
    let mut yPos := 0.0
    for overlapIndex in overlaps do
      if !(alreadyPlaced[overlapIndex]?.getD false) then continue
      let some other := nodes[overlapIndex]? | continue
      let overlapRect := other.rectangle
      if yPos < overlapRect.y + overlapRect.height + verticalGap
          && yPos + currHeight + verticalGap > overlapRect.y then
        yPos := overlapRect.y + overlapRect.height + verticalGap
    nodes := nodes.modify nodeIndex fun n => { n with rectangle := { n.rectangle with y := yPos } }
    alreadyPlaced := alreadyPlaced.setIfInBounds nodeIndex true
    stripSize := fmax stripSize (yPos + currHeight)
  return (nodes, stripSize)

/-- The greedy strategy as an `IRectangleStripOverlapRemovalStrategy`. -/
def strategy : IRectangleStripOverlapRemovalStrategy := ⟨removeOverlaps⟩

end GreedyRectangleStripOverlapRemover

end Elk.Alg.Common.Overlaps
