import Elk.Alg.Common.Overlaps.RectangleNode
/-!
# `org.eclipse.elk.alg.common.overlaps.IRectangleStripOverlapRemovalStrategy`

Classes implementing this interface know how to remove overlaps between a strip
of rectangles (elk-rs trait `RectangleStripOverlapRemovalStrategy`).

Java/Rust pass the whole `RectangleStripOverlapRemover`; the strategy only reads
its gaps and reads/writes its rectangle nodes. To avoid a cyclic structure the
Lean strategy receives exactly that data and returns the updated nodes.
-/
namespace Elk.Alg.Common.Overlaps

/-- `IRectangleStripOverlapRemovalStrategy` as a closure structure. -/
structure IRectangleStripOverlapRemovalStrategy where
  /-- `removeOverlaps(overlapRemover)`: given the horizontal gap, the vertical gap and the
  remover's rectangle nodes (sorted by x, overlaps computed), returns the nodes with their
  new y coordinates and the height of the resulting strip of rectangles. -/
  removeOverlaps : (horizontalGap verticalGap : Float) → Array RectangleNode →
    Array RectangleNode × Float

instance : Inhabited IRectangleStripOverlapRemovalStrategy := ⟨⟨fun _ _ ns => (ns, 0.0)⟩⟩

end Elk.Alg.Common.Overlaps
