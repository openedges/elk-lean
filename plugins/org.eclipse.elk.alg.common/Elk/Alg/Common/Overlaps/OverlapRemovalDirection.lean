import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.common.overlaps.RectangleStripOverlapRemover.OverlapRemovalDirection`

Java inner enum of `RectangleStripOverlapRemover` (elk-rs `overlaps/mod.rs`
`OverlapRemovalDirection`), in its own file because Lean modules cannot be
cyclic. The direction in which overlaps are removed: rectangles are moved along
this direction away from the start coordinate.
-/
namespace Elk.Alg.Common.Overlaps

/-- `OverlapRemovalDirection` (`UP`, `DOWN`, `LEFT`, `RIGHT`). -/
elk_enum OverlapRemovalDirection := up down left right

end Elk.Alg.Common.Overlaps
