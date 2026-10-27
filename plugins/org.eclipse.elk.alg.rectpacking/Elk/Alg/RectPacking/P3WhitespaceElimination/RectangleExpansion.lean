import Elk.Alg.RectPacking.Util
/-!
# `org.eclipse.elk.alg.rectpacking.p3whitespaceelimination.RectangleExpansion`

Port of `p3whitespaceelimination/rectangle_expansion.rs` (elk-rs): distributes the additional
height evenly over the rows (the i-th row moves down by `i` shares) and expands every row to the
drawing width. The row is mutably borrowed in Rust while it moves and expands, which never
notifies (`set_location` / `expand` of blocks do not call `notify_parent`).
-/
namespace Elk.Alg.RectPacking.P3WhitespaceElimination

open Elk.Graph Elk.Alg.RectPacking.Util
open RectPackingM

namespace RectangleExpansion

/-- `expand(rows, drawing_width, additional_height, node_node_spacing)`. -/
def expand (rows : Array RectRowId) (drawingWidth additionalHeight _nodeNodeSpacing : Float) :
    RectPackingM Unit := do
  if rows.isEmpty then return
  let heightPerRow := additionalHeight / rows.size.toFloat
  let mut index := 0
  for row in rows do
    let newY := (← getRow row).y + heightPerRow * index.toFloat
    RectRow.setY row newY
    RectRow.expand row drawingWidth heightPerRow
    index := index + 1

end RectangleExpansion

end Elk.Alg.RectPacking.P3WhitespaceElimination
