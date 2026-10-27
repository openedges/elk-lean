import Elk.Core.Util.ElkUtil
import Elk.Alg.RectPacking.Util.RectPackingArena
/-!
# `org.eclipse.elk.alg.rectpacking.util.BlockRow`

Port of `util/block_row.rs` (elk-rs). A `BlockRow` is a value owned by its `Block`; every method
takes the row and returns the updated row, while the rectangle geometry (`ElkNode` x/y/size) is
updated in `ElkM`. Float operations follow the Rust evaluation order (`a += b + c` is
`a + (b + c)`).
-/
namespace Elk.Alg.RectPacking.Util

open Elk.Graph Elk.Core.Util Elk.Core.Math

namespace BlockRow

/-- `BlockRow::new(x, y, node_node_spacing)`. -/
def new (x y nodeNodeSpacing : Float) : BlockRow := { x, y, nodeNodeSpacing }

/-- `add_rectangle(rect)`: places the rectangle right of the last one (spacing unless the row is
empty) at the row's y and grows the row. Rust returns `true`; the updated row is returned here. -/
def addRectangle (row : BlockRow) (rect : NodeId) : ElkM BlockRow := do
  let offset := if row.rects.isEmpty then 0.0 else row.nodeNodeSpacing
  ElkM.modifyNode rect fun n => { n with x := row.x + row.width + offset }
  ElkM.modifyNode rect fun n => { n with y := row.y }
  let n ← ElkM.getNode rect
  let height := fmax row.height n.height
  let width := row.width + (n.width + offset)
  return { row with height, width, rects := row.rects.push rect }

/-- `update_row()`: re-places all rectangles from the row's x and recomputes width and height. -/
def updateRow (row : BlockRow) : ElkM BlockRow := do
  let mut width : Float := 0.0
  let mut height : Float := 0.0
  for rect in row.rects do
    ElkM.modifyNode rect fun n => { n with x := row.x + width, y := row.y }
    let n ← ElkM.getNode rect
    width := width + (n.width + row.nodeNodeSpacing)
    height := fmax height (n.height + row.nodeNodeSpacing)
  if !row.rects.isEmpty then
    return { row with width := width - row.nodeNodeSpacing, height := height - row.nodeNodeSpacing }
  else
    return { row with width := 0.0, height := 0.0 }

/-- `remove_rectangle(rect, update)`: removes every occurrence of the rectangle (`retain`) and
optionally re-places the remaining ones. -/
def removeRectangle (row : BlockRow) (rect : NodeId) (update : Bool) : ElkM BlockRow := do
  let row := { row with rects := row.rects.filter (· != rect) }
  if update then updateRow row else return row

/-- `expand(width_for_row, additional_height_for_row, index)`: distributes the additional width
evenly over the rectangles (shifting the i-th by `i * w`), moves them down by
`index * additional_height_for_row`, sets their height to the new row height and translates
their content (`ElkUtil::translate(rect, new_size, old_size)`). -/
def expand (row : BlockRow) (widthForRow additionalHeightForRow : Float) (index : Nat) : ElkM BlockRow := do
  let additionalWidthForRect :=
    if row.rects.isEmpty then 0.0 else (widthForRow - row.width) / row.rects.size.toFloat
  let row := { row with height := row.height + additionalHeightForRow, width := widthForRow }
  let mut i := 0
  for rect in row.rects do
    let old ← ElkM.getNode rect
    let oldWidth := old.width
    let oldHeight := old.height
    ElkM.modifyNode rect fun n =>
      { n with x := n.x + i.toFloat * additionalWidthForRect
               y := n.y + index.toFloat * additionalHeightForRow
               width := n.width + additionalWidthForRect
               height := row.height }
    let new ← ElkM.getNode rect
    ElkUtil.translateNodeWithSizes rect ⟨new.width, new.height⟩ ⟨oldWidth, oldHeight⟩
    i := i + 1
  return row

/-- `nodes()`. -/
@[inline] def nodes (row : BlockRow) : Array NodeId := row.rects

end BlockRow

end Elk.Alg.RectPacking.Util
