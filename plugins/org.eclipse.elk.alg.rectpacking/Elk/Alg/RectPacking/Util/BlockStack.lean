import Elk.Alg.RectPacking.Util.Block
/-!
# `org.eclipse.elk.alg.rectpacking.util.BlockStack`

Port of `util/block_stack.rs` (elk-rs): blocks stacked on top of each other. The stack data
lives in the `RectPackingArena`; the methods take a `BlockStackId`.
-/
namespace Elk.Alg.RectPacking.Util

open Elk.Graph Elk.Core.Util
open RectPackingM

namespace BlockStack

/-- `BlockStack::new(x, y, node_node_spacing)`. -/
def new (x y nodeNodeSpacing : Float) : BlockStack := { x, y, nodeNodeSpacing }

/-- `Rc::new(RefCell::new(BlockStack::new(x, y, node_node_spacing)))`. -/
def create (x y nodeNodeSpacing : Float) : RectPackingM BlockStackId :=
  RectPackingM.addStack (new x y nodeNodeSpacing)

/-- `BlockStack::add_block(stack, block)`: sets the block's stack and grows the stack
(maximum width, heights plus spacing). -/
def addBlock (s : BlockStackId) (b : BlockId) : RectPackingM Unit := do
  Block.setStack b (some s)
  let blk ← getBlock b
  modifyStack s fun st =>
    { st with width := fmax st.width blk.width
              height := st.height + (blk.height + (if st.blocks.isEmpty then 0.0 else st.nodeNodeSpacing))
              blocks := st.blocks.push b }

/-- `update_dimension()`: recomputes width and height from the blocks. -/
def updateDimension (s : BlockStackId) : RectPackingM Unit := do
  let st ← getStack s
  let mut height : Float := 0.0
  let mut width : Float := 0.0
  let mut index := 0
  for b in st.blocks do
    let blk ← getBlock b
    width := fmax width blk.width
    height := height + (blk.height + (if index > 0 then st.nodeNodeSpacing else 0.0))
    index := index + 1
  modifyStack s fun x => { x with height, width }

/-- `set_location(x, y)`: moves every block by the position change. -/
def setLocation (s : BlockStackId) (x y : Float) : RectPackingM Unit := do
  let st ← getStack s
  let xDiff := x - st.x
  let yDiff := y - st.y
  for b in st.blocks do
    let blk ← getBlock b
    Block.setLocation b (blk.x + xDiff) (blk.y + yDiff)
  modifyStack s fun st => { st with x, y }

/-- `minimum_width()`: the maximum `minWidth` of the blocks. -/
def minimumWidth (s : BlockStackId) : RectPackingM Float := do
  let mut minWidth : Float := 0.0
  for b in (← getStack s).blocks do
    minWidth := fmax minWidth (← getBlock b).minWidth
  return minWidth

/-- `get_width_for_fixed_height(height)`: a single block answers `width_for_target_height`;
otherwise binary search (step > 1) between the minimum width and the stack width for the
smallest width whose summed block heights are below `height`. -/
def getWidthForFixedHeight (s : BlockStackId) (height : Float) : RectPackingM Float := do
  let st ← getStack s
  if st.blocks.size == 1 then
    return ← Block.widthForTargetHeight st.blocks[0]! height
  let minWidth ← minimumWidth s
  let mut upperBound := st.width
  let mut lowerBound := minWidth
  let mut viableWidth := st.width
  let mut newWidth := (upperBound - lowerBound) / 2.0 + lowerBound
  while lowerBound + 1.0 < upperBound do
    let mut totalHeight : Float := 0.0
    for b in st.blocks do
      totalHeight := totalHeight + (← Block.heightForTargetWidth b newWidth)
    if totalHeight < height then
      viableWidth := newWidth
      upperBound := newWidth
    else
      lowerBound := newWidth
    newWidth := (upperBound - lowerBound) / 2.0 + lowerBound
  return viableWidth

/-- `place_rects_in(target_width)`: re-places every block below the previous one in
`target_width`. Like Rust/Java the resulting height is the final `current_y` (it starts at the
stack's y and includes the trailing spacing). -/
def placeRectsIn (s : BlockStackId) (targetWidth : Float) : RectPackingM Unit := do
  let st ← getStack s
  let mut currentY := st.y
  let mut currentHeight : Float := 0.0
  let mut currentWidth : Float := 0.0
  for b in st.blocks do
    Block.setLocation b st.x currentY
    let _ ← Block.placeRectsIn b targetWidth
    let blk ← getBlock b
    currentWidth := fmax currentWidth blk.width
    currentY := currentY + (blk.height + st.nodeNodeSpacing)
    currentHeight := currentY
  modifyStack s fun x => { x with width := currentWidth, height := currentHeight }

/-- `BlockStack::expand(stack, additional_width, additional_height)`: shifts the i-th block down
by `i * h` (`h` = equal share of the additional height) and expands it to the stack width plus
the additional width. The block list and the stack width are read once at the start. -/
def expand (s : BlockStackId) (additionalWidth additionalHeight : Float) : RectPackingM Unit := do
  let st ← getStack s
  let blocks := st.blocks
  let stackWidth := st.width
  let additionalHeightPerBlock :=
    if blocks.isEmpty then 0.0 else additionalHeight / blocks.size.toFloat
  let mut index := 0
  for b in blocks do
    let blk ← getBlock b
    Block.setLocation b blk.x (blk.y + index.toFloat * additionalHeightPerBlock)
    let blk ← getBlock b
    let expandWidth := stackWidth - blk.width + additionalWidth
    Block.expand b expandWidth additionalHeightPerBlock
    index := index + 1

/-- `set_width(width)`. -/
def setWidth (s : BlockStackId) (width : Float) : RectPackingM Unit := modifyStack s fun x => { x with width }
/-- `set_height(height)`. -/
def setHeight (s : BlockStackId) (height : Float) : RectPackingM Unit := modifyStack s fun x => { x with height }

end BlockStack

end Elk.Alg.RectPacking.Util
