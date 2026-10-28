import Elk.Alg.RectPacking.Util.Block
/-!
# `org.eclipse.elk.alg.rectpacking.util.BlockStack`

Port of `util/block_stack.rs` (elk-rs): blocks stacked on top of each other. The stack data
lives in the `RectPackingArena`; the methods take a `BlockStackId`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0
private def fl2p0 : Float := 2.0

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
              height := st.height + (blk.height + (if st.blocks.isEmpty then fl0p0 else st.nodeNodeSpacing))
              blocks := st.blocks.push b }

/-- `update_dimension()`: recomputes width and height from the blocks. -/
def updateDimension (s : BlockStackId) : RectPackingM Unit := do
  let st ← getStack s
  let mut height : Float := fl0p0
  let mut width : Float := fl0p0
  let mut index := 0
  for b in st.blocks do
    let blk ← getBlock b
    width := fmax width blk.width
    height := height + (blk.height + (if index > 0 then st.nodeNodeSpacing else fl0p0))
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

/-- The binary search loop of `get_width_for_fixed_height` (pure, on the graph value: the block
heights are those of layouts of copies, nothing moves). -/
private partial def searchWidth (g : ElkGraph) (blocks : Array Block) (height upperBound lowerBound
    viableWidth newWidth : Float) : Float :=
  if lowerBound + fl1p0 < upperBound then
    let totalHeight := blocks.foldl (init := fl0p0) fun acc blk => acc + (Block.boundsIn g blk newWidth).2
    if totalHeight < height then
      searchWidth g blocks height newWidth lowerBound newWidth ((newWidth - lowerBound) / fl2p0 + lowerBound)
    else
      searchWidth g blocks height upperBound newWidth viableWidth ((upperBound - newWidth) / fl2p0 + newWidth)
  else viableWidth

/-- `get_width_for_fixed_height(height)`: a single block answers `width_for_target_height`;
otherwise binary search (step > 1) between the minimum width and the stack width for the
smallest width whose summed block heights are below `height`. -/
def getWidthForFixedHeight (s : BlockStackId) (height : Float) : RectPackingM Float := do
  let st ← getStack s
  if st.blocks.size == 1 then
    return ← Block.widthForTargetHeight st.blocks[0]! height
  let minWidth ← minimumWidth s
  let upperBound := st.width
  let lowerBound := minWidth
  let mut blocks : Array Block := Array.mkEmpty st.blocks.size
  for b in st.blocks do
    blocks := blocks.push (← getBlock b)
  let g ← getThe ElkGraph
  return searchWidth g blocks height upperBound lowerBound st.width
    ((upperBound - lowerBound) / 2.0 + lowerBound)

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
    if blocks.isEmpty then fl0p0 else additionalHeight / blocks.size.toFloat
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
