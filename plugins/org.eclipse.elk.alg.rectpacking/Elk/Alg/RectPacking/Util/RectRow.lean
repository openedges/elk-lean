import Elk.Alg.RectPacking.Util.BlockStack
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.rectpacking.util.RectRow`

Port of `RectRow.java` (elk-rs `util/rect_row.rs`): a row of blocks (and of the block stacks built
from them). The row data lives in the `RectPackingArena`; the methods take a `RectRowId`.
`RectRow.new` and `RectRow.notifyAboutNodeChange` are defined in the arena module.

Java semantics (elk-rs differed): `removeBlock` removes the **first** occurrence of the block
(`List.remove(Object)`; a row can list a block twice, see the arena module) and starts the height at
`Double.MIN_VALUE` (the smallest positive double, also the height of a row without blocks or with
zero-height blocks only); `expand` does not update the row's own width and height;
`calculateBlockStacks` appends to the existing stacks (it is never called by ELK).
-/

namespace Elk.Alg.RectPacking.Util

open Elk.Graph Elk.Core.Util
open RectPackingM

namespace RectRow

/-- `Rc::new(RefCell::new(RectRow::new(y, node_node_spacing)))`. -/
def create (y nodeNodeSpacing : Float) : RectPackingM RectRowId := addRow (new y nodeNodeSpacing)

/-- `expand(width, additionalHeight)`: distributes the additional width evenly over the stacks
(shifting the i-th stack right by `i * w`) and expands every stack to the row height plus the
additional height. The row's width and height stay as they are (Java). -/
def expand (row : RectRowId) (width additionalHeight : Float) : RectPackingM Unit := do
  let r ← getRow row
  let additionalWidth := width - r.width
  let additionalWidthPerStack := additionalWidth / r.stacks.size.toFloat
  let mut index := 0
  for s in r.stacks do
    let st ← getStack s
    let additionalHeightForStack := r.height - st.height + additionalHeight
    BlockStack.setLocation s (st.x + index.toFloat * additionalWidthPerStack) st.y
    BlockStack.expand s additionalWidthPerStack additionalHeightForStack
    index := index + 1

/-- `calculateBlockStacks()`: appends stacks to the row's stacks: consecutive blocks with the same x
(`!=` against the previous x, starting at `-1`) share a stack. -/
def calculateBlockStacks (row : RectRowId) : RectPackingM Unit := do
  let r ← getRow row
  let mut stacks : Array BlockStackId := r.stacks
  let mut currentX : Float := -1.0
  for b in r.children do
    let blockX := (← getBlock b).x
    if blockX != currentX then
      let s ← BlockStack.create blockX r.y r.nodeNodeSpacing
      BlockStack.addBlock s b
      stacks := stacks.push s
      currentX := blockX
    else if let some last := stacks.back? then
      BlockStack.addBlock last b
  modifyRow row fun x => { x with stacks }

/-- `get_first_block()` (Rust panics on an empty row; `default` here). -/
def getFirstBlock (row : RectRowId) : RectPackingM BlockId := do
  return (← getRow row).children[0]!

/-- `get_last_block()` (Rust panics on an empty row; `default` here). -/
def getLastBlock (row : RectRowId) : RectPackingM BlockId := do
  let r ← getRow row
  return r.children[r.children.size - 1]!

/-- `number_of_assigned_blocks()`. -/
def numberOfAssignedBlocks (row : RectRowId) : RectPackingM Nat := do
  return (← getRow row).children.size

/-- `add_block(block)`: appends the block and grows the row (maximum height, widths plus
spacing). -/
def addBlock (row : RectRowId) (b : BlockId) : RectPackingM Unit := do
  let blk ← getBlock b
  modifyRow row fun r =>
    { r with height := javaMax r.height blk.height
             width := r.width + (blk.width + (if r.children.isEmpty then fl0p0 else r.nodeNodeSpacing))
             children := r.children.push b }

/-- `removeBlock(block)`: removes the first occurrence of the block, shrinks the width by the block
width (plus spacing if blocks remain) and recomputes the height (`Math.max` from
`Double.MIN_VALUE`). -/
def removeBlock (row : RectRowId) (b : BlockId) : RectPackingM Unit := do
  let blockWidth := (← getBlock b).width
  modifyRow row fun r => { r with children := r.children.erase b }
  let r ← getRow row
  let width := r.width - (blockWidth + (if r.children.isEmpty then fl0p0 else r.nodeNodeSpacing))
  let mut newMaxHeight := Float.minPositive
  for c in r.children do
    newMaxHeight := javaMax newMaxHeight (← getBlock c).height
  modifyRow row fun x => { x with width, height := newMaxHeight }

/-- `set_y(y)`: moves every stack (not the blocks outside stacks) by the change of y. -/
def setY (row : RectRowId) (y : Float) : RectPackingM Unit := do
  let r ← getRow row
  let yChange := y - r.y
  for s in r.stacks do
    let st ← getStack s
    BlockStack.setLocation s st.x (st.y + yChange)
  modifyRow row fun x => { x with y }

/-- `add_stack(stack)`. -/
def addStack (row : RectRowId) (s : BlockStackId) : RectPackingM Unit :=
  modifyRow row fun r => { r with stacks := r.stacks.push s }

/-- `resetStacks()`: a new empty stack list (the blocks keep their stack references). -/
def resetStacks (row : RectRowId) : RectPackingM Unit :=
  modifyRow row fun r => { r with stacks := #[] }

/-- `set_height(height)`. -/
def setHeight (row : RectRowId) (height : Float) : RectPackingM Unit := modifyRow row fun x => { x with height }
/-- `set_width(width)`. -/
def setWidth (row : RectRowId) (width : Float) : RectPackingM Unit := modifyRow row fun x => { x with width }
/-- `set_potential_additional_width_to_get_last_block(value)`. -/
def setPotentialAdditionalWidthToGetLastBlock (row : RectRowId) (value : Float) : RectPackingM Unit :=
  modifyRow row fun x => { x with potentialAdditionalWidthToGetLastBlock := value }

end RectRow

end Elk.Alg.RectPacking.Util
