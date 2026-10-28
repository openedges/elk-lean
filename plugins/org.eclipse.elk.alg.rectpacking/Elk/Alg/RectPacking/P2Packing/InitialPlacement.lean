import Elk.Alg.RectPacking.Util
import Elk.Alg.RectPacking.Options.RectPackingOptions
/-!
# `org.eclipse.elk.alg.rectpacking.p2packing.InitialPlacement`

Port of `p2packing/initial_placement.rs` (elk-rs): places the rectangles in rows of at most the
bounding width, bundling consecutive rectangles of similar height into blocks, and the helpers
that try to add a rectangle to an existing block (used by the compaction).

Float operations follow the Rust evaluation order (`a + b + c` is `(a + b) + c`, `a += b + c` is
`a + (b + c)`).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.RectPacking.P2Packing

open Elk.Graph Elk.Core.Util Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options
open RectPackingM

namespace InitialPlacement

/-- `is_similar_height(block, rect, node_node_spacing)`: the rectangle height lies between the
smallest rectangle height and the minimum height of the block, or within 50 % of the block's
average height. -/
def isSimilarHeight (block : BlockId) (rect : NodeId) (_nodeNodeSpacing : Float) : RectPackingM Bool := do
  let rectHeight := (← ElkM.getNode rect).height
  let blk ← getBlock block
  if rectHeight >= blk.smallestRectHeight && rectHeight <= blk.minHeight then
    return true
  else
    return blk.averageHeight * 0.5 <= rectHeight && blk.averageHeight * 1.5 >= rectHeight

/-- `place(rectangles, bounding_width, node_node_spacing)`: the initial rows. A new row starts
when the rectangle does not fit into the bounding width (or has `IN_NEW_ROW`); a new block starts
when the rectangle is not of similar height (always with `PACKING_COMPACTION_ROW_HEIGHT_REEVALUATION`
on the rectangle's parent). -/
def place (rectangles : Array NodeId) (boundingWidth nodeNodeSpacing : Float) :
    RectPackingM (Array RectRowId) := do
  let mut rows : Array RectRowId := #[]
  let mut row ← RectRow.create fl0p0 nodeNodeSpacing
  let mut drawingHeight : Float := fl0p0
  let block ← Block.create fl0p0 fl0p0 row nodeNodeSpacing
  RectRow.addBlock row block
  let mut currentWidth : Float := fl0p0
  let mut currentBlock := block
  for rect in rectangles do
    let rectNode ← ElkM.getNode rect
    let rectWidth := rectNode.width
    let inNewRow := (rectNode.props.get RectPackingOptions.IN_NEW_ROW).getD false
    let isBlockEmpty := (← getBlock currentBlock).children.isEmpty
    let potentialRowWidth := currentWidth + rectWidth + (if isBlockEmpty then fl0p0 else nodeNodeSpacing)
    if potentialRowWidth > boundingWidth || inNewRow then
      drawingHeight := drawingHeight + ((← getRow row).height + nodeNodeSpacing)
      rows := rows.push row
      row ← RectRow.create drawingHeight nodeNodeSpacing
      currentBlock ← Block.create fl0p0 (← getRow row).y row nodeNodeSpacing
      RectRow.addBlock row currentBlock
    let rowHeightReevaluation ← match rectNode.parent with
      | some p => do
        pure (((← ElkM.getNode p).props.get RectPackingOptions.PACKING_COMPACTION_ROW_HEIGHT_REEVALUATION).getD false)
      | none => pure false
    let similar ← if (← getBlock currentBlock).children.isEmpty then pure true
      else if rowHeightReevaluation then pure false
      else isSimilarHeight currentBlock rect nodeNodeSpacing
    if similar then
      Block.addChild currentBlock rect
    else
      let blk ← getBlock currentBlock
      let newBlockX := blk.x + blk.width + nodeNodeSpacing
      let newBlock ← Block.create newBlockX (← getRow row).y row nodeNodeSpacing
      RectRow.addBlock row newBlock
      Block.addChild newBlock rect
      currentBlock := newBlock
    let n ← ElkM.getNode rect
    currentWidth := n.x + n.width
  rows := rows.push row
  return rows

/-- `place_rect_in_block(row, block, rect, bounding_width, node_node_spacing)`: adds the
rectangle to the last block row (if it fits into the bounding width and the row height, or the
row has a single block) or to a new block row (if it fits below); `false` if the heights are not
similar or it fits nowhere. -/
def placeRectInBlock (row : RectRowId) (block : BlockId) (rect : NodeId)
    (boundingWidth nodeNodeSpacing : Float) : RectPackingM Bool := do
  if (← isSimilarHeight block rect nodeNodeSpacing) then
    let blk ← getBlock block
    let lastRowNewX := Block.lastRowNewX blk
    let lastRowY := Block.lastRowY blk
    let n ← ElkM.getNode rect
    let rectWidth := n.width
    let rectHeight := n.height
    let r ← getRow row
    let rowHeight := r.height
    if lastRowNewX + rectWidth + nodeNodeSpacing <= boundingWidth &&
        (lastRowY - r.y + rectHeight <= rowHeight || r.children.size == 1) then
      Block.addChild block rect
      return true
    else if blk.x + rectWidth <= boundingWidth &&
        blk.y + blk.height + rectHeight + nodeNodeSpacing <= r.y + rowHeight then
      Block.addChildInNewRow block rect
      return true
  return false

end InitialPlacement

end Elk.Alg.RectPacking.P2Packing
