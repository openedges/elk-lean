import Elk.Alg.RectPacking.P2Packing.InitialPlacement
/-!
# `org.eclipse.elk.alg.rectpacking.p2packing.Compaction`

Port of `p2packing/compaction.rs` (elk-rs): compacts one row by moving blocks of the row and the
first block of the next row into stacks (absorbing rectangles, placing a block below or beside
another one, using the row height or width).

The row list (`rows: &mut Vec<RectRowRef>`) is threaded through the functions and returned.
Removing a row from the list drops it in Rust (the phase's row list holds the only strong
reference while the compaction runs), so `removeRowAt` calls `RectRow.drop`: `Block.parent_row()`
of blocks that still point to it returns `None` from then on. The `RefCell` borrows of the Rust
code never overlap with a notifying block other than the notifier itself (the notifier's own
`borrow_mut` is modelled by `notifyAboutNodeChange`), so no `withBorrowed` is needed.

Rust deviation from Java kept: `something_was_changed |= absorb_blocks(..)` always runs the
absorption (no short circuit), like Java's `|=`.
-/
namespace Elk.Alg.RectPacking.P2Packing

open Elk.Graph Elk.Core.Util Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options
open RectPackingM

namespace Compaction

/-- `rows.remove(index)`: removes the row from the list and drops it (`RectRow.drop`, see the
module doc). -/
def removeRowAt (rows : Array RectRowId) (index : Nat) : RectPackingM (Array RectRowId) := do
  match rows[index]? with
  | some r =>
    RectRow.drop r
    return rows.eraseIdx! index
  | none => return rows

/-- `rows.len() > index && rows[index].children().is_empty()` (short-circuit). -/
def rowIsEmptyAt (rows : Array RectRowId) (index : Nat) : RectPackingM Bool := do
  match rows[index]? with
  | some r => return (← getRow r).children.isEmpty
  | none => return false

/-- `node_in_new_row(node)`: `IN_NEW_ROW` (default `false`). -/
def nodeInNewRow (node : NodeId) : RectPackingM Bool := do
  return ((← ElkM.getNode node).props.get RectPackingOptions.IN_NEW_ROW).getD false

/-- `get_next_block(rows, row, block_id, next_row_index)`: the next block of the row, else the
first block of the next row (if that row has blocks). -/
def getNextBlock (rows : Array RectRowId) (row : RectRowId) (blockId nextRowIndex : Nat) :
    RectPackingM (Option BlockId) := do
  let r ← getRow row
  if blockId < r.children.size - 1 then
    return r.children[blockId + 1]?
  else if h : nextRowIndex < rows.size then
    let next ← getRow rows[nextRowIndex]
    if !next.children.isEmpty then return next.children[0]? else return none
  else
    return none

/-- `use_row_height(row, block)`: if the block is lower than the row, re-places its stack in the
width needed for the row height; `true` if the stack width changed. -/
def useRowHeight (row : RectRowId) (block : BlockId) : RectPackingM Bool := do
  let rowHeight := (← getRow row).height
  let blockHeight := (← getBlock block).height
  let some stack ← Block.stackOf block | return false
  let previousWidth := (← getStack stack).width
  if blockHeight < rowHeight then
    let targetWidth ← BlockStack.getWidthForFixedHeight stack rowHeight
    if (← getStack stack).width > targetWidth then
      BlockStack.placeRectsIn stack targetWidth
      return previousWidth != (← getStack stack).width
  return false

/-- `use_row_width(block, bounding_width)`: re-places the block in the remaining row width and
updates its stack. -/
def useRowWidth (block : BlockId) (boundingWidth : Float) : RectPackingM Unit := do
  let blockX := (← getBlock block).x
  let _ ← Block.placeRectsIn block (boundingWidth - blockX)
  if let some stack ← Block.stackOf block then
    BlockStack.updateDimension stack

/-- `absorb_blocks(row, block, next_block, bounding_width, node_node_spacing)`: moves the
rectangles of the next block into the block while they fit; removes the emptied next block from
its (live) parent row. -/
def absorbBlocks (row : RectRowId) (block nextBlock : BlockId) (boundingWidth nodeNodeSpacing : Float) :
    RectPackingM Bool := do
  let mut somethingWasChanged := false
  let mut rect := (← getBlock nextBlock).children[0]!
  while (← InitialPlacement.placeRectInBlock row block rect boundingWidth nodeNodeSpacing) do
    somethingWasChanged := true
    Block.removeChild nextBlock rect
    let nb ← getBlock nextBlock
    if nb.children.isEmpty then break
    rect := nb.children[0]!
  if (← getBlock nextBlock).children.isEmpty then
    if let some parentRow ← Block.parentRowOf nextBlock then
      RectRow.removeBlock parentRow nextBlock
  if somethingWasChanged then
    if let some stack ← Block.stackOf block then
      BlockStack.updateDimension stack
  return somethingWasChanged

/-- `place_below(rows, row, block, next_block, was_from_next_row, bounding_width, next_row_index,
node_node_spacing)`: places the next block below the block (same stack) if both fit into the row
height in the remaining width; a block of the next row moves into the row. -/
def placeBelow (rows : Array RectRowId) (row : RectRowId) (block nextBlock : BlockId)
    (wasFromNextRow : Bool) (boundingWidth : Float) (nextRowIndex : Nat) (nodeNodeSpacing : Float) :
    RectPackingM (Bool × Array RectRowId) := do
  let mut rows := rows
  let remainingWidth := boundingWidth - (← getBlock block).x
  if (← getBlock nextBlock).minWidth + nodeNodeSpacing > remainingWidth then
    return (false, rows)
  let blk ← getBlock block
  let rowY := (← getRow row).y
  let currentBlockMinHeight := blk.y - rowY + (← Block.heightForTargetWidth block remainingWidth)
  let nextBlockMinHeight ← Block.heightForTargetWidth nextBlock remainingWidth
  if currentBlockMinHeight + nodeNodeSpacing + nextBlockMinHeight <= (← getRow row).height then
    let blockX := (← getBlock block).x
    let _ ← Block.placeRectsIn block (boundingWidth - blockX)
    Block.setFixed block true
    let _ ← Block.placeRectsIn nextBlock (boundingWidth - blockX)
    let b ← getBlock block
    Block.setLocation nextBlock blockX (b.y + b.height + nodeNodeSpacing)
    Block.setPositionFixed nextBlock true
    if let some stack ← Block.stackOf block then
      BlockStack.addBlock stack nextBlock
    if wasFromNextRow then
      RectRow.addBlock row nextBlock
      Block.setParentRow nextBlock row
      if h : nextRowIndex < rows.size then
        let nextRow := rows[nextRowIndex]
        RectRow.removeBlock nextRow nextBlock
        if (← getRow nextRow).children.isEmpty then
          rows ← removeRowAt rows nextRowIndex
    return (true, rows)
  return (false, rows)

/-- `place_beside(rows, row, block, next_block, was_from_next_row, bounding_width,
next_row_index, node_node_spacing, row_height_reevaluation)`: shrinks the block's stack to the
row height and places the next block beside it (or, as the last row optimization, grows the
block to the next block's height); the next block moves from the next row into the row. -/
def placeBeside (rows : Array RectRowId) (row : RectRowId) (block nextBlock : BlockId)
    (_wasFromNextRow : Bool) (boundingWidth : Float) (nextRowIndex : Nat) (nodeNodeSpacing : Float)
    (rowHeightReevaluation : Bool) : RectPackingM (Bool × Array RectRowId) := do
  let mut rows := rows
  let some stack ← Block.stackOf block | return (false, rows)
  let r ← getRow row
  let rowHeight := r.height
  let st ← getStack stack
  let currentBlockMinWidth ← BlockStack.getWidthForFixedHeight stack (r.y + rowHeight - st.y)
  let nextBlockMinHeight := (← getBlock nextBlock).minHeight
  let shouldRowHeightBeReevaluated := nextBlockMinHeight > rowHeight && rowHeightReevaluation
  let mut targetWidthOfNextBlock :=
    boundingWidth - ((← getStack stack).x + currentBlockMinWidth - nodeNodeSpacing)
  let nextBlockHeight ← Block.heightForTargetWidth nextBlock targetWidthOfNextBlock
  if shouldRowHeightBeReevaluated && nextBlockHeight > nextBlockMinHeight then
    return (false, rows)
  if shouldRowHeightBeReevaluated then
    let stacks := (← getRow row).stacks
    let mut potentialWidth : Float := 0.0
    for s in stacks do
      potentialWidth := potentialWidth + ((← BlockStack.getWidthForFixedHeight s nextBlockMinHeight) + nodeNodeSpacing)
    targetWidthOfNextBlock := boundingWidth - potentialWidth
  if targetWidthOfNextBlock < (← getBlock nextBlock).minWidth then
    return (false, rows)
  let lastRowOptimization : Bool ←
    if h : nextRowIndex = rows.size - 1 ∧ nextRowIndex < rows.size then
      pure (targetWidthOfNextBlock >= (← getRow rows[nextRowIndex]).width)
    else pure false
  if !shouldRowHeightBeReevaluated && nextBlockHeight > rowHeight && !lastRowOptimization then
    return (false, rows)
  if lastRowOptimization || shouldRowHeightBeReevaluated || nextBlockHeight <= rowHeight then
    if lastRowOptimization && nextBlockHeight > rowHeight then
      Block.setHeight block nextBlockHeight
      let targetWidth ← Block.widthForTargetHeight block nextBlockHeight
      let _ ← Block.placeRectsIn block targetWidth
    else
      BlockStack.placeRectsIn stack currentBlockMinWidth
      Block.setFixed block true
    let b ← getBlock block
    let _ ← Block.placeRectsIn nextBlock (boundingWidth - (b.x + b.width))
    let st ← getStack stack
    Block.setLocation nextBlock (st.x + st.width) (← getRow row).y
    RectRow.addBlock row nextBlock
    if h : nextRowIndex < rows.size then
      let nextRow := rows[nextRowIndex]
      RectRow.removeBlock nextRow nextBlock
      if (← getRow nextRow).children.isEmpty then
        rows ← removeRowAt rows nextRowIndex
    return (true, rows)
  return (false, rows)

/-- `compact(row_idx, rows, bounding_width, node_node_spacing, row_height_reevaluation)`:
compacts the row `row_idx`. Returns `(something_was_changed, compact_row_again)` and the updated
row list. The block index is not advanced after an empty block was removed and after the next
block was absorbed completely (Rust `continue`). -/
def compact (rowIdx : Nat) (rows : Array RectRowId) (boundingWidth nodeNodeSpacing : Float)
    (rowHeightReevaluation : Bool) : RectPackingM ((Bool × Bool) × Array RectRowId) := do
  let mut rows := rows
  let mut somethingWasChanged := false
  let mut compactRowAgain := false
  let nextRowIndex := rowIdx + 1
  let row := rows[rowIdx]!
  let mut currentStack : Option BlockStackId := none
  let mut blockId := 0
  while blockId < (← RectRow.numberOfAssignedBlocks row) do
    let block := (← getRow row).children[blockId]!
    if (← getBlock block).fixed then
      blockId := blockId + 1
      continue
    if (← getBlock block).children.isEmpty then
      IO.eprintln "There should not be an empty block. Empty blocks are directly removed."
      RectRow.removeBlock row block
      somethingWasChanged := true
      continue
    if !(← getBlock block).positionFixed then
      if let some stack := currentStack then
        BlockStack.updateDimension stack
      let stackX ← match currentStack with
        | some stack => do
          let st ← getStack stack
          pure (st.x + st.width + nodeNodeSpacing)
        | none => pure 0.0
      let rowY := (← getRow row).y
      let newStack ← BlockStack.create stackX rowY nodeNodeSpacing
      let ns ← getStack newStack
      Block.setLocation block (ns.x + ns.width) rowY
      RectRow.addStack row newStack
      BlockStack.addBlock newStack block
      Block.setPositionFixed block true
      currentStack := some newStack
    let mut nextBlock ← getNextBlock rows row blockId nextRowIndex
    let wasFromNextRow : Bool ← match nextBlock with
      | some nb => do
        match ← Block.parentRowOf nb with
        | some parent => pure (parent != row)
        | none => pure false
      | none => pure false
    if let some nextBlockRef := nextBlock then
      let nb ← getBlock nextBlockRef
      let firstInNewRow ← match nb.children[0]? with
        | some c => nodeInNewRow c
        | none => pure false
      if !nb.children.isEmpty && !firstInNewRow then
        useRowWidth block boundingWidth
        let absorbed ← absorbBlocks row block nextBlockRef boundingWidth nodeNodeSpacing
        somethingWasChanged := somethingWasChanged || absorbed
      else
        RectRow.removeBlock row nextBlockRef
        break
      if (← getBlock nextBlockRef).children.isEmpty then
        if h : nextRowIndex < rows.size then
          RectRow.removeBlock rows[nextRowIndex] nextBlockRef
        nextBlock := none
        while (← rowIsEmptyAt rows nextRowIndex) do
          rows ← removeRowAt rows nextRowIndex
      if nextBlock.isNone then
        continue
      -- the next block is not empty here (an empty one was cleared above)
      let firstChild := (← getBlock nextBlockRef).children[0]!
      let mut placedBelow := false
      if !(← nodeInNewRow firstChild) then
        let (placed, rows') ← placeBelow rows row block nextBlockRef wasFromNextRow boundingWidth
          nextRowIndex nodeNodeSpacing
        rows := rows'
        placedBelow := placed
      if placedBelow then
        somethingWasChanged := true
        blockId := blockId + 1
        continue
      if wasFromNextRow then
        let oldRowHeight := (← getRow row).height
        let nextBlockMinHeight := (← getBlock nextBlockRef).minHeight
        let mut placedBeside := false
        if !(← nodeInNewRow (← getBlock nextBlockRef).children[0]!) then
          let (placed, rows') ← placeBeside rows row block nextBlockRef wasFromNextRow boundingWidth
            nextRowIndex nodeNodeSpacing rowHeightReevaluation
          rows := rows'
          placedBeside := placed
        if placedBeside then
          somethingWasChanged := true
          if oldRowHeight < nextBlockMinHeight then
            compactRowAgain := true
            Block.setParentRow nextBlockRef row
            break
          blockId := blockId + 1
          continue
        else if (← useRowHeight row block) then
          Block.setFixed block true
          somethingWasChanged := true
          blockId := blockId + 1
          continue
      else if (← useRowHeight row block) then
        Block.setFixed block true
        somethingWasChanged := true
        blockId := blockId + 1
        continue
      if somethingWasChanged then
        blockId := blockId + 1
        continue
    if (← useRowHeight row block) then
      Block.setFixed block true
      somethingWasChanged := true
      if let some nextBlockRef := nextBlock then
        Block.setPositionFixed nextBlockRef false
      blockId := blockId + 1
      continue
    else if let some stack ← Block.stackOf block then
      BlockStack.updateDimension stack
    blockId := blockId + 1
  return ((somethingWasChanged, compactRowAgain), rows)

end Compaction

end Elk.Alg.RectPacking.P2Packing
