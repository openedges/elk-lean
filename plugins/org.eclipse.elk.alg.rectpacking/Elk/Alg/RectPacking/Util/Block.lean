import Elk.Core.Math.ElkRectangle
import Elk.Alg.RectPacking.Util.BlockRow
/-!
# `org.eclipse.elk.alg.rectpacking.util.Block`

Port of `util/block.rs` (elk-rs). The block data lives in the `RectPackingArena`
(`Elk.Alg.RectPacking.Util.RectPackingArena`); the methods take a `BlockId`. Every mutating
method that notifies the parent row in Rust (`notify_parent`) does so here, with the Rust
`RefCell` semantics described in the arena module.

The query methods that work on a clone in Rust (`height_for_target_width`,
`place_rects_in_width_height`) are `placeRectsInInternal` on a `Block` value with
`placeRects := false`, which neither moves rectangles nor notifies.

Rust deviations from Java kept: `setLocation` moves the block rows by `row.x + (x - self.x)`
(Java `row.x + x - self.x`); `adjust_size_add`/`adjust_size_after_remove` keep the old
`averageHeight` when the block has no children (Java computes `NaN`); `add_child_in_new_row`
starts at the block's y when the block has no rows (Java throws).
-/
namespace Elk.Alg.RectPacking.Util

open Elk.Graph Elk.Core.Util Elk.Core.Math
open RectPackingM

namespace Block

/-- `Block::new(x, y, parent_row, node_node_spacing)`. -/
def new (x y : Float) (parentRow : RectRowId) (nodeNodeSpacing : Float) : Block :=
  { x, y, parentRow := some parentRow, nodeNodeSpacing }

/-- `Rc::new(RefCell::new(Block::new(x, y, parent_row, node_node_spacing)))`. -/
def create (x y : Float) (parentRow : RectRowId) (nodeNodeSpacing : Float) : RectPackingM BlockId :=
  addBlock (new x y parentRow nodeNodeSpacing)

/-- `adjust_size_add(rect)`. -/
private def adjustSizeAdd (b : BlockId) (rect : NodeId) : RectPackingM Unit := do
  let n ← ElkM.getNode rect
  let rectWidth := n.width
  let rectHeight := n.height
  modifyBlock b fun blk => Id.run do
    let lastRowWidth := match blk.rows.back? with
      | some r => r.width
      | none => 0.0
    let spacing := if blk.children.size == 1 then 0.0 else blk.nodeNodeSpacing
    let mut blk := blk
    blk := { blk with smallestRectWidth := fmin blk.smallestRectWidth rectWidth }
    blk := { blk with width := fmax blk.width lastRowWidth }
    blk := { blk with minWidth := fmax blk.minWidth (rectWidth + spacing) }
    blk := { blk with smallestRectHeight := fmin blk.smallestRectHeight rectHeight }
    blk := { blk with maxHeight := blk.maxHeight + (rectHeight + spacing) }
    blk := { blk with minHeight := fmax blk.minHeight rectHeight }
    let mut totalHeight : Float :=
      if !blk.rows.isEmpty then (blk.rows.size - 1).toFloat * blk.nodeNodeSpacing else 0.0
    for row in blk.rows do
      totalHeight := totalHeight + row.height
    blk := { blk with height := totalHeight }
    let childCount := blk.children.size.toFloat
    if childCount > 0.0 then
      blk := { blk with averageHeight :=
        blk.maxHeight / childCount - blk.nodeNodeSpacing * ((childCount - 1.0) / childCount) }
    return blk
  notifyParent b

/-- `add_child(rect)`: appends the rectangle to the last block row (creating the first row at the
block position if there is none). -/
def addChild (b : BlockId) (rect : NodeId) : RectPackingM Unit := do
  let blk ← getBlock b
  let mut rows := blk.rows
  if rows.isEmpty then
    rows := rows.push (BlockRow.new blk.x blk.y blk.nodeNodeSpacing)
  let last ← BlockRow.addRectangle rows[rows.size - 1]! rect
  rows := rows.set! (rows.size - 1) last
  setBlock b { blk with children := blk.children.push rect, rows }
  adjustSizeAdd b rect

/-- `add_child_in_new_row(rect)`: starts a new block row below the last one (at the block y if
there is no row). -/
def addChildInNewRow (b : BlockId) (rect : NodeId) : RectPackingM Unit := do
  let blk ← getBlock b
  let lastRowY := match blk.rows.back? with
    | some r => r.y + r.height + blk.nodeNodeSpacing
    | none => blk.y
  let row ← BlockRow.addRectangle (BlockRow.new blk.x lastRowY blk.nodeNodeSpacing) rect
  setBlock b { blk with children := blk.children.push rect, rows := blk.rows.push row }
  adjustSizeAdd b rect

/-- `adjust_size_after_remove()`: drops empty rows, recomputes width/height from the rows (the
spacing is added for every row with index > 0 of the original row list) and the
min/max/smallest values from the children. -/
private def adjustSizeAfterRemove (b : BlockId) : RectPackingM Unit := do
  let blk ← getBlock b
  let mut newWidth : Float := 0.0
  let mut newHeight : Float := 0.0
  let mut kept : Array BlockRow := #[]
  let mut index := 0
  for row in blk.rows do
    if row.rects.isEmpty then
      pure ()
    else
      newWidth := fmax newWidth row.width
      newHeight := newHeight + (row.height + (if index > 0 then blk.nodeNodeSpacing else 0.0))
      kept := kept.push row
    index := index + 1
  let mut minWidth : Float := 0.0
  let mut minHeight : Float := 0.0
  let mut maxHeight : Float := 0.0
  let mut smallestRectHeight := Float.posInf
  let mut smallestRectWidth := Float.posInf
  for rect in blk.children do
    let n ← ElkM.getNode rect
    smallestRectWidth := fmin smallestRectWidth n.width
    minWidth := fmax minWidth n.width
    minHeight := fmax minHeight n.height
    smallestRectHeight := fmin smallestRectHeight n.height
    maxHeight := maxHeight + (n.height + blk.nodeNodeSpacing)
  let childCount := blk.children.size.toFloat
  let averageHeight :=
    if childCount > 0.0 then
      maxHeight / childCount - blk.nodeNodeSpacing * ((childCount - 1.0) / childCount)
    else blk.averageHeight
  setBlock b { blk with rows := kept, height := newHeight, width := newWidth, minWidth, minHeight,
                        maxHeight, smallestRectHeight, smallestRectWidth, averageHeight }
  notifyParent b

/-- `remove_child(rect)`: removes the rectangle from the children and from the first block row
containing it (re-placing that row and dropping it if it became empty). -/
def removeChild (b : BlockId) (rect : NodeId) : RectPackingM Unit := do
  let blk ← getBlock b
  let mut rows := blk.rows
  let mut rowIndex : Option Nat := none
  for i in [0:rows.size] do
    if rows[i]!.rects.contains rect then
      let row ← BlockRow.removeRectangle rows[i]! rect true
      rows := rows.set! i row
      if row.rects.isEmpty then rowIndex := some i
      break
  if let some i := rowIndex then rows := rows.eraseIdx! i
  setBlock b { blk with children := blk.children.filter (· != rect), rows }
  adjustSizeAfterRemove b

/-- `set_location(x, y)`: moves the rectangles and the block rows by the position change. -/
def setLocation (b : BlockId) (x y : Float) : RectPackingM Unit := do
  let blk ← getBlock b
  let xChange := x - blk.x
  let yChange := y - blk.y
  for rect in blk.children do
    ElkM.modifyNode rect fun n => { n with x := n.x + xChange, y := n.y + yChange }
  let rows := blk.rows.map fun row => { row with x := row.x + xChange, y := row.y + yChange }
  setBlock b { blk with rows, x, y }

/-- `place_rects_in_internal(width, place_rects)` on a block value: lays the children out in
rows of at most `width` (a new row starts when the next rectangle would exceed the width and the
current row is not empty). With `placeRects` the rectangles are moved, the block rows rebuilt and
the block's width/height set (the caller stores the block and notifies the parent row); without,
nothing changes. Returns the updated block and the bounds `(x, y, width, height)`. -/
def placeRectsInInternal (blk : Block) (width : Float) (placeRects : Bool) : ElkM (Block × ElkRectangle) := do
  let nns := blk.nodeNodeSpacing
  let mut currentX : Float := 0.0
  let mut currentY := blk.y
  let mut currentWidth : Float := 0.0
  let mut currentHeight : Float := 0.0
  let mut maxHeightInRow : Float := 0.0
  let mut widthInRow : Float := 0.0
  let mut row := 0
  let mut rows : Array BlockRow := if placeRects then #[BlockRow.new blk.x blk.y nns] else #[]
  let mut index := 0
  for rect in blk.children do
    let n ← ElkM.getNode rect
    let rectWidth := n.width
    let rectHeight := n.height
    if currentX + rectWidth + (if index > 0 then nns else 0.0) > width && maxHeightInRow > 0.0 then
      currentX := 0.0
      currentY := currentY + (maxHeightInRow + nns)
      currentWidth := fmax currentWidth widthInRow
      currentHeight := currentHeight + (maxHeightInRow + nns)
      maxHeightInRow := 0.0
      widthInRow := 0.0
      if placeRects then
        row := row + 1
        rows := rows.push (BlockRow.new blk.x currentY nns)
      index := 0
    widthInRow := widthInRow + (rectWidth + (if index > 0 then nns else 0.0))
    maxHeightInRow := fmax maxHeightInRow rectHeight
    if placeRects then
      if h : row < rows.size then
        let r ← BlockRow.addRectangle rows[row] rect
        rows := rows.set! row r
    currentX := currentX + (rectWidth + (if index > 0 then nns else 0.0))
    index := index + 1
  currentWidth := fmax currentWidth widthInRow
  currentHeight := currentHeight + maxHeightInRow
  let blk := if placeRects then { blk with rows, width := currentWidth, height := currentHeight } else blk
  return (blk, ElkRectangle.ofValues blk.x blk.y currentWidth currentHeight)

/-- `place_rects_in_width_height(width, height, false)`: whether the children fit into
`width × height` (computed on a copy, nothing moves). -/
def fitsInWidthHeight (blk : Block) (width height : Float) : ElkM Bool := do
  let (_, bounds) ← placeRectsInInternal blk width false
  return bounds.width <= width && bounds.height <= height

/-- `width_for_target_height(height)`: the smallest width (binary search between `minWidth` and
`width`, step > 1) for which the children fit into the height. -/
def widthForTargetHeight (b : BlockId) (height : Float) : RectPackingM Float := do
  let blk ← getBlock b
  if blk.maxHeight <= height then return blk.minWidth
  if ← fitsInWidthHeight blk blk.minWidth height then return blk.minWidth
  let mut upperBound := blk.width
  let mut lowerBound := blk.minWidth
  let mut viableWidth := blk.width
  let mut newWidth := (upperBound - lowerBound) / 2.0 + lowerBound
  while lowerBound + 1.0 < upperBound do
    if ← fitsInWidthHeight blk newWidth height then
      viableWidth := newWidth
      upperBound := newWidth
    else
      lowerBound := newWidth
    newWidth := (upperBound - lowerBound) / 2.0 + lowerBound
  return viableWidth

/-- `height_for_target_width(width)`: the height of the children laid out in `width` (on a copy). -/
def heightForTargetWidth (b : BlockId) (width : Float) : RectPackingM Float := do
  let (_, bounds) ← placeRectsInInternal (← getBlock b) width false
  return bounds.height

/-- Places the rectangles in `width`, stores the block and notifies the parent row. -/
private def placeRectsInStore (b : BlockId) (width : Float) : RectPackingM ElkRectangle := do
  let (blk, bounds) ← placeRectsInInternal (← getBlock b) width true
  setBlock b blk
  notifyParent b
  return bounds

/-- `place_rects_in_width_height_public(width, height)`: places the rectangles in `width` and
returns whether they fit into `width × height`. -/
def placeRectsInWidthHeightPublic (b : BlockId) (width height : Float) : RectPackingM Bool := do
  let bounds ← placeRectsInStore b width
  return bounds.width <= width && bounds.height <= height

/-- `place_rects_in(width)`: places the rectangles in `width`; `true` if the size changed. -/
def placeRectsIn (b : BlockId) (width : Float) : RectPackingM Bool := do
  let blk ← getBlock b
  let oldWidth := blk.width
  let oldHeight := blk.height
  let bounds ← placeRectsInStore b width
  return bounds.width != oldWidth || bounds.height != oldHeight

/-- `expand(additional_width_per_block, additional_height_for_block)`: grows the block and
expands every block row to the new width with an equal share of the additional height. -/
def expand (b : BlockId) (additionalWidthPerBlock additionalHeightForBlock : Float) : RectPackingM Unit := do
  let blk ← getBlock b
  let widthForRow := blk.width + additionalWidthPerBlock
  let additionalHeightForRow := additionalHeightForBlock / blk.rows.size.toFloat
  let mut rows := blk.rows
  for index in [0:rows.size] do
    let row ← BlockRow.expand rows[index]! widthForRow additionalHeightForRow index
    rows := rows.set! index row
  setBlock b { blk with width := blk.width + additionalWidthPerBlock,
                        height := blk.height + additionalHeightForBlock, rows }

/-- `reset_block()` (`adjust_size_after_remove`). -/
def resetBlock (b : BlockId) : RectPackingM Unit := adjustSizeAfterRemove b

/-- `last_row()`: the last block row (Rust panics without rows; `default` here). -/
def lastRow (blk : Block) : BlockRow := blk.rows[blk.rows.size - 1]!

/-- `last_row_new_x()`: the right end of the last block row. -/
def lastRowNewX (blk : Block) : Float :=
  let r := lastRow blk
  r.x + r.width

/-- `last_row_y()`. -/
def lastRowY (blk : Block) : Float := (lastRow blk).y

/-- `set_width(width)`. -/
def setWidth (b : BlockId) (width : Float) : RectPackingM Unit := modifyBlock b fun x => { x with width }
/-- `set_height(height)`. -/
def setHeight (b : BlockId) (height : Float) : RectPackingM Unit := modifyBlock b fun x => { x with height }
/-- `set_parent_row(parent_row)`. -/
def setParentRow (b : BlockId) (row : RectRowId) : RectPackingM Unit :=
  modifyBlock b fun x => { x with parentRow := some row }
/-- `set_stack(stack)`. -/
def setStack (b : BlockId) (stack : Option BlockStackId) : RectPackingM Unit :=
  modifyBlock b fun x => { x with stack }
/-- `set_fixed(fixed)`. -/
def setFixed (b : BlockId) (fixed : Bool) : RectPackingM Unit := modifyBlock b fun x => { x with fixed }
/-- `set_position_fixed(position_fixed)`. -/
def setPositionFixed (b : BlockId) (positionFixed : Bool) : RectPackingM Unit :=
  modifyBlock b fun x => { x with positionFixed }
/-- `set_smallest_rect_width(value)`. -/
def setSmallestRectWidth (b : BlockId) (value : Float) : RectPackingM Unit :=
  modifyBlock b fun x => { x with smallestRectWidth := value }

end Block

end Elk.Alg.RectPacking.Util
