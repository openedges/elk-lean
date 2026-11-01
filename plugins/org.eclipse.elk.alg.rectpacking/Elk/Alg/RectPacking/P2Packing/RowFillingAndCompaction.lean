import Elk.Core.Math
import Elk.Core.Alg
import Elk.Alg.RectPacking.Options.InternalProperties
import Elk.Alg.RectPacking.P2Packing.Compaction
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.rectpacking.p2packing.RowFillingAndCompaction`

Port of `p2packing/row_filling_and_compaction.rs` (elk-rs): the initial placement followed by the
row-wise compaction; records the potential row width changes used by further compaction
iterations and stores the rows (`RowsStorage`) for the whitespace elimination.

The Rust object is mutable (`&mut self`); `start` returns the drawing and the updated object.

Java semantics (ELK Java is the reference; elk-rs differed):
* After a row has to be compacted again, Java compacts the **same** row again (`rowIdx--` followed
  by the loop's `rowIdx++`); elk-rs continued with the previous row (`row_idx - 1`, or row 0
  again), which moved later rows onto earlier ones.
* The rectangles laid out are the children of `layout_graph` (the clone in later compaction
  iterations); the `rectangles` argument is unused (as in Java).
* `Math.max`/`Math.min` (NaN propagating; elk-rs `f64::max`/`f64::min`).
* The special case of a single row reads the last stack / last block with `List.get(size - 1)`
  (Java's `IndexOutOfBoundsException` for an empty list; elk-rs skipped it).
-/

namespace Elk.Alg.RectPacking.P2Packing

open Elk.Graph Elk.Core.Util Elk.Core.Math Elk.Core.Alg
open Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options
open RectPackingM

/-- `RowFillingAndCompaction`. -/
structure RowFillingAndCompaction where
  aspectRatio : Float
  nodeNodeSpacing : Float
  potentialRowWidthDecreaseMin : Float := Float.posInf
  potentialRowWidthDecreaseMax : Float := fl0p0
  potentialRowWidthIncreaseMin : Float := Float.posInf
  potentialRowWidthIncreaseMax : Float := fl0p0
  deriving Inhabited, Repr

namespace RowFillingAndCompaction

/-- `RowFillingAndCompaction::new(aspect_ratio, node_node_spacing)`. -/
def new (aspectRatio nodeNodeSpacing : Float) : RowFillingAndCompaction := { aspectRatio, nodeNodeSpacing }

/-- `adjust_width_and_height(row)`: updates the stack dimensions and sets the row height (maximum
stack height) and width (stack widths plus spacing). -/
def adjustWidthAndHeight (self : RowFillingAndCompaction) (row : RectRowId) : RectPackingM Unit := do
  let stacks := (← getRow row).stacks
  let mut maxHeight : Float := fl0p0
  let mut maxWidth : Float := fl0p0
  let mut index := 0
  for stack in stacks do
    BlockStack.updateDimension stack
    let st ← getStack stack
    maxHeight := javaMax maxHeight st.height
    maxWidth := maxWidth + (st.width + (if index > 0 then self.nodeNodeSpacing else fl0p0))
    index := index + 1
  RectRow.setHeight row maxHeight
  RectRow.setWidth row maxWidth

/-- `start(rectangles, progress_monitor, layout_graph, padding)`: places and compacts the
children of `layoutGraph`, sets `ADDITIONAL_HEIGHT` and `ROWS` on it and returns the drawing
(`WHOLE_DRAWING`) together with the updated object. -/
def start (self : RowFillingAndCompaction) (_rectangles : Array NodeId) (_monitor : ProgressMonitor)
    (layoutGraph : NodeId) (padding : ElkPadding) : RectPackingM (DrawingData × RowFillingAndCompaction) := do
  let mut self := self
  let nns := self.nodeNodeSpacing
  let props := (← ElkM.getNode layoutGraph).props
  let targetWidth := (props.get InternalProperties.TARGET_WIDTH).getD fl0p0
  let minWidth := (props.get InternalProperties.MIN_WIDTH).getD fl0p0
  let minHeight := (props.get InternalProperties.MIN_HEIGHT).getD fl0p0
  let rectangles := (← ElkM.getNode layoutGraph).children
  DrawingUtil.resetCoordinates rectangles
  let mut rows ← InitialPlacement.place rectangles targetWidth nns
  let rowHeightReevaluation :=
    ((← ElkM.getNode layoutGraph).props.get RectPackingOptions.PACKING_COMPACTION_ROW_HEIGHT_REEVALUATION).getD false
  let mut rowIdx := 0
  while rowIdx < rows.size do
    let currentRow := rows[rowIdx]!
    if rowIdx != 0 then
      let prev ← getRow rows[rowIdx - 1]!
      RectRow.setY currentRow (prev.y + prev.height + nns)
    let ((_somethingChanged, compactRowAgain), rows') ←
      Compaction.compact rowIdx rows targetWidth nns rowHeightReevaluation
    rows := rows'
    if compactRowAgain then
      let blocks := (← getRow currentRow).children
      for block in blocks do
        Block.setFixed block false
        Block.setPositionFixed block false
        Block.resetBlock block
      RectRow.resetStacks currentRow
      RectRow.setWidth currentRow targetWidth
      -- Java `rowIdx--` + the loop's `rowIdx++`: the same row again
    else
      self.adjustWidthAndHeight currentRow
      if h : rowIdx + 1 < rows.size then
        let nextRow := rows[rowIdx + 1]
        let currentRowWidth := (← getRow currentRow).width
        let nextRowFirstBlockWidth := (← getBlock (← RectRow.getFirstBlock nextRow)).width
        let increase := currentRowWidth + nns + nextRowFirstBlockWidth - targetWidth
        self := { self with
          potentialRowWidthIncreaseMax := javaMax increase self.potentialRowWidthDecreaseMax
          potentialRowWidthIncreaseMin := javaMin increase self.potentialRowWidthDecreaseMin }
        let stacks := (← getRow currentRow).stacks
        if let some lastStack := stacks.back? then
          let lastStackWidth := (← getStack lastStack).width
          let spacing := if stacks.size <= 1 then fl0p0 else nns
          let decreaseValue := lastStackWidth + spacing
          self := { self with potentialRowWidthDecreaseMax := javaMax self.potentialRowWidthDecreaseMax decreaseValue }
          self := { self with potentialRowWidthDecreaseMin := javaMin self.potentialRowWidthDecreaseMax decreaseValue }
      if rows.size == 1 then
        let stacks := (← getRow currentRow).stacks
        let some lastStack := stacks.back?
          | throw (IO.userError "java.lang.IndexOutOfBoundsException: Index -1 out of bounds for length 0")
        let some lastBlock := (← getStack lastStack).blocks.back?
          | throw (IO.userError "java.lang.IndexOutOfBoundsException: Index -1 out of bounds for length 0")
        let blk ← getBlock lastBlock
        let lastBlockWidth := blk.width
        for blockRow in blk.rows do
          let decrease := lastBlockWidth - blockRow.width
          self := { self with
            potentialRowWidthDecreaseMax := javaMax self.potentialRowWidthDecreaseMax decrease
            potentialRowWidthDecreaseMin := javaMin self.potentialRowWidthDecreaseMin decrease }
          let increase := blockRow.width + nns
          self := { self with
            potentialRowWidthIncreaseMax := javaMax self.potentialRowWidthIncreaseMax increase
            potentialRowWidthIncreaseMin := javaMin self.potentialRowWidthIncreaseMin increase }
      rowIdx := rowIdx + 1
  let size ← DrawingUtil.calculateDimensions rows nns
  let totalWidth := javaMax size.x (minWidth - (padding.left + padding.right))
  let height := javaMax size.y (minHeight - (padding.top + padding.bottom))
  let additionalHeight := height - size.y
  ElkM.setNodeProp layoutGraph InternalProperties.ADDITIONAL_HEIGHT additionalHeight
  let rowsKey ← RowsStorage.storeRows layoutGraph rows
  ElkM.setNodeProp layoutGraph InternalProperties.ROWS rowsKey
  return (DrawingData.new self.aspectRatio totalWidth (size.y + additionalHeight) .wholeDrawing, self)

end RowFillingAndCompaction

end Elk.Alg.RectPacking.P2Packing
