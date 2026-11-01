import Elk.Core.Alg
import Elk.Core.Options
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.TopdownPacking.Grid
import Elk.Alg.TopdownPacking.GridElkNode
import Elk.Alg.TopdownPacking.TopdownPackingPhases
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.topdownpacking.BottomRowEqualWhitespaceEliminator`

Port of `bottom_row_equal_whitespace_eliminator.rs` (elk-rs): phase 2 of topdown packing.
Distributes the horizontal whitespace of every row equally among the row's nodes (widening
them), then the vertical whitespace below the last row among the nodes.
-/

namespace Elk.Alg.TopdownPacking

open Elk.Graph Elk.Core.Alg Elk.Core.Util Elk.Core.Options

namespace BottomRowEqualWhitespaceEliminator

/-- `process(layout_graph, progress_monitor)`: the whitespace elimination phase. -/
def process (_layoutGraph : GridElkNode) (monitor : ProgressMonitor) : GridM Unit := do
  let _ ← monitor.begin "Whitespace elimination" fl1p0
  let wrapper ← get
  monitor.log s!"Whitespace elimination began for node {← wrapper.identifier}"
  if (← wrapper.width) == fl0p0 || wrapper.cols == 0 then
    monitor.log "Parent node has no width, skipping phase"
    monitor.done
    return
  let padding := (← ElkM.getNode wrapper.node).props.getD CoreOptions.PADDING {}
  for rowIndex in [0:wrapper.rows] do
    let row ← GridM.liftExcept (Grid.getRow wrapper rowIndex)
    if row.isEmpty then continue
    let mut lastIndex := row.size
    let mut last : Option NodeId := none
    while last.isNone do
      if lastIndex == 0 then break
      lastIndex := lastIndex - 1
      last := row[lastIndex]!
    let some lastNode := last | continue
    let ln ← ElkM.getNode lastNode
    let rightBorder := ln.x + ln.width
    let layoutWidth ← wrapper.width
    if rightBorder + padding.right < layoutWidth then
      monitor.log s!"Eliminate white space in row {rowIndex}"
      let extraSpace := layoutWidth - (rightBorder + padding.right)
      let extraSpacePerNode := extraSpace / (lastIndex.toFloat + fl1p0)
      let mut accumulatedShift := fl0p0
      for item in row.take (lastIndex + 1) do
        if let some n := item then
          ElkM.modifyNode n fun nd => { nd with x := nd.x + accumulatedShift }
          ElkM.modifyNode n fun nd => { nd with width := nd.width + extraSpacePerNode }
        accumulatedShift := accumulatedShift + extraSpacePerNode
  let col ← GridM.liftExcept (Grid.getColumn wrapper 0)
  let last : Option NodeId := col.reverse.findSome? id
  let some lastNode := last
    | monitor.logGraph "Graph after whitespace elimination"
      monitor.done
  let ln ← ElkM.getNode lastNode
  let bottomBorder := ln.y + ln.height
  let layoutHeight ← wrapper.height
  let extraSpace := layoutHeight - (bottomBorder + padding.bottom)
  let extraSpacePerNode := extraSpace / (col.size.toFloat + fl1p0)
  let mut accumulatedShift := fl0p0
  monitor.log "Eliminate vertical white space"
  if bottomBorder + padding.bottom < layoutHeight then
    for rowIndex in [0:wrapper.rows] do
      let row ← GridM.liftExcept (Grid.getRow wrapper rowIndex)
      for item in row do
        let some n := item | break
        ElkM.modifyNode n fun nd => { nd with y := nd.y + accumulatedShift }
        ElkM.modifyNode n fun nd => { nd with height := nd.height + extraSpacePerNode }
        accumulatedShift := accumulatedShift + extraSpacePerNode
  monitor.logGraph "Graph after whitespace elimination"
  monitor.done

/-- The phase (`ILayoutPhase`) with an empty processor configuration. -/
def phase : LayoutPhase GridM TopdownPackingPhases GridElkNode TopdownPackingProcessors :=
  { name := "BottomRowEqualWhitespaceEliminator"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure (some LayoutProcessorConfiguration.create) }

end BottomRowEqualWhitespaceEliminator

end Elk.Alg.TopdownPacking
