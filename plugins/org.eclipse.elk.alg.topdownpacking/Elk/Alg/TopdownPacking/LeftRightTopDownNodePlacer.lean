import Elk.Core.Alg
import Elk.Core.Math
import Elk.Core.Options
import Elk.Core.Util.Java
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.TopdownPacking.Grid
import Elk.Alg.TopdownPacking.GridElkNode
import Elk.Alg.TopdownPacking.INodeArranger
import Elk.Alg.TopdownPacking.TopdownPackingPhases
import Elk.Alg.TopdownPacking.Options.TopdownpackingOptions
/-!
# `org.eclipse.elk.alg.topdownpacking.LeftRightTopDownNodePlacer`

Port of `left_right_top_down_node_placer.rs` (elk-rs): phase 1 of topdown packing. Places the
children of a node on a `cols x rows` grid (`cols = ceil(sqrt(n))`), left to right and top to
bottom, each with the hierarchical node width / aspect ratio of the parent. Also the
`INodeArranger` predicting the resulting graph size.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0

namespace Elk.Alg.TopdownPacking

open Elk.Graph Elk.Core.Alg Elk.Core.Math Elk.Core.Util Elk.Core.Options
open Elk.Alg.TopdownPacking.Options

namespace LeftRightTopDownNodePlacer

/-- `get_predicted_size(graph)` (`INodeArranger`): the size needed to arrange all children of
`graph`. Computed on `i32` columns/rows like Rust (`cols == 0` yields `-1` gaps). -/
def getPredictedSize (graph : NodeId) : ElkM KVector := do
  let node ← ElkM.getNode graph
  let numberOfChildren := node.children.size
  let padding := node.props.getD TopdownpackingOptions.PADDING {}
  let nodeNodeSpacing := node.props.getD TopdownpackingOptions.SPACING_NODE_NODE fl0p0
  let hierarchicalNodeWidth := node.props.getD CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH fl0p0
  let hierarchicalNodeAspectRatio := node.props.getD CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO fl1p0
  let cols : Int := Float.toIntTrunc (Float.ceil (Float.sqrt numberOfChildren.toFloat))
  let requiredWidth := Int.toFloat cols * hierarchicalNodeWidth
    + padding.left + padding.right + Int.toFloat (cols - 1) * nodeNodeSpacing
  let rows : Int := if (numberOfChildren : Int) > cols * cols - cols || cols == 0 then cols else cols - 1
  let requiredHeight := Int.toFloat rows * hierarchicalNodeWidth / hierarchicalNodeAspectRatio
    + padding.top + padding.bottom + Int.toFloat (rows - 1) * nodeNodeSpacing
  return ⟨requiredWidth, requiredHeight⟩

/-- The `INodeArranger` of this strategy. -/
def arranger : INodeArranger := { getPredictedSize := getPredictedSize }

/-- `process(layout_graph, progress_monitor)`: the node placement phase. -/
def process (_layoutGraph : GridElkNode) (monitor : ProgressMonitor) : GridM Unit := do
  let _ ← monitor.begin "Node placement" 1.0
  let wrapper ← get
  monitor.log s!"Node placement began for node {← wrapper.identifier}"
  let node ← ElkM.getNode wrapper.node
  let padding := node.props.getD TopdownpackingOptions.PADDING {}
  let nodeNodeSpacing := node.props.getD TopdownpackingOptions.SPACING_NODE_NODE 0.0
  let graphSize ← getPredictedSize wrapper.node
  wrapper.setDimensions (fmax node.width graphSize.x) (fmax node.height graphSize.y)
  let nodes ← wrapper.children
  let cols : Nat := (Float.toIntTrunc (Float.ceil (Float.sqrt nodes.size.toFloat))).toNat
  let rows : Nat := if nodes.size > cols * cols - cols || cols == 0 then cols else cols - 1
  modify fun g => Grid.setGridSize g cols rows
  monitor.log s!"{← wrapper.identifier}\nPlacing {nodes.size} nodes in {cols} columns."
  monitor.done
  monitor.log "Node Arrangement done!"
  let mut currX := padding.left
  let mut currY := padding.top
  let mut currentCol := 0
  let mut currentRow := 0
  let desiredNodeWidth := node.props.getD CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH 0.0
  let aspectRatio := node.props.getD CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO 1.0
  for child in nodes do
    ElkM.modifyNode child fun n => { n with width := desiredNodeWidth, height := desiredNodeWidth / aspectRatio }
    ElkM.modifyNode child fun n => { n with x := currX }
    ElkM.modifyNode child fun n => { n with y := currY }
    monitor.log s!"currX: {Float.toRustDisplay currX}"
    monitor.log s!"currY: {Float.toRustDisplay currY}"
    let g ← get
    set (← GridM.liftExcept (Grid.put g currentCol currentRow child))
    monitor.logGraph s!"{(← ElkM.getNode child).identifier.getD ""} placed in ({currentCol}|{currentRow})"
    currX := currX + ((← ElkM.getNode child).width + nodeNodeSpacing)
    currentCol := currentCol + 1
    if currentCol >= cols then
      currX := padding.left
      currY := currY + (desiredNodeWidth / aspectRatio + nodeNodeSpacing)
      currentCol := 0
      currentRow := currentRow + 1
  monitor.log "Node Placing done!"
  monitor.logGraph "Graph after node placement"
  monitor.done

/-- The phase (`ILayoutPhase`) with an empty processor configuration. -/
def phase : LayoutPhase GridM TopdownPackingPhases GridElkNode TopdownPackingProcessors :=
  { name := "LeftRightTopDownNodePlacer"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure (some LayoutProcessorConfiguration.create) }

end LeftRightTopDownNodePlacer

end Elk.Alg.TopdownPacking
