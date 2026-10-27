import Elk.Core.Alg
import Elk.Core.Util.Sort
import Elk.Alg.RectPacking.Util.RectPackingArena
import Elk.Alg.RectPacking.Options.RectPackingOptions
/-!
# `org.eclipse.elk.alg.rectpacking.intermediate.InteractiveNodeReorderer`

Port of `intermediate/interactive_node_reorderer.rs` (elk-rs): children with a
`DESIRED_POSITION` are taken out, sorted by that position and re-inserted at it (clamped to
`[0, remaining count]`); afterwards every child gets its index as `CURRENT_POSITION` and the
children are stored in the new order.

Sort order: the comparator returns `Less` for equal positions (Java `-1`), which is not a
consistent order. Rust `sort_by` uses insertion sort for at most 20 elements; with this
comparator it yields ascending positions with equal positions in **reverse** input order. That
order is reproduced exactly (stable sort of the reversed list); for more than 20 nodes with equal
desired positions Rust's driftsort may order the ties differently (not reproduced).

Rust deviation from Java kept: the insertion index is clamped at 0 (Java throws for a negative
desired position).
-/
namespace Elk.Alg.RectPacking.Intermediate

open Elk.Graph Elk.Core.Util Elk.Core.Alg Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options

namespace InteractiveNodeReorderer

/-- `get_desired_position(node)`: `DESIRED_POSITION` (default `-1`). -/
def getDesiredPosition (graph : ElkGraph) (node : NodeId) : Int :=
  (graph.node node).props.getD RectPackingOptions.DESIRED_POSITION (-1)

/-- Rust `fixed_nodes.sort_by(…)` with the `Less`-on-equal comparator (see the module doc). -/
def sortFixedNodes (graph : ElkGraph) (fixedNodes : Array NodeId) : Array NodeId :=
  stableSort fixedNodes.reverse fun a b =>
    Ord.compare (getDesiredPosition graph a) (getDesiredPosition graph b)

/-- `process(graph, progress_monitor)` on the `ElkGraph`. -/
def run (graph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "Interactive Node Reorderer" 1.0
  let mut rectangles := (← ElkM.getNode graph).children
  let mut fixedNodes : Array NodeId := #[]
  for rect in rectangles do
    if (← ElkM.getNode rect).props.has RectPackingOptions.DESIRED_POSITION then
      fixedNodes := fixedNodes.push rect
  rectangles := rectangles.filter fun n => !fixedNodes.contains n
  let g ← get
  fixedNodes := sortFixedNodes g fixedNodes
  for node in fixedNodes do
    let position := getDesiredPosition g node
    let insertPos := (max (min position (rectangles.size : Int)) 0).toNat
    rectangles := rectangles.insertIdxIfInBounds insertPos node
  let mut index : Int := 0
  for node in rectangles do
    ElkM.setNodeProp node RectPackingOptions.CURRENT_POSITION index
    index := index + 1
  ElkM.modifyNode graph fun n => { n with children := rectangles }
  monitor.done

/-- `InteractiveNodeReorderer` as an `ILayoutProcessor<ElkNode>`. -/
def processor : LayoutProcessor RectPackingM NodeId :=
  { name := "InteractiveNodeReorderer", process := fun graph monitor => run graph monitor }

end InteractiveNodeReorderer

end Elk.Alg.RectPacking.Intermediate
