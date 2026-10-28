import Elk.Core.Alg
import Elk.Core.Util.Sort
import Elk.Core.Util.JavaSort
import Elk.Alg.RectPacking.Util.RectPackingArena
import Elk.Alg.RectPacking.Options.RectPackingOptions
/-!
# `org.eclipse.elk.alg.rectpacking.intermediate.InteractiveNodeReorderer`

Port of `InteractiveNodeReorderer.java` (elk-rs `intermediate/interactive_node_reorderer.rs`):
children with a `DESIRED_POSITION` are taken out, sorted by that position and re-inserted at it
(clamped to the remaining count); afterwards every child gets its index as `CURRENT_POSITION` and
the children are stored in the new order.

Sort order: the comparator returns `-1` for equal positions, which is not a consistent order, so
JDK `TimSort` decides the result (`javaSortBy`, `Collections.sort`; elk-rs used Rust's sort).

A negative desired position is inserted with `children.add(position, node)` into the EMF list:
`BasicEList.addUnique` calls `System.arraycopy(data, position, …)`, which throws
`ArrayIndexOutOfBoundsException: arraycopy: source index <position> out of bounds for object
array[<capacity>]` — the capacity of the children list's array, grown one child at a time by the
graph import (`BasicEList.grow`: `c + c / 2 + 4` from 0: 4, 10, 19, 32, 52, …). (elk-rs clamped the
position at 0.)
-/
namespace Elk.Alg.RectPacking.Intermediate

open Elk.Graph Elk.Core.Util Elk.Core.Alg Elk.Alg.RectPacking.Util Elk.Alg.RectPacking.Options

namespace InteractiveNodeReorderer

/-- `get_desired_position(node)`: `DESIRED_POSITION` (default `-1`). -/
def getDesiredPosition (graph : ElkGraph) (node : NodeId) : Int :=
  (graph.node node).props.getD RectPackingOptions.DESIRED_POSITION (-1)

/-- `Collections.sort(fixedNodes, …)` with the `-1`-on-equal comparator (see the module doc). -/
def sortFixedNodes (graph : ElkGraph) (fixedNodes : Array NodeId) : Except String (Array NodeId) :=
  javaSortBy fixedNodes fun a b =>
    let pa := getDesiredPosition graph a
    let pb := getDesiredPosition graph b
    if pa == pb then .lt else Ord.compare pa pb

/-- The capacity of an EMF `BasicEList` array after adding `n` elements one by one
(`BasicEList.grow`: `newCapacity = oldCapacity + oldCapacity / 2 + 4`). -/
def emfListCapacity (n : Nat) : Nat := Id.run do
  let mut c := 0
  for _ in [0:n + 1] do
    if c ≥ n then break
    c := c + c / 2 + 4
  return c

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
  fixedNodes ← match sortFixedNodes g fixedNodes with
    | .ok sorted => pure sorted
    | .error e => throw (IO.userError s!"java.lang.IllegalArgumentException: {e}")
  let capacity := emfListCapacity (← ElkM.getNode graph).children.size
  for node in fixedNodes do
    let position := min (getDesiredPosition g node) (rectangles.size : Int)
    if position < 0 then
      throw (IO.userError
        s!"java.lang.ArrayIndexOutOfBoundsException: arraycopy: source index {position} out of bounds for object array[{capacity}]")
    rectangles := rectangles.insertIdxIfInBounds position.toNat node
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
