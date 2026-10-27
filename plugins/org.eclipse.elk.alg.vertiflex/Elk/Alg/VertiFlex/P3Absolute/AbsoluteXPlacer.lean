import Elk.Core.Alg
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.VertiFlex.VertiFlexLayoutPhases
import Elk.Alg.VertiFlex.VertiFlexUtil
/-!
# `org.eclipse.elk.alg.vertiflex.p3absolute.AbsoluteXPlacer`

Port of `absolute_x_placer.rs` (elk-rs): phase 3 of VertiFlex. The relative x coordinates of
phase 2 (relative to the parent) are turned into absolute coordinates, shifted such that the
leftmost node ends up at `x = 0`.
-/
namespace Elk.Alg.VertiFlex.P3Absolute

open Elk.Graph Elk.Core.Alg Elk.Core.Util

namespace AbsoluteXPlacer

/-- `find_minimal_x(tree)`: the minimal x (relative to the root of the tree) of a subtree; the
minimum is clamped at `0.0` for inner nodes like in Rust. -/
partial def findMinimalX (tree : NodeId) : ElkM Float := do
  let children ← VertiFlexUtil.outgoingChildren tree
  let treeX := (← ElkM.getNode tree).x
  if children.isEmpty then
    return treeX
  else
    let mut minSubtreeX := 0.0
    for child in children do
      let testX ← findMinimalX child
      if testX < minSubtreeX then
        minSubtreeX := testX
    return minSubtreeX + treeX

/-- `absolute_tree_coords(tree)`: adds the x of the parent to every descendant (top down). -/
partial def absoluteTreeCoords (tree : NodeId) : ElkM Unit := do
  let children ← VertiFlexUtil.outgoingChildren tree
  if !children.isEmpty then
    let baseX := (← ElkM.getNode tree).x
    for child in children do
      ElkM.modifyNode child fun nd => { nd with x := nd.x + baseX }
      absoluteTreeCoords child

/-- `process(graph, progress_monitor)`. -/
def process (graph : NodeId) (monitor : ProgressMonitor) : VertiFlexM Unit := do
  let _ ← monitor.begin "AbsolutPlacer" 1.0
  let hasChildren := !(← ElkM.getNode graph).children.isEmpty
  if hasChildren then
    if let some parent ← VertiFlexUtil.findRoot graph then
      let newX := (← ElkM.getNode parent).x - (← findMinimalX parent)
      ElkM.modifyNode parent fun nd => { nd with x := newX }
      absoluteTreeCoords parent
  monitor.done

/-- The phase (`ILayoutPhase`) without a processor configuration. -/
def phase : VertiFlexPhase :=
  { name := "AbsoluteXPlacer"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure none }

end AbsoluteXPlacer

end Elk.Alg.VertiFlex.P3Absolute
