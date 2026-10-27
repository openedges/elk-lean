import Elk.Alg.Common.Utils.Utils
import Elk.Alg.Spore.SporePhases
/-!
# `org.eclipse.elk.alg.spore.p3execution.GrowTreePhase`

Port of `p3execution/grow_tree_phase.rs` (elk-rs) and `GrowTreePhase.java`: the execution phase of
the overlap removal. Traverses the spanning tree depth first (child by child, each child's subtree
completely before the next sibling); every child is first translated by the displacement of its
parent, then moved along the line from the parent's original center to its own original center,
scaled by the overlap factor `Utils.overlap(parent.rect, child.rect)` so that the two rectangles
just touch. Sets `OVERLAPS_EXISTED` if any pair overlapped (`factor > 1`). Without a tree (empty
graph) nothing happens and the property is not set. The SVG debug output is not ported
(TODO(debug)).
-/
namespace Elk.Alg.Spore.P3Execution

open Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Alg.Common Elk.Alg.Common.Spore Elk.Alg.Common.Utils
open Elk.Alg.Spore.Graph

namespace GrowTreePhase

/-- Rust `grow_at` for the subtree `c` below the (already placed) node `parent`: returns the
placed subtree and whether an overlap was found (`overlaps` is the accumulated flag). -/
def growSubtree (parent : Node) (c : Tree Node) (overlaps : Bool) : Tree Node × Bool := Id.run do
  let delta := parent.vertex - parent.originalVertex
  let translated := c.node.translate delta
  let t := Utils.overlap parent.rect translated.rect
  let mut overlaps := overlaps
  if t > 1.0 then overlaps := true
  let direction := (translated.originalVertex - parent.originalVertex).scale t
  let newCenter := parent.vertex + direction
  let placed := translated.setCenterPosition newCenter
  let mut children : Array (Tree Node) := #[]
  for _h : grandchild in c.children do
    let (gc, ov) := growSubtree placed grandchild overlaps
    children := children.push gc
    overlaps := ov
  return ({ node := placed, children }, overlaps)
termination_by c
decreasing_by exact Tree.sizeOf_lt_of_mem ‹_›

/-- Rust `grow_at(root, ...)`: grows the whole tree below its (unchanged) root. -/
def growTree (root : Tree Node) : Tree Node × Bool := Id.run do
  let mut overlaps := false
  let mut children : Array (Tree Node) := #[]
  for child in root.children do
    let (c, ov) := growSubtree root.node child overlaps
    children := children.push c
    overlaps := ov
  return ({ root with children }, overlaps)

/-- `process(graph, progressMonitor)`: the grow tree phase. -/
def process (_graph : Unit) (monitor : ProgressMonitor) : SporeM Unit := do
  let _ ← monitor.begin "Grow Tree" 1.0
  modify fun g =>
    match g.tree with
    | none => g
    | some root =>
      let (tree, overlapsExisted) := growTree root
      ({ g with tree := some tree }).setProperty InternalProperties.OVERLAPS_EXISTED overlapsExisted
  monitor.done

/-- The `GrowTreePhase` phase (no intermediate processors). -/
def phase : SporePhase :=
  { name := "GrowTreePhase", process := process, getLayoutProcessorConfiguration := fun _ => noProcessors }

end GrowTreePhase

end Elk.Alg.Spore.P3Execution
