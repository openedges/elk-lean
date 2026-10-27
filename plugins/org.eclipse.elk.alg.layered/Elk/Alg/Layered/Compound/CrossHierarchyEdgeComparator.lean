import Elk.Alg.Layered.Compound.CrossHierarchyMap
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.compound.CrossHierarchyEdgeComparator`

Port of `hierarchy_level` and `sort_cross_hierarchy_edges` of `compound/mod.rs` (elk-rs):
sorts the segments of a cross-hierarchy edge from the start to the end segment: `OUTPUT`
segments before `INPUT` segments, `OUTPUT` segments from deeper to higher levels, `INPUT`
segments from higher to deeper levels.

The comparator is a weak order on the `INPUT`/`OUTPUT` segments the processors create, so the
stable `stableSort` yields the same order as Rust's stable `sort_by`. The hierarchy levels are
computed once per segment before sorting (the comparator is pure); a segment graph that is not
a descendant of the top-level graph (Rust `expect` panic, Java `IllegalArgumentException`)
gets level `0`.
-/
namespace Elk.Alg.Layered.Compound

open Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

namespace CrossHierarchyEdgeComparator

/-- `hierarchyLevel(nestedGraph, topLevelGraph)`: the number of parent steps from the nested
graph to the top-level graph (`none` if it is not a descendant). -/
def hierarchyLevel (nestedGraph topGraph : LGraphId) : LayeredM (Option Int) := do
  let mut current := nestedGraph
  let mut level : Int := 0
  let mut result : Option Int := none
  -- every step goes to the parent graph; the arena hierarchy is finite and acyclic
  while true do
    if current == topGraph then
      result := some level
      break
    let some parentNode := (← LayeredM.getGraph current).parentNode | break
    let some parentGraph ← LayeredM.nodeGraph parentNode | break
    current := parentGraph
    level := level + 1
  return result

/-- `compare(edge1, edge2)` given the hierarchy levels of both segments. -/
def compareWithLevels (edge1 : CrossHierarchyEdge) (level1 : Int) (edge2 : CrossHierarchyEdge) (level2 : Int) :
    Ordering :=
  if edge1.portType == .output && edge2.portType == .input then .lt
  else if edge1.portType == .input && edge2.portType == .output then .gt
  else
    let diff := if edge1.portType == .output then level2 - level1 else level1 - level2
    compare diff 0

/-- Rust `sort_cross_hierarchy_edges(edges, graph)` (Java
`Collections.sort(edges, new CrossHierarchyEdgeComparator(graph))`). -/
def sortCrossHierarchyEdges (edges : Array CrossHierarchyEdge) (graph : LGraphId) :
    LayeredM (Array CrossHierarchyEdge) := do
  let mut keyed : Array (CrossHierarchyEdge × Int) := #[]
  for e in edges do
    keyed := keyed.push (e, (← hierarchyLevel e.graph graph).getD 0)
  let sorted := stableSort keyed fun (e1, l1) (e2, l2) => compareWithLevels e1 l1 e2 l2
  return sorted.map (·.1)

end CrossHierarchyEdgeComparator

end Elk.Alg.Layered.Compound
