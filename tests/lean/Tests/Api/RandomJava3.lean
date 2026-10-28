import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
Regression tests for the random-graph Java parity round of agent RJ3 (mrtree, radial, layered P4).
Every fixture under `tests/fixtures/rj3/` is laid out with `Elk.Api.layoutJson` and compared at
tolerance `0` with the layout of unmodified ELK Java 0.12.0 in a fresh JVM (`<name>.java.json`,
`ElkJavaBaseline`), or must fail with Java's exception text (`<name>.java.error`). All of them
differed from Java before their fix. Inputs come from `scripts/run_random_java_parity.sh` (sets
`v`/`o`, seeds 1–10) and P3J's crossing minimisation variants (`gen_p3_graphs.py`):

* `mrtree_parallel_edges` (`v6/g0266`): `TreeUtil.getAllOutgoingEdges`/`getAllIncomingEdges` keep
  one of several edges with the same `toString()` (parallel edges), so the second edge is routed by
  the middle-to-middle fallback.
* `mrtree_children_cache` (`v7/g0238`): `getChildren()` are the targets of the outgoing edges after
  the treeification removed a parallel edge (elk-rs' child cache lost the first copy instead).
* `mrtree_compaction_down`, `mrtree_compaction_right` (`o1/g0503`, `o4/g0006`):
  `CompactionProcessor` — `TreeSet` sweep, Java's parent test, the node keeps a position inside a
  level, the node list sorted in place.
* `mrtree_bfs_walker` (`o4/g0388`): a `BFS` treeification keeps parallel edges and second parents;
  Java's `NodePlacer` walks the children lists with their duplicates.
* `mrtree_walker_stack_overflow` (`o1/g0180`): a node listed twice in a row becomes its own right
  sibling; Java's `secondWalk` overflows the stack (`java.lang.StackOverflowError`).
* `mrtree_fan_substring` (`o4/g0123`): `FanProcessor` identifiers of different lengths on one level
  (`StringIndexOutOfBoundsException` from `substring`).
* `mrtree_round_half_up` (`v6/g0278`): `(int) Math.round` rounds negative halves up.
* `radial_rotation_trig`, `radial_sorter_atan2` (`o1/g0438`, `o2/g0306`): the reference JVM's
  `Math.sin`/`Math.cos` (HotSpot aarch64 stubs) and fdlibm `Math.atan2`/`Math.acos`.
* `linear_segments_dependencies` (`v3/g0156`): `LinearSegmentsNodePlacer` — the split segment leaves
  the predecessor's dependency list once, incoming counts are decremented unconditionally.
* `ns_placer_crossings` (P3 variant `v10_g0319`): `NetworkSimplexPlacer.markCrossingEdges` scans the
  ports' own incoming edges with Java's `ListIterator` (the open edge at index 0 is never closed).
-/
namespace Tests.Api.RandomJava3

open Tests Elk.Api Elk.Core.Util

private def fixtureDir : System.FilePath := "tests/fixtures/rj3"

/-- The fixtures laid out and compared with `<name>.java.json`. -/
def fixtures : Array String := #[
  "mrtree_parallel_edges", "mrtree_children_cache", "mrtree_compaction_down", "mrtree_compaction_right",
  "mrtree_bfs_walker", "mrtree_round_half_up", "radial_rotation_trig", "radial_sorter_atan2",
  "linear_segments_dependencies", "ns_placer_crossings"]

/-- The fixtures whose layout fails with Java's exception (`<name>.java.error`). -/
def errorFixtures : Array String := #["mrtree_walker_stack_overflow", "mrtree_fan_substring"]

def layouts : Suite := suite "rj3.java" do
  for name in fixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
    | .ok out =>
      let expected ← IO.FS.readFile (fixtureDir / s!"{name}.java.json")
      checkJson s!"{name}: ELK Java layout (tol 0)" out expected
    | .error e => report s!"{name}: layout expected" false e

def errors : Suite := suite "rj3.java.errors" do
  for name in errorFixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    let expected := (← IO.FS.readFile (fixtureDir / s!"{name}.java.error")).trimAscii.toString
    match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
    | .ok _ => report s!"{name}: Java's exception expected" false "layout succeeded"
    | .error e => checkEq s!"{name}: ELK Java's exception text" e expected

def suites : Array Suite := #[layouts, errors]

end Tests.Api.RandomJava3
