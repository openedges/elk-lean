import Tests.Framework
import Tests.JsonCompare
import Elk.Api
import Elk.Core.Util.JavaHashSet
/-!
Regression tests for agent SPV (SPOrE, VertiFlex, rectpacking option sets and three deterministic layered
cases of the random-graph Java parity). Every layout fixture under `tests/fixtures/spv/` is laid out with
`Elk.Api.layoutJson` and compared at tolerance `0` with the layout of unmodified ELK Java 0.12.0 in a fresh
JVM (`<name>.java.json`, `ElkJavaBaseline`), or must fail with Java's exception text (`<name>.java.error`).
All of them differed from Java before their fix. Inputs come from `scripts/run_random_java_parity.sh`
(sets `v`/`o`/`p`, seeds 1–10) and P3J's variant set `p3a`:

* `spore_*` (`o9/g0005`, `o2/g0451`, `o2/g0392`, `o4/g0205`, `o6/g0429`, `o5/g0132`): the iteration
  order of Java's `HashSet<TTriangle>`/`HashSet<TEdge>` (value hash codes; `Elk.Core.Util.JavaHashSet`)
  in `BowyerWatsonTriangulation`, the scanline overlap edges and `NaiveMinST` (ties of equal costs).
* `vertiflex_split_group` (`o1/g0513`): `RelativeXPlacer.splitGroup` never increments its index, so a
  group of equal-height children goes to the right (`-1` result).
* `vertiflex_node_model_order_option` (`o7/g0218`): the root move reads `CONSIDER_NODE_MODEL_ORDER` from
  the tree node, not from the layout graph.
* `vertiflex_port_edges_ignored`, `vertiflex_port_target_cast`: the tree walks use the node's own edges
  (`getOutgoingEdges()`); a port target is Java's `ClassCastException`.
* `rectpacking_recompact_same_row` (`v10/g0460`): `RowFillingAndCompaction` compacts the same row again.
* `rectpacking_stale_parent_row` (`v8/g0580`): Java's strong parent-row references (a block of a removed
  next row is added to the row twice), `RectRow.removeBlock` of the first occurrence, `Double.MIN_VALUE`.
* `ns_placer_stale_side_view` (`p2/v2_g0421`): `LNode.getPortSideView` returns the cached index range even
  after ports were added (`NetworkSimplexPlacer.markCrossingEdges` misses edges like Java).
* `sort_by_input_model_ports` (`p5/v5_g0464`): `ModelOrderPortComparator`'s previous-layer check decides
  on the first source node found; its fourth transitivity check never decides.
* `orthogonal_insert_sorted_float` (P3 variant `v5_g0360`): `HyperEdgeSegment.insertSorted` compares the
  `float` value of the coordinates (duplicate coordinates count in the dependency weights).

`spv.javaHashSet` replays a recorded operation sequence (`scripts/gen_hashset_ops.py`, seed 1: adds,
removals, iterator removals, `removeAll`, `clear`, many keys in one bin, up to six tree bins that grow,
shrink and split on resize) on `JavaHashSet` and compares every iteration order with the one
`java.util.HashSet` printed (`scripts/java/HashSetOrder.java`; `hashset_ops.txt`, `hashset_ops.java.txt`).
-/
namespace Tests.Api.RandomJavaSpv

open Tests Elk.Api Elk.Core.Util

private def fixtureDir : System.FilePath := "tests/fixtures/spv"

/-- The fixtures laid out and compared with `<name>.java.json`. -/
def fixtures : Array String := #[
  "spore_overlap_hash_order", "spore_overlap_orthogonal", "spore_overlap_circle_underlap",
  "spore_overlap_rectangle_underlap", "spore_overlap_small_shifts", "spore_compaction_hash_order",
  "vertiflex_split_group", "vertiflex_node_model_order_option", "vertiflex_port_edges_ignored",
  "rectpacking_recompact_same_row", "rectpacking_stale_parent_row", "ns_placer_stale_side_view",
  "sort_by_input_model_ports", "orthogonal_insert_sorted_float"]

/-- The fixtures whose layout fails with Java's exception (`<name>.java.error`). -/
def errorFixtures : Array String := #["vertiflex_port_target_cast"]

def layouts : Suite := suite "spv.java" do
  for name in fixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
    | .ok out =>
      let expected ← IO.FS.readFile (fixtureDir / s!"{name}.java.json")
      checkJson s!"{name}: ELK Java layout (tol 0)" out expected
    | .error e => report s!"{name}: layout expected" false e

def errors : Suite := suite "spv.java.errors" do
  for name in errorFixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    let expected := (← IO.FS.readFile (fixtureDir / s!"{name}.java.error")).trimAscii.toString
    match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
    | .ok _ => report s!"{name}: Java's exception expected" false "layout succeeded"
    | .error e => checkEq s!"{name}: ELK Java's exception text" e expected

/-- A key with a chosen Java hash code and identity by id (the test class of `HashSetOrder.java`). -/
private structure Key where
  id : Nat
  h : UInt32
  deriving Inhabited

private instance : BEq Key := ⟨fun a b => a.id == b.id⟩
private instance : JavaHashCode Key := ⟨fun k => k.h, fun a b => a.id == b.id⟩

private def parseInt (s : String) : Int :=
  if s.startsWith "-" then -((s.drop 1).toString.toNat!) else s.toNat!

private def toU32 (i : Int) : UInt32 := (if i < 0 then i + 4294967296 else i).toNat.toUInt32

def javaHashSet : Suite := suite "spv.javaHashSet" do
  let ops ← IO.FS.lines (fixtureDir / "hashset_ops.txt")
  let expected ← IO.FS.lines (fixtureDir / "hashset_ops.java.txt")
  let mut set : JavaHashSet Key := {}
  let mut out : Array String := #[]
  let mut maxTrees := 0
  for line in ops do
    let p := (line.trimAscii.toString.splitOn " ").toArray
    match p[0]! with
    | "a" => set := (set.add ⟨p[1]!.toNat!, toU32 (parseInt p[2]!)⟩).1
    | "r" => set := (set.remove ⟨p[1]!.toNat!, toU32 (parseInt p[2]!)⟩).1
    | "i" => let id := p[1]!.toNat!; set := set.removeIf (·.id == id)
    | "R" =>
      let mut c : Array Key := #[]
      let mut i := 1
      while i + 1 < p.size do
        c := c.push ⟨p[i]!.toNat!, toU32 (parseInt p[i+1]!)⟩
        i := i + 2
      set := set.removeAll c
    | "c" => set := set.clear
    | "p" => out := out.push (" ".intercalate (set.toArray.map (toString ·.id)).toList)
    | _ => pure ()
    let trees := set.table.foldl (fun n b => match b with | .tree .. => n + 1 | .chain _ => n) 0
    maxTrees := max maxTrees trees
  checkEq "iteration orders recorded" out.size expected.size
  let mut firstDiff : Option Nat := none
  for i in [0:min out.size expected.size] do
    if firstDiff.isNone && out[i]! != expected[i]! then firstDiff := some i
  checkEq "every iteration order equals java.util.HashSet's" firstDiff none
  check "the sequence reaches tree bins (at least 9 keys in one bin, table of 64 bins)" (maxTrees > 0)

def suites : Array Suite := #[layouts, errors, javaHashSet]

end Tests.Api.RandomJavaSpv
