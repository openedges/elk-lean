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
* `vertiflex_constraint_before_cast`: the vertical constraint check casts edge by edge, so a child that
  violates its constraint is reported before a later edge's `ClassCastException`.
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
def errorFixtures : Array String := #["vertiflex_port_target_cast", "vertiflex_constraint_before_cast"]

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

/-- `Math.asin` of the reference JVM (Temurin 21.0.13, aarch64; `scripts/java/AsinDump.java`, seed 42):
argument and result bits — the branch boundaries (`|x| = 1`, `0.5`, `0.975`, `2^-27`), NaN arguments
and random arguments of every branch. -/
private def javaAsinSamples : Array (UInt64 × UInt64) := #[
  (0x3FF0000000000000, 0x3FF921FB54442D18),
  (0xBFF0000000000000, 0xBFF921FB54442D18),
  (0x0000000000000000, 0x0000000000000000),
  (0x8000000000000000, 0x8000000000000000),
  (0x3FE0000000000000, 0x3FE0C152382D7366),
  (0xBFE0000000000000, 0xBFE0C152382D7366),
  (0x3FDFFFFFFFFFFFFF, 0x3FE0C152382D7365),
  (0x3FEF333333333333, 0x3FF58C2B5CE0C3E5),
  (0xBFEF333333333333, 0xBFF58C2B5CE0C3E5),
  (0x3FEF333333333332, 0x3FF58C2B5CE0C3E3),
  (0x3FEF33333333338D, 0x3FF58C2B5CE0C4B0),
  (0x3DDB7CDFD9D7BDBB, 0x3DDB7CDFD9D7BDBB),
  (0xBDDB7CDFD9D7BDBB, 0xBDDB7CDFD9D7BDBB),
  (0x01A56E1FC2F8F359, 0x01A56E1FC2F8F359),
  (0x3E30000000000000, 0x3E30000000000000),
  (0x3E40000000000000, 0x3E40000000000000),
  (0x3FD3333333333333, 0x3FD380159E14F6FF),
  (0xBFE6666666666666, 0xBFE8D00E692AFD95),
  (0x3FEFFFFFFAA19C47, 0x3FF9216709C28B31),
  (0xBFEFFFFFFAA19C47, 0xBFF9216709C28B31),
  (0x3FF0000000000001, 0x7FF8000000000000),
  (0xBFF8000000000000, 0x7FF8000000000000),
  (0x4000000000000000, 0x7FF8000000000000),
  (0x7FF8000000000000, 0x7FF8000000000000),
  (0x7FF0000000000000, 0x7FF8000000000000),
  (0x0000000000000001, 0x0000000000000001),
  (0x3FDD20CE81BFD15C, 0x3FDE3DB0915C82CC),
  (0x3FC773DDE188B804, 0x3FC795FA20331C0E),
  (0x3FEF561C63818F9D, 0x3FF5DE58FF4F04A5),
  (0xBD61BBA76B52C856, 0xBD61BBA76B52C856),
  (0x3FE9D0D9E738597C, 0x3FEE0930BB7C46AA),
  (0xBFC0CBB8B3C99470, 0xBFC0D82823F6C6F4),
  (0x3FEF4E02022A6B75, 0x3FF5CA949938434D),
  (0x3E6DAC800C318574, 0x3E6DAC800C318578),
  (0x3FEAD644326E6BC6, 0x3FEFD57C0D37BADE),
  (0xBFB04220A3DA51E0, 0xBFB044EE35D6CEF8),
  (0x3FEFC289751A753E, 0x3FF72BEAFB044F56),
  (0xBE28BD82FCC5C830, 0xBE28BD82FCC5C830),
  (0x3FC82750D5A6D650, 0x3FC84C9CAF4F7AC0),
  (0xBFD2932B0BFD4A90, 0xBFD2D897808C280C),
  (0x3FEFD53AB82AEA5E, 0x3FF77F3E8363B72C),
  (0xBDB60B3CC513B2BC, 0xBDB60B3CC513B2BC)]

private def hexBits (s : String) : UInt64 :=
  s.foldl (fun acc c =>
    let d := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
    acc * 16 + d.toUInt64) 0

/-- `javaAsin` (`KVector.toRadians`) against the reference JVM's `Math.asin`, bit for bit; with
`ELK_ASIN_CASES` set to the output of `java AsinDump <n>` also every line of that file. -/
def javaAsin : Suite := suite "spv.javaAsin" do
  for (x, v) in javaAsinSamples do
    if (Float.ofBits v).isNaN then check s!"javaAsin {x} = NaN" (Elk.Core.Util.javaAsin (Float.ofBits x)).isNaN
    else checkEq s!"javaAsin {x}" (Elk.Core.Util.javaAsin (Float.ofBits x)).toBits v
  let some path ← IO.getEnv "ELK_ASIN_CASES"
    | IO.println "SKIP spv.javaAsin (full): ELK_ASIN_CASES not set"
  let mut n := 0
  let mut bad := 0
  for line in ← IO.FS.lines path do
    if let [a, b] := line.splitOn " " then
      n := n + 1
      let got := (Elk.Core.Util.javaAsin (Float.ofBits (hexBits a))).toBits
      let expected := hexBits b
      unless got == expected || ((Float.ofBits got).isNaN && (Float.ofBits expected).isNaN) do
        bad := bad + 1
  check s!"javaAsin equals Math.asin on all {n} arguments of {path}" (n > 0 && bad == 0)

def suites : Array Suite := #[layouts, errors, javaHashSet, javaAsin]

end Tests.Api.RandomJavaSpv
