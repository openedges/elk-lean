import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
Edge sections against ELK Java 0.12.0 (random-graph parity class `SEC`,
`docs/robustness-random-graphs.md` §8; fixtures `tests/fixtures/sections/`).

ELK Java writes an edge's `sections` only for the `ElkEdgeSection`s the edge has after layout:
the ones of the input (kept unchanged unless an algorithm routes the edge) and the ones a layout
algorithm creates for the edges it routes. elk-rs (and elk-lean before this suite) added a
straight "fallback" section in the layered `ElkGraphLayoutTransferrer` to every section-less edge
of the layered container and of all its descendants, so the edges of children laid out earlier by
box, fixed, rectpacking (none routed), radial (only node-to-node tree edges), force/stress (only
edges between child nodes) or mrtree (no hierarchical edges or self loops) got a section ELK Java
does not write.

`<name>.java.json` is the output of the pipeline's ELK Java harness (`ElkJavaBaseline`) for the
input `<name>.json`; the suite checks, per edge, that elk-lean writes `sections` exactly where Java
does, with the same content (tolerance 0), and the whole document where it is equal to Java's.

* `<alg>_in_layered`: a layered root with one compound child laid out by `<alg>` (node-to-node,
  port-to-node, hierarchical edge to the child's own port, self loop, edges with `elk.bendPoints`
  or an input section).
* `two_sections_<alg>`: one edge with two input sections. The routing algorithms keep the *first*
  one (Java `ElkGraphUtil.firstEdgeSection(edge, true, true)` in force/stress, mrtree, radial,
  vertiflex, spore and layered; elk-rs kept the last one in force/stress/vertiflex/spore and both in
  mrtree), box and rectpacking keep both, and fixed (with `elk.bendPoints`) and random throw
  `java.lang.IllegalStateException` (their "throw away all except for the last one" loop calls
  `ListIterator.remove()` before `next()`).
-/
namespace Tests.Api.Sections

open Tests Elk.Api Elk.Json

private def fixtureDir : System.FilePath := "tests/fixtures/sections"

/-- `(fixture, whole document equal to ELK Java)`: force and mrtree still differ in the node
positions (their algorithm-specific option defaults, `DEF`), so only the presence of their edge
sections, their ids and their `incomingShape`/`outgoingShape` are compared. -/
private def fixtures : Array (String × Bool) := #[
  ("box_in_layered", true), ("fixed_in_layered", true), ("rectpacking_in_layered", true),
  ("radial_in_layered", true), ("stress_in_layered", true), ("layered_in_layered", true),
  ("force_in_layered", false), ("mrtree_in_layered", false),
  ("two_sections_box", true), ("two_sections_rectpacking", true), ("two_sections_layered", true),
  ("two_sections_radial", true), ("two_sections_stress", true), ("two_sections_vertiflex", true),
  ("two_sections_force", false), ("two_sections_mrtree", false)]

/-- `(fixture, ELK Java 0.12.0 exception)`. -/
private def exceptions : Array (String × String) := #[
  ("two_sections_fixed", "java.lang.IllegalStateException"),
  ("two_sections_random", "java.lang.IllegalStateException")]

private def field? (v : Value) (k : String) : Option Value :=
  match v with
  | .obj kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

/-- `(id, incomingShape, outgoingShape)` of each section of a `sections` array. -/
private def sectionKeys (v : Value) : Array (String × String × String) :=
  let str (o : Value) (k : String) := match field? o k with | some (.str s) => s | _ => "-"
  match v with
  | .arr xs => xs.map fun x => (str x "id", str x "incomingShape", str x "outgoingShape")
  | _ => #[]

/-- `(edge id, sections)` of every edge of the graph, depth first. -/
private partial def edgeSections (n : Value) (acc : Array (String × Option Value)) : Array (String × Option Value) :=
  Id.run do
    let mut acc := acc
    if let some (.arr es) := field? n "edges" then
      for e in es do
        let id := match field? e "id" with | some (.str s) => s | _ => "?"
        acc := acc.push (id, field? e "sections")
    if let some (.arr cs) := field? n "children" then
      for c in cs do acc := edgeSections c acc
    return acc

def sections : Suite := suite "sections.java" do
  for (name, whole) in fixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    let expected ← IO.FS.readFile (fixtureDir / s!"{name}.java.json")
    match ← layoutJson input "{}" (pretty := true) (sortKeys := true) with
    | .error e => report s!"{name}: layout expected" false e
    | .ok out =>
      match Elk.Json.parse out, Elk.Json.parse expected (lenient := true) with
      | .ok a, .ok j =>
        let le := edgeSections a #[]
        let je := edgeSections j #[]
        checkEq s!"{name}: edge ids" (le.map (·.1)) (je.map (·.1))
        for ((id, ls), (_, js)) in le.zip je do
          checkEq s!"{name}: {id} has sections like Java" ls.isSome js.isSome
          if let (some lv, some jv) := (ls, js) then
            if whole then
              let d := jsonDiff s!"{id}/sections" lv jv 0.0
              report s!"{name}: {id} sections equal to Java" d.isNone (d.getD "")
            else
              checkEq s!"{name}: {id} section ids and shapes like Java" (sectionKeys lv) (sectionKeys jv)
        if whole then checkJson s!"{name}: layout equal to ELK Java" out expected
      | _, _ => report s!"{name}: JSON expected" false
  for (name, expected) in exceptions do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    match ← layoutJson input "{}" (pretty := true) (sortKeys := true) with
    | .error e => checkEq s!"{name}: ELK Java exception" e expected
    | .ok _ => report s!"{name}: exception expected" false

def suites : Array Suite := #[sections]

end Tests.Api.Sections
