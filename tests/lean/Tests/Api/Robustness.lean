import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
Regression tests for the random-graph robustness classification (`docs/robustness-random-graphs.md`,
fixtures `tests/fixtures/robustness/`). Every input is laid out with `Elk.Api.layoutJson`; the
expected exceptions are ELK Java 0.12.0's (class and text). The JSON API wraps `java.lang.*`
exceptions as `UnsupportedConfigurationException` (elk-rs `catch_layout`), so those are compared
after that prefix.

* `robustness.hang`: the NORTH/SOUTH label stacking loop of elk-rs' simplified ELK path
  (`NodeDimensionCalculation.calculateLabelAndNodeSizesForElk`, elk-rs loops forever on it)
  terminates with the pinned label positions; the node micro layout itself now runs Java's full
  cell system, whose result equals ELK Java (`label_stack_hang.java.json`, node positions aside:
  force's padding default is not part of the node micro layout).
* `robustness.exceptions`: Java's exception class and message where Lean used to report another
  class (`radial_not_a_tree`), another text (`layer_sweep_in_child`) or nothing
  (`fixed_edge_without_section`; `port_without_side`: Java's node size calculator validation,
  elk-rs lays it out).
* `robustness.lenient`: inputs ELK Java rejects and elk-lean (like elk-rs) lays out; pinned so that a
  change of that behaviour is noticed (`java_crossing_counter_aioobe`: a Java defect).

`radial_cycle_overflow.json` (Java `StackOverflowError`, elk-rs and elk-lean overflow the stack the
same way) aborts the process and is therefore not run here.
-/
namespace Tests.Api.Robustness

open Tests Elk Elk.Graph Elk.Api Elk.Json Elk.Core.Util.Adapters Elk.Alg.Common.NodeSpacing

private def fixtureDir : System.FilePath := "tests/fixtures/robustness"

private def apiWrapper : String := "org.eclipse.elk.core.UnsupportedConfigurationException: "

/-- The error of a layout with the API wrapper in front of `java.*` classes removed. -/
private def javaError (e : String) : String :=
  if e.startsWith (apiWrapper ++ "java.") then (e.drop apiWrapper.length).toString else e

private def layoutFixture (name : String) : IO (Except String String) := do
  let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
  layoutJson input "{}" (pretty := true) (sortKeys := true)

/-- Imports a fixture into a fresh arena (the JSON importer of `Elk.Api.layoutValue`). -/
private def importFixture (name : String) : IO (NodeId × ElkGraph) := do
  let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
  let .ok v := Elk.Json.parse input | throw (IO.userError s!"{name}: not JSON")
  ensureInitialized
  let defaults ← match ← GlobalOptions.parse "{}" with
    | .ok g => pure g
    | .error e => throw (IO.userError e)
  let ((root, _), g) ← (ImportM.run (JsonImporter.transform v) { defaults := some defaults }).run {}
  return (root, g)

def hang : Suite := suite "robustness.hang" do
  -- elk-rs' ELK path (no longer used by `NodeMicroLayout`) terminates: pinned label positions
  let (root, g) ← importFixture "label_stack_hang"
  let (((size, labelYs)), _) ← (do
      NodeDimensionCalculation.calculateLabelAndNodeSizesForElk (← ElkGraphAdapters.adapt root) root
      let g ← get
      let node := (g.node root).children[0]!
      let port := (g.node node).ports[0]!
      return ((((g.node node).width, (g.node node).height)), (g.port port).labels.map fun l => (g.label l).y) :
        ElkM ((Float × Float) × Array Float)).run g
  check "label_stack_hang: elk-rs ELK path terminates (node 62 x 0)" (size == (62.0, 0.0))
  check "label_stack_hang: elk-rs ELK path label positions (-25.4, -15.8)" (labelYs == #[-25.4, -15.8])
  -- the node micro layout (Java's cell system) equals ELK Java
  match ← layoutFixture "label_stack_hang" with
  | .ok out =>
    let expected ← IO.FS.readFile (fixtureDir / "label_stack_hang.java.json")
    match Elk.Json.parse out, Elk.Json.parse expected (lenient := true) with
    | .ok a, .ok e =>
      let d := jsonDiff "" (layoutSizingView a) (layoutSizingView e) 0.0
      report "label_stack_hang: node micro layout equals ELK Java" d.isNone (d.getD "")
    | _, _ => report "label_stack_hang: JSON output" false
  | .error e => report "label_stack_hang: layout expected" false e

/-- `(fixture, ELK Java 0.12.0 exception)`. -/
private def expectedExceptions : Array (String × String) := #[
  ("radial_not_a_tree", "java.lang.IllegalArgumentException: The given graph is not a tree!"),
  ("layer_sweep_in_child",
    "org.eclipse.elk.core.UnsupportedGraphException: The hierarchy aware processor LAYER_SWEEP in child node " ++
    "G-unlayered[n_x, n_root.n0.b] is only allowed if the root node specifies the same hierarchical processor."),
  ("fixed_edge_without_section",
    "java.lang.IllegalArgumentException: The edge needs to have exactly one edge section. Found: 0"),
  ("port_without_side",
    "java.lang.IllegalArgumentException: Label and node size calculator can only be used with ports that have port sides assigned.")]

def exceptions : Suite := suite "robustness.exceptions" do
  for (name, expected) in expectedExceptions do
    match ← layoutFixture name with
    | .ok _ => report s!"{name}: exception expected" false
    | .error e => checkEq s!"{name}: Java exception" (javaError e) expected

def lenient : Suite := suite "robustness.lenient" do
  for name in #["java_crossing_counter_aioobe"] do
    match ← layoutFixture name with
    | .ok _ => check s!"{name}: laid out (ELK Java throws)" true
    | .error e => report s!"{name}: layout expected" false e

def suites : Array Suite := #[hang, exceptions, lenient]

end Tests.Api.Robustness
