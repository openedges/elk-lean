import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
Regression tests for the random-graph robustness classification (`docs/robustness-random-graphs.md`,
fixtures `tests/fixtures/robustness/`). Every input is laid out with `Elk.Api.layoutJson`; the
expected exceptions are ELK Java 0.12.0's `Throwable.toString()` (class and text), which the JSON
API reports unchanged (`Elk.Api.catchLayout` no longer wraps `java.lang.*` or other fully qualified
exception classes as `UnsupportedConfigurationException`).

* `robustness.hang`: the NORTH/SOUTH label stacking loop of elk-rs' simplified ELK path
  (`NodeDimensionCalculation.calculateLabelAndNodeSizesForElk`, elk-rs loops forever on it)
  terminates with the pinned label positions; the node micro layout itself now runs Java's full
  cell system, whose result equals ELK Java (`label_stack_hang.java.json`, node positions aside:
  force's padding default is not part of the node micro layout).
* `robustness.exceptions`: Java's exception class and message where Lean used to report another
  class (`radial_not_a_tree`, `json_unknown_target`), another text (`layer_sweep_in_child`, the
  `layer_constraint_*` node designations of `LayerConstraintPre/Postprocessor`) or nothing
  (`fixed_edge_without_section`; `port_without_side`: Java's node size calculator validation,
  elk-rs lays it out).
* `java_crossing_counter_aioobe` (in `robustness.exceptions` since LM): Java's crossing counter reads a
  stale far-end position beyond its index tree; elk-lean now checks Java's tree bounds and throws the same
  `ArrayIndexOutOfBoundsException` (elk-rs lays it out). `robustness.lenient` pins nothing at the moment.

`radial_cycle_overflow.json` (Java `StackOverflowError`, elk-rs and elk-lean overflow the stack the
same way) aborts the process and is therefore not run here.
-/
namespace Tests.Api.Robustness

open Tests Elk Elk.Graph Elk.Api Elk.Json Elk.Core.Util.Adapters Elk.Alg.Common.NodeSpacing

private def fixtureDir : System.FilePath := "tests/fixtures/robustness"

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
  ("java_crossing_counter_aioobe", "java.lang.ArrayIndexOutOfBoundsException: Index 5 out of bounds for length 2"),
  ("radial_not_a_tree", "java.lang.IllegalArgumentException: The given graph is not a tree!"),
  ("layer_sweep_in_child",
    "org.eclipse.elk.core.UnsupportedGraphException: The hierarchy aware processor LAYER_SWEEP in child node " ++
    "G-unlayered[n_x, n_root.n0.b] is only allowed if the root node specifies the same hierarchical processor."),
  ("fixed_edge_without_section",
    "java.lang.IllegalArgumentException: The edge needs to have exactly one edge section. Found: 0"),
  ("layer_constraint_first",
    "org.eclipse.elk.core.UnsupportedConfigurationException: Node 'root.n0.b' has its layer constraint set to FIRST, " ++
    "but has at least one incoming edge that  does not come from a FIRST_SEPARATE node. That must not happen."),
  ("layer_constraint_first_labelled",
    "org.eclipse.elk.core.UnsupportedConfigurationException: Node 'A label' has its layer constraint set to FIRST, " ++
    "but has at least one incoming edge that  does not come from a FIRST_SEPARATE node. That must not happen."),
  ("layer_constraint_last",
    "org.eclipse.elk.core.UnsupportedConfigurationException: Node 'root.n0.b' has its layer constraint set to LAST, " ++
    "but has at least one outgoing edge that  does not go to a LAST_SEPARATE node. That must not happen."),
  ("layer_constraint_first_separate",
    "org.eclipse.elk.core.UnsupportedConfigurationException: Node 'root.n0.a' has its layer constraint set to " ++
    "FIRST_SEPARATE, but has at least one incoming edge. FIRST_SEPARATE nodes must not have incoming edges."),
  ("layer_constraint_last_separate",
    "org.eclipse.elk.core.UnsupportedConfigurationException: Node 'root.n0.a' has its layer constraint set to " ++
    "LAST_SEPARATE, but has at least one outgoing edge. LAST_SEPARATE nodes must not have outgoing edges."),
  ("json_unknown_target", "org.eclipse.elk.graph.json.JsonImportException: Referenced shape does not exist: x"),
  ("port_without_side",
    "java.lang.IllegalArgumentException: Label and node size calculator can only be used with ports that have port sides assigned.")]

def exceptions : Suite := suite "robustness.exceptions" do
  for (name, expected) in expectedExceptions do
    match ← layoutFixture name with
    | .ok _ => report s!"{name}: exception expected" false
    | .error e => checkEq s!"{name}: Java exception" e expected

def lenient : Suite := suite "robustness.lenient" do
  for name in (#[] : Array String) do
    match ← layoutFixture name with
    | .ok _ => check s!"{name}: laid out (ELK Java throws)" true
    | .error e => report s!"{name}: layout expected" false e

/-- `catchLayout`: errors in `Throwable.toString()` form pass unchanged, other texts are wrapped as
`UnsupportedConfigurationException` (elk-rs `catch_layout`). -/
def errorText : Suite := suite "robustness.errorText" do
  let wrapper := "org.eclipse.elk.core.UnsupportedConfigurationException: "
  let cases : Array (String × String) := #[
    ("java.lang.IllegalStateException: x", "java.lang.IllegalStateException: x"),
    ("java.lang.NullPointerException", "java.lang.NullPointerException"),
    ("java.lang.StackOverflowError", "java.lang.StackOverflowError"),
    ("org.eclipse.elk.alg.layered.options.UnspecifiedSpacingException: s",
      "org.eclipse.elk.alg.layered.options.UnspecifiedSpacingException: s"),
    ("org.eclipse.elk.core.UnsupportedGraphException: g", "org.eclipse.elk.core.UnsupportedGraphException: g"),
    ("plain message", wrapper ++ "plain message"),
    ("java.lang.Thing happened: x", wrapper ++ "java.lang.Thing happened: x"),
    ("java.util.Foo: x", wrapper ++ "java.util.Foo: x"),
    ("com.example.SomeException: x", wrapper ++ "com.example.SomeException: x")]
  for (msg, expected) in cases do
    match ← catchLayout (α := Unit) (throw (IO.userError msg)) with
    | .error e => checkEq s!"catchLayout {msg}" e expected
    | .ok _ => report s!"catchLayout {msg}: error expected" false

def suites : Array Suite := #[hang, exceptions, lenient, errorText]

end Tests.Api.Robustness
