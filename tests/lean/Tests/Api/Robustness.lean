import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
Regression tests for the random-graph robustness classification (`docs/robustness-random-graphs.md`,
fixtures `tests/fixtures/robustness/`). Every input is laid out with `Elk.Api.layoutJson`; the
expected exceptions are ELK Java 0.12.0's (class and text). The JSON API wraps `java.lang.*`
exceptions as `UnsupportedConfigurationException` (elk-rs `catch_layout`), so those are compared
after that prefix.

* `robustness.hang`: the NORTH/SOUTH label stacking loop of the ELK node micro layout path
  terminated (elk-rs loops forever on it; ELK Java lays it out). The output is pinned.
* `robustness.exceptions`: Java's exception class and message where Lean used to report another
  class (`radial_not_a_tree`), another text (`layer_sweep_in_child`) or nothing
  (`fixed_edge_without_section`).
* `robustness.lenient`: inputs ELK Java rejects and elk-lean (like elk-rs) lays out; pinned so that a
  change of that behaviour is noticed (`java_crossing_counter_aioobe`: a Java defect;
  `port_without_side`: Java's node size calculator validation, not ported).

`radial_cycle_overflow.json` (Java `StackOverflowError`, elk-rs and elk-lean overflow the stack the
same way) aborts the process and is therefore not run here.
-/
namespace Tests.Api.Robustness

open Tests Elk.Api

private def fixtureDir : System.FilePath := "tests/fixtures/robustness"

private def apiWrapper : String := "org.eclipse.elk.core.UnsupportedConfigurationException: "

/-- The error of a layout with the API wrapper in front of `java.*` classes removed. -/
private def javaError (e : String) : String :=
  if e.startsWith (apiWrapper ++ "java.") then (e.drop apiWrapper.length).toString else e

private def layoutFixture (name : String) : IO (Except String String) := do
  let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
  layoutJson input "{}" (pretty := true) (sortKeys := true)

def hang : Suite := suite "robustness.hang" do
  match ← layoutFixture "label_stack_hang" with
  | .ok out =>
    let expected ← IO.FS.readFile (fixtureDir / "label_stack_hang.expected.json")
    checkJson "label_stack_hang terminates with the pinned layout" out expected
  | .error e => report "label_stack_hang: layout expected" false e

/-- `(fixture, ELK Java 0.12.0 exception)`. -/
private def expectedExceptions : Array (String × String) := #[
  ("radial_not_a_tree", "java.lang.IllegalArgumentException: The given graph is not a tree!"),
  ("layer_sweep_in_child",
    "org.eclipse.elk.core.UnsupportedGraphException: The hierarchy aware processor LAYER_SWEEP in child node " ++
    "G-unlayered[n_x, n_root.n0.b] is only allowed if the root node specifies the same hierarchical processor."),
  ("fixed_edge_without_section",
    "java.lang.IllegalArgumentException: The edge needs to have exactly one edge section. Found: 0")]

def exceptions : Suite := suite "robustness.exceptions" do
  for (name, expected) in expectedExceptions do
    match ← layoutFixture name with
    | .ok _ => report s!"{name}: exception expected" false
    | .error e => checkEq s!"{name}: Java exception" (javaError e) expected

def lenient : Suite := suite "robustness.lenient" do
  for name in #["java_crossing_counter_aioobe", "port_without_side"] do
    match ← layoutFixture name with
    | .ok _ => check s!"{name}: laid out (ELK Java throws)" true
    | .error e => report s!"{name}: layout expected" false e

def suites : Array Suite := #[hang, exceptions, lenient]

end Tests.Api.Robustness
