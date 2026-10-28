import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
ELK Java 0.12.0 expectations of the node micro layout path (`NodeMicroLayout`: Java's port sort,
the full `NodeLabelAndSizeCalculator.process` cell system pipeline and the node margins) and of
Java's node size validation, on the fixtures in `tests/fixtures/nodemicro/` (inputs `<name>.json`,
ELK Java outputs `<name>.java.json` from `ElkJavaBaseline`). Every input is laid out with
`Elk.Api.layoutJson`.

* `nodemicro.java.layout`: the whole layout equals Java's (values exactly, tolerance `0`): stress,
  rectpacking, a rectpacking child graph (`MinSizePreProcessor` sizes the graph node by its labels
  and ports), box and fixed (their padding default `15`).
* `nodemicro.java.sizing`: the node micro layout result equals Java's — node sizes, port positions
  and sizes, port and node label positions (all relative to their node) — for algorithms whose
  node placement still differs from Java (force, mrtree, radial: not part of the node micro
  layout); node positions and edges are not compared.
* `nodemicro.java.exceptions`: Java's exception class and message for every node size validation:
  `UnsupportedConfigurationException: Invalid port/node label placement: [..]` (`NodeContext`, also
  for the layered graph node through `computeInsideNodeLabelPadding`),
  `IllegalArgumentException: Label and node size calculator can only be used with ports that have
  port sides assigned.` (`PortContextCreator`, also from rectpacking's `MinSizePreProcessor`) and
  `IllegalStateException: Port side is undefined` (`ElkGraphAdapters.PortComparator` during Java's
  `TimSort` of a `FIXED_ORDER` node; with distinct `PORT_INDEX`es the comparator never reaches the
  side check and the port contexts throw instead). The JSON API wraps `java.lang.*` exceptions as
  `UnsupportedConfigurationException`, so those are compared after that prefix.
-/
namespace Tests.Api.NodeMicroLayout

open Tests Elk.Api Elk.Json

private def fixtureDir : System.FilePath := "tests/fixtures/nodemicro"

private def apiWrapper : String := "org.eclipse.elk.core.UnsupportedConfigurationException: "

/-- The error of a layout with the API wrapper in front of `java.*` classes removed. -/
private def javaError (e : String) : String :=
  if e.startsWith (apiWrapper ++ "java.") then (e.drop apiWrapper.length).toString else e

private def layoutFixture (name : String) : IO (Except String String) := do
  let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
  layoutJson input "{}" (pretty := true) (sortKeys := true)

private def checkAgainstJava (name : String) (view : Value → Value) : TestM Unit := do
  match ← layoutFixture name with
  | .error e => report s!"{name}: layout expected" false e
  | .ok out =>
    let expected ← IO.FS.readFile (fixtureDir / s!"{name}.java.json")
    match Elk.Json.parse out, Elk.Json.parse expected (lenient := true) with
    | .ok a, .ok e =>
      let d := jsonDiff "" (view a) (view e) 0.0
      report s!"{name}: equals ELK Java" d.isNone (d.getD "")
    | .error err, _ => report s!"{name}: output is JSON" false s!"{err}"
    | _, .error err => report s!"{name}: Java output is JSON" false s!"{err}"

def layout : Suite := suite "nodemicro.java.layout" do
  for name in #["stress", "rectpacking", "rectpacking_child", "box", "fixed"] do
    checkAgainstJava name id

def sizing : Suite := suite "nodemicro.java.sizing" do
  for name in #["force", "mrtree", "radial"] do
    checkAgainstJava name layoutSizingView

/-- `(fixture, ELK Java 0.12.0 exception)`. -/
private def expectedExceptions : Array (String × String) := #[
  ("invalid_port_label_placement",
    "org.eclipse.elk.core.UnsupportedConfigurationException: Invalid port label placement: [INSIDE, ALWAYS_SAME_SIDE, SPACE_EFFICIENT]"),
  ("invalid_node_label_placement",
    "org.eclipse.elk.core.UnsupportedConfigurationException: Invalid node label placement: [H_LEFT, H_RIGHT, V_TOP, INSIDE]"),
  ("layered_graph_invalid_placement",
    "org.eclipse.elk.core.UnsupportedConfigurationException: Invalid port label placement: [OUTSIDE, ALWAYS_OTHER_SAME_SIDE, SPACE_EFFICIENT]"),
  ("port_without_side",
    "java.lang.IllegalArgumentException: Label and node size calculator can only be used with ports that have port sides assigned."),
  ("port_without_side_indexed",
    "java.lang.IllegalArgumentException: Label and node size calculator can only be used with ports that have port sides assigned."),
  ("rectpacking_child_port_without_side",
    "java.lang.IllegalArgumentException: Label and node size calculator can only be used with ports that have port sides assigned."),
  ("port_side_undefined", "java.lang.IllegalStateException: Port side is undefined")]

def exceptions : Suite := suite "nodemicro.java.exceptions" do
  for (name, expected) in expectedExceptions do
    match ← layoutFixture name with
    | .ok _ => report s!"{name}: exception expected" false
    | .error e => checkEq s!"{name}: Java exception" (javaError e) expected

def suites : Array Suite := #[layout, sizing, exceptions]

end Tests.Api.NodeMicroLayout
