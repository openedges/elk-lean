import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
ELK Java 0.12.0 expectations of layered node sizes, port positions and label positions (the
random-graph parity class `LNODE`) and of the layered importer's edge selection, on the fixtures in
`tests/fixtures/lnode/` (inputs `<name>.json`, ELK Java outputs `<name>.java.json` from
`ElkJavaBaseline`). Every input is laid out with `Elk.Api.layoutJson` and compared with Java exactly
(tolerance `0`).

* `lnode.java.layout`:
  - `selfloop_port_order`: `SelfLoopPortRestorer` sorts the ports of a one-sided self loop by
    `SelfLoopPort.getSLNetFlow()` (elk-rs: the `LPort` net flow without the hidden self loops);
  - `port_index_partial`: `PortListSorter` sorts a `FIXED_ORDER` node whose ports only partly have
    a `PORT_INDEX` with Java's `TimSort` (the comparator is not a consistent order);
  - `fixed_ratio_ports`: the cell system places `FIXED_RATIO` ports at the ratio stored on the
    `LPort` (`PORT_RATIO_OR_POSITION`; elk-rs places them at `0`);
  - `external_ns_port_margins`: `HierarchicalPortOrthogonalEdgeRouter` computes the margins of the
    restored north/south external port dummies (elk-rs computes none);
  - `min_graph_size_separate`, `min_graph_size_include`: `calculateMinimumGraphSize` lays the label
    cells out for the parent's `DIRECTION` and writes `MINIMUM_SIZE` / the minimum into the
    ElkNode's own option values (Java's `copyProperties` aliasing);
  - `fixed_port_labels_compound`: no elk-rs `processNode` pre-pass for compound nodes with placed
    fixed port labels in `LabelAndNodeSizeProcessor`;
  - `edge_cross_hierarchy_separate`, `edge_cross_hierarchy_layered_child`: Java's flat import only
    transforms edges between children (or a child and the graph); a root edge into a child's
    child is left to no run instead of raising an error;
  - `edge_inside_self_loop_separate`: inside self loops of a separately laid out compound node.
* `lnode.java.exceptions`: Java's exception for a flat edge to a `NO_LAYOUT` sibling (`transformEdge`:
  "The source or the target of edge ElkEdge … could not be found. …", with EMF's `toString` of the
  edge) and for a hyperedge in a flat graph (`ElkGraphUtil.getSourceNode`: "Passed edge is not
  'simple'.").
-/
namespace Tests.Api.LayeredNodeJava

open Tests Elk.Api Elk.Json

private def fixtureDir : System.FilePath := "tests/fixtures/lnode"

private def layoutFixture (name : String) : IO (Except String String) := do
  let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
  layoutJson input "{}" (pretty := true) (sortKeys := true)

private def checkAgainstJava (name : String) : TestM Unit := do
  match ← layoutFixture name with
  | .error e => report s!"{name}: layout expected" false e
  | .ok out =>
    let expected ← IO.FS.readFile (fixtureDir / s!"{name}.java.json")
    match Elk.Json.parse out, Elk.Json.parse expected (lenient := true) with
    | .ok a, .ok e =>
      let d := jsonDiff "" a e 0.0
      report s!"{name}: equals ELK Java" d.isNone (d.getD "")
    | .error err, _ => report s!"{name}: output is JSON" false s!"{err}"
    | _, .error err => report s!"{name}: Java output is JSON" false s!"{err}"

def layout : Suite := suite "lnode.java.layout" do
  for name in #["selfloop_port_order", "port_index_partial", "fixed_ratio_ports", "external_ns_port_margins",
      "min_graph_size_separate", "min_graph_size_include", "fixed_port_labels_compound",
      "edge_cross_hierarchy_separate", "edge_cross_hierarchy_layered_child", "edge_inside_self_loop_separate"] do
    checkAgainstJava name

/-- `(fixture, ELK Java 0.12.0 exception)`. -/
private def expectedExceptions : Array (String × String) := #[
  ("edge_to_no_layout_node",
    "org.eclipse.elk.core.UnsupportedGraphException: The source or the target of edge ElkEdge \"e0\" ElkNode \"x\" (0.0,0.0 | 30.0,30.0) -> ElkNode \"z\" (5.0,7.0 | 30.0,30.0) could not be found. This usually happens when an edge connects a node laid out by ELK Layered to a node in another level of hierarchy laid out by either another instance of ELK Layered or another layout algorithm alltogether. The former can be solved by setting the hierarchyHandling option to INCLUDE_CHILDREN."),
  ("edge_hyperedge_flat", "java.lang.IllegalArgumentException: Passed edge is not 'simple'.")]

def exceptions : Suite := suite "lnode.java.exceptions" do
  for (name, expected) in expectedExceptions do
    match ← layoutFixture name with
    | .ok _ => report s!"{name}: exception expected" false
    | .error e => checkEq s!"{name}: Java exception" (javaExceptionText e) expected

/-- Java `Double.toString` (`Float.toJavaString`), used by the exception texts above. -/
def javaDoubleText : Suite := suite "lnode.java.doubleToString" do
  let cases : Array (Float × String) := #[(0.0, "0.0"), (-0.0, "-0.0"), (30.0, "30.0"), (50.5, "50.5"),
    (0.1, "0.1"), (0.001, "0.001"), (0.0001, "1.0E-4"), (1.5e-7, "1.5E-7"), (1234567.0, "1234567.0"),
    (1.0e7, "1.0E7"), (12345678.9, "1.23456789E7"), (-2.25, "-2.25"), (1.0e21, "1.0E21"),
    (100.0, "100.0"), (0.30000000000000004, "0.30000000000000004")]
  for (x, s) in cases do
    checkEq s!"Double.toString {s}" (Elk.Core.Util.Float.toJavaString x) s

def suites : Array Suite := #[layout, exceptions, javaDoubleText]

end Tests.Api.LayeredNodeJava
