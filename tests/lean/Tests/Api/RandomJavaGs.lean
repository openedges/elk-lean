import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
Regression tests for agent GS (the greedy switch `NullPointerException` of ELK Java 0.12.0 and the
hierarchical import). Every
fixture under `tests/fixtures/gs/` is laid out with `Elk.Api.layoutJson`; it must fail with the
exception text of unmodified ELK Java 0.12.0 (`<name>.java.error`) or equal Java's layout at
tolerance `0` (`<name>.java.json`).

The pattern: a port of a node without port constraints (`UNDEFINED` → `FREE`, so the import sets no
`NON_FREE_PORTS`) with exactly one incoming and one outgoing edge (no `HYPEREDGES` either). With
neither property the `InvertedPortProcessor` is not scheduled; `PortSideProcessor` puts the port on
`WEST` (net flow `0`), so its outgoing edge leaves a western port towards the next layer. When the
greedy switch compares two nodes of that next layer, `BetweenLayerEdgeTwoNodeCrossingsCounter` only
numbered the *eastern* ports of the western layer, and `AdjacencyList.addAdjacencyOf` unboxes
`portPositions.get(westernPort) == null`. Lean skipped the edge before GS and laid the graph out.

* `npe_pass_through_port`: the minimal case (a labelled edge puts a second node into the target's layer).
* `npe_random_v9_g0273` (random set `v9/g0273`, also its four P3 variants) and
  `npe_disco_layered_components` (DisCo set `c4/g0120`, components laid out by layered): the same NPE.
* `aioobe_pass_through_port_single_node_layer`: without the label the target layer has one node, the
  greedy switch never compares, and the crossing count of `LayerSweepCrossingMinimizer` overflows its
  index tree on the unnumbered western port first (matched since LM).
* `pass_through_port_side_fixed`: `FIXED_SIDE` on the node sets `NON_FREE_PORTS`, the
  `InvertedPortProcessor` reroutes the edge and Java lays the graph out.

The hierarchical import and its neighbours (found with GS's hierarchical model order generator):

* `edge_not_found_in_no_layout_compound`: Java's edge loop of `importHierarchicalGraph` also visits
  the graph of a `NO_LAYOUT` compound node (without `ALGORITHM`, so the engine keeps it in the run),
  whose children were never transformed: "could not be found" `UnsupportedGraphException`.
* `no_layout_compound_with_algorithm`: with an `ALGORITHM` the `NO_LAYOUT` node has no resolved
  algorithm, the engine separates it and nothing inside is visited.
* `outside_port_next_to_hierarchical_port`: the parent node's ports get the external port positions
  as computed (elk-rs shifted the "pure self loop" dummy of the outside edge's port).
* `bf_model_order_single_node_without_order` / `df_model_order_node_without_order`: the model order
  layerers fail only from their sort's comparator, i.e. with two or more real nodes.
* `origin_port_class_cast` (generated `h0143`): `sortPortsByDummyPositionsInLastLayer` reaches a
  normal node while walking the last layer for the hierarchical ports, `(LPort) ORIGIN` fails.
-/
namespace Tests.Api.RandomJavaGs

open Tests Elk.Api

private def fixtureDir : System.FilePath := "tests/fixtures/gs"

/-- The fixtures laid out and compared with `<name>.java.json`. -/
def fixtures : Array String := #["pass_through_port_side_fixed", "no_layout_compound_with_algorithm",
  "outside_port_next_to_hierarchical_port", "bf_model_order_single_node_without_order"]

/-- The fixtures whose layout fails with Java's exception (`<name>.java.error`). -/
def errorFixtures : Array String := #[
  "npe_pass_through_port", "npe_random_v9_g0273", "npe_disco_layered_components",
  "aioobe_pass_through_port_single_node_layer", "edge_not_found_in_no_layout_compound",
  "df_model_order_node_without_order", "origin_port_class_cast"]

def layouts : Suite := suite "gs.java" do
  for name in fixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
    | .ok out =>
      let expected ← IO.FS.readFile (fixtureDir / s!"{name}.java.json")
      checkJson s!"{name}: ELK Java layout (tol 0)" out expected
    | .error e => report s!"{name}: layout expected" false e

def errors : Suite := suite "gs.java.errors" do
  for name in errorFixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    let expected := (← IO.FS.readFile (fixtureDir / s!"{name}.java.error")).trimAscii.toString
    match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
    | .ok _ => report s!"{name}: Java's exception expected" false "layout succeeded"
    | .error e => checkEq s!"{name}: ELK Java's exception text" e expected

def suites : Array Suite := #[layouts, errors]

end Tests.Api.RandomJavaGs
