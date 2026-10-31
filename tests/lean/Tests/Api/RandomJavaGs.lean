import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
Regression tests for agent GS (the greedy switch `NullPointerException` of ELK Java 0.12.0). Every
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
-/
namespace Tests.Api.RandomJavaGs

open Tests Elk.Api

private def fixtureDir : System.FilePath := "tests/fixtures/gs"

/-- The fixtures laid out and compared with `<name>.java.json`. -/
def fixtures : Array String := #["pass_through_port_side_fixed"]

/-- The fixtures whose layout fails with Java's exception (`<name>.java.error`). -/
def errorFixtures : Array String := #[
  "npe_pass_through_port", "npe_random_v9_g0273", "npe_disco_layered_components",
  "aioobe_pass_through_port_single_node_layer"]

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
