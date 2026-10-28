import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
Regression tests for the layered crossing minimisation (P3) and the processors around it aligned
with ELK Java 0.12.0 (agent P3J). Every fixture under `tests/fixtures/p3java/` is laid out with
`Elk.Api.layoutJson` and compared at tolerance `0` with the layout of unmodified ELK Java 0.12.0
(`<name>.java.json`, `scripts/run_java_baseline.sh`). All of them failed (or did not terminate)
before their fix. Random graphs come from `scripts/run_random_java_parity.sh` (seed sets `s5`, `v5`)
or from their crossing minimisation option variants (strategy, greedy switch, model order, node
promotion, interactive positions and sections):

* `barycenter_live_port_order` (`s5/g0032`): `BarycenterHeuristic.calculateBarycenter` visits the
  node's *current* ports (the port distributor reordered them), which decides the recursion into
  in-layer neighbours and so which node gets which perturbation draw.
* `greedy_port_slots` (`v5/g0228`): `GreedyPortDistributor.switchPorts` writes through the side
  view, so a switch exchanges the list slots of the two view positions.
* `first_try_shared_property`: `FIRST_TRY_WITH_INITIAL_ORDER` and `SECOND_TRY_WITH_INITIAL_ORDER`
  share one property id, so only the first randomized run keeps the initial order.
* `first_try_left_by_early_return`: a run returning early (initial order without crossings) leaves
  the flag on the graph, and the greedy switch run on that graph reads it.
* `greedy_shared_port_positions`: the in-layer counters of a `SwitchDecider` share the greedy
  heuristic's port position array (stale positions of other layers included).
* `sort_by_input_model_ports`: `SortByInputModelProcessor` sorts the ports with `Collections.sort`
  (TimSort) and the stateful `ModelOrderPortComparator`; the port comparators of layer 0 see its
  sorted node order.
* `north_south_model_order`: `NorthSouthPortPreprocessor.modelOrderNorthSouthInputReversing`
  (`Lists.reverse(incoming).addAll(outgoing)` puts the outgoing ports first, reversed).
* `importer_section_ports`: a port created for an edge end at a node with fixed port sides starts
  at the section's start/end point (`ElkGraphImporter.transformEdge`).
* `node_promotion_model_order`: `NodePromotion.modelOrderNodePromotion` (Java's index handling,
  dynamic layer bounds and maximal keys; did not terminate before).
* `model_order_median_first_layer`: `ModelOrderBarycenterHeuristic.setFirstLayerOrder` sorts the
  first layer with the model order insertion sort; `MedianHeuristic` sorts with TimSort and
  `weightComparator`.
* `interactive_original_bendpoints` (hand-made): `InteractiveCrossingMinimizer` interpolates the
  long edge dummies along `ORIGINAL_BENDPOINTS` (the imported section).
* `greedy_switch_index_error`: Java's `BinaryIndexedTree.rank` throws
  `ArrayIndexOutOfBoundsException` on a stale far-end position (did not terminate before).
-/
namespace Tests.Api.LayeredP3Java

open Tests Elk.Api Elk.Core.Util

private def fixtureDir : System.FilePath := "tests/fixtures/p3java"

/-- The fixtures laid out and compared with `<name>.java.json`. -/
def fixtures : Array String := #[
  "barycenter_live_port_order", "greedy_port_slots", "first_try_shared_property", "first_try_left_by_early_return",
  "greedy_shared_port_positions", "sort_by_input_model_ports", "north_south_model_order", "importer_section_ports",
  "node_promotion_model_order", "model_order_median_first_layer", "interactive_original_bendpoints"]

def layouts : Suite := suite "layered.p3Java" do
  for name in fixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
    | .ok out =>
      let expected ← IO.FS.readFile (fixtureDir / s!"{name}.java.json")
      checkJson s!"{name}: ELK Java layout (tol 0)" out expected
    | .error e => report s!"{name}: layout expected" false e

def errors : Suite := suite "layered.p3Java.errors" do
  let input ← IO.FS.readFile (fixtureDir / "greedy_switch_index_error.json")
  match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
  | .ok _ => report "greedy_switch_index_error: Java's exception expected" false "layout succeeded"
  | .error e =>
    checkEq "greedy_switch_index_error: ELK Java's exception text" e
      "java.lang.ArrayIndexOutOfBoundsException: Index 9 out of bounds for length 9"

def suites : Array Suite := #[layouts, errors]

end Tests.Api.LayeredP3Java
