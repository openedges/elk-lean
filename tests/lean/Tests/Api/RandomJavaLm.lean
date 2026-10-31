import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
Regression tests for agent LM (the last elk-rs leftovers of the layered crossing minimisation, the
model order exceptions of nested graphs). Every fixture under `tests/fixtures/lm/` is an input of the
variant sets of `scripts/gen_p3_graphs.py`/NIK (`npb`: node promotion options, every compound node laid
out by layered in the same run) laid out with `Elk.Api.layoutJson`; it must fail with the exception text
of unmodified ELK Java 0.12.0 (`<name>.java.error`, `ElkJavaBaseline`) or equal Java's layout at
tolerance `0` (`<name>.java.json`). All differed from Java before LM:

* `crossing_tree_index_stale_far_end` (`npb/v1_g0132`): the in-layer crossing count of the last layer
  reads the position an earlier count left for an in-layer edge's far end on the other side (`7`) and
  overflows the size-1 tree in `BinaryIndexedTree.rank` (`AllCrossingsCounter.countAllCrossings`, the
  count after the first sweep). The counts now check Java's tree bounds on every path and recount like
  Java (elk-rs cached the count; Lean failed later in a greedy switch with `Index 1 … length 1`).
* `npe_nested_max_model_order` (`npb/v8_g0264`): `MAX_MODEL_ORDER_NODES` is set only on the top-level graph
  of a hierarchical import, so the model order comparison of a nested graph unboxes `null`.
* `npe_edge_model_order_preprocessing` (`npb/v6_g0572`): the edges of a hierarchical import get model
  orders only when the top-level graph needs them, so `longEdgeTargetNodePreprocessing` unboxes `null`.
* `npe_edge_model_order_connected_edges` (`npb/v1_g0128`): the same in
  `ModelOrderNodeComparator.getModelOrderFromConnectedEdges`.
-/
namespace Tests.Api.RandomJavaLm

open Tests Elk.Api

private def fixtureDir : System.FilePath := "tests/fixtures/lm"

/-- The fixtures laid out and compared with `<name>.java.json`. -/
def fixtures : Array String := #[]

/-- The fixtures whose layout fails with Java's exception (`<name>.java.error`). -/
def errorFixtures : Array String := #[
  "crossing_tree_index_stale_far_end", "npe_nested_max_model_order", "npe_edge_model_order_preprocessing",
  "npe_edge_model_order_connected_edges"]

def layouts : Suite := suite "lm.java" do
  for name in fixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
    | .ok out =>
      let expected ← IO.FS.readFile (fixtureDir / s!"{name}.java.json")
      checkJson s!"{name}: ELK Java layout (tol 0)" out expected
    | .error e => report s!"{name}: layout expected" false e

def errors : Suite := suite "lm.java.errors" do
  for name in errorFixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    let expected := (← IO.FS.readFile (fixtureDir / s!"{name}.java.error")).trimAscii.toString
    match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
    | .ok _ => report s!"{name}: Java's exception expected" false "layout succeeded"
    | .error e => checkEq s!"{name}: ELK Java's exception text" e expected

def suites : Array Suite := #[layouts, errors]

end Tests.Api.RandomJavaLm
