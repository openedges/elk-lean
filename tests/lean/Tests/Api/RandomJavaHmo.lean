import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
Regression tests for agent HMO (the hierarchical model order generator `h` sets against ELK Java
0.12.0). Every fixture under `tests/fixtures/hmo/` is laid out with `Elk.Api.layoutJson`; it must
fail with the exception text of unmodified ELK Java 0.12.0 (`<name>.java.error`) or equal Java's
layout at tolerance `0` (`<name>.java.json`). The fixtures are reductions of generated graphs
(`scripts/gen_hierarchical_mo_graphs.py`, seeds 1 and 2) that keep Java's outcome.

* `scc_node_type_no_preferred_ids` (from `h1/h1104`): `SCCNodeTypeCycleBreaker` compares the node's
  group id with the graph's `cbPreferredSourceId`/`cbPreferredTargetId` as boxed `Integer`s (`==`);
  unset preferences are `null` and never match, so connectivity decides (elk-rs defaulted them to `0`
  and reversed the incoming edges of the minimum node).
* `scc_node_type_preferred_source_uncached`: both ids `200` are distinct boxes outside the `Integer`
  cache, the preference does not match either; `..._cached` (ids `1`): it matches.
* `bk_class_graph_cycle_npe` (from `h2/h0687`): the class graph of `BKCompactor` has a cycle, a class
  that is never placed keeps `classShift == null`, and the final coordinate loop unboxes it.
* `coffman_graham_cycle_stack_overflow` (from `h1/h1143`): `MODEL_ORDER` cycle breaking leaves a
  cycle through a `noModelOrder` node, and the transitive reduction DFS of `CoffmanGrahamLayerer`
  recurses until the stack overflows (Lean ran its explicit stack without bound).
* `longest_path_cycle_stack_overflow` (from `h6/h0433`): the same cycle in `LongestPathLayerer.visit`.
* `hierarchical_sweep_empty_nested_order_aioobe` (from the P3 variant `p2/v2_g0045`): the hierarchical
  layer sweep reads `nestedGraphNodeOrder[startIndex][0]` of a nested graph without nodes to order.
* `hierarchical_edge_offset_summation` (from `h3/h0190`): the hierarchical offset of an edge whose
  coordinates belong to a graph two levels up is summed like Java's `KVector.add` chain (elk-rs
  grouped the terms, one ulp off).
-/
namespace Tests.Api.RandomJavaHmo

open Tests Elk.Api

private def fixtureDir : System.FilePath := "tests/fixtures/hmo"

/-- The fixtures laid out and compared with `<name>.java.json`. -/
def fixtures : Array String := #["scc_node_type_no_preferred_ids", "scc_node_type_preferred_source_uncached",
  "scc_node_type_preferred_source_cached", "hierarchical_edge_offset_summation"]

/-- The fixtures whose layout fails with Java's exception (`<name>.java.error`). -/
def errorFixtures : Array String := #["bk_class_graph_cycle_npe", "coffman_graham_cycle_stack_overflow",
  "longest_path_cycle_stack_overflow", "hierarchical_sweep_empty_nested_order_aioobe"]

def layouts : Suite := suite "hmo.java" do
  for name in fixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
    | .ok out =>
      let expected ← IO.FS.readFile (fixtureDir / s!"{name}.java.json")
      checkJson s!"{name}: ELK Java layout (tol 0)" out expected
    | .error e => report s!"{name}: layout expected" false e

def errors : Suite := suite "hmo.java.errors" do
  for name in errorFixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    let expected := (← IO.FS.readFile (fixtureDir / s!"{name}.java.error")).trimAscii.toString
    match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
    | .ok _ => report s!"{name}: Java's exception expected" false "layout succeeded"
    | .error e => checkEq s!"{name}: ELK Java's exception text" e expected

def suites : Array Suite := #[layouts, errors]

end Tests.Api.RandomJavaHmo
