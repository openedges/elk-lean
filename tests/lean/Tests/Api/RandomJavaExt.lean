import Tests.Framework
import Tests.JsonCompare
import Elk.Api
import Elk.Core.Util.Sort
/-!
Regression tests for agent EXT (the external-port set `x`: compound nodes with external ports,
port constraints, labels and alignment, mixed hierarchy handling and cross-hierarchy edges, against
ELK Java 0.12.0). Every fixture under `tests/fixtures/ext/` is laid out with `Elk.Api.layoutJson`;
it must fail with the exception text of unmodified ELK Java 0.12.0 (`<name>.java.error`) or equal
Java's layout at tolerance `0` (`<name>.java.json`). The fixtures are greedy reductions of generated
graphs (`scripts/gen_external_port_graphs.py`) that keep Java's outcome, on which the elk-lean binary
before EXT differed from Java and the EXT binary does not (`docs/robustness-random-graphs.md`
section 22).

* `external_port_dummy_null_node_size` (from `x1/x0011`): `CompoundGraphPreprocessor` passes a
  `null` node size to `LGraphUtil.createExternalPortDummy`; `FIXED_RATIO` dereferences it.
* `parent_hyperedge_inside_self_loop_scan` (from `x1/x0171`): the inside self loop scan of
  `importFlatGraph` calls `getSourceNode` on a hyperedge of the parent.
* `sweep_type_decider_node_without_layer` (from `x1/x0013`), `sweep_type_decider_stale_index`
  (from `x1/x0422`): `LayerSweepTypeDecider.nodeInfoFor` of the nested graph's external port dummy
  that a north/south `PORT_DUMMY` names.
* `spline_anchor_north_south_without_coordinate` (from `x1/x0080`): `SplineSegment.anchorY` unboxes a
  missing `SPLINE_NS_PORT_Y_COORD` (the `SOUTH` port of a northern external port dummy).
* `label_dummy_remover_post_compaction` (from `x1/x0560`): labels at the compacted dummy position.
* `resize_node_label_zero_height` (from `x9/x0495`), `lgraph_resize_node_label_zero_height` (from
  `x3/x0467`): `ElkUtil.resizeNode` / `LGraphUtil.resizeNode` move the label of a node of height
  `0` to the bottom (percentages divided by `0`).
* `compaction_junction_points` (from `x2/x0129`): the post compaction moves junction points.
* `compound_postprocessor_top_level_external_port` (from `x2/x0259`): `CrossHierarchyEdge`'s
  `(LPort)` cast of a top-level external port dummy's `ElkPort` origin.
* `north_south_crossings_stale_port_dummy` (from `x1/x0313`): the north/south crossing count reads
  the stale positions of a compound node's nested external port dummy.
* `scanline_invalid_hitboxes` (from `x10/x0275`): the post compaction's scanline `TreeSet` rejects
  an interval with the centre of an active one.
* `self_loop_routing_slot_count` (from `x6/x0398`): Java's routing slot counts leave unoccupied
  sides without slots (`ArrayIndexOutOfBoundsException` for a label there).
* `hierarchical_port_restore_order_negative_zero` (from `x6/x0452`): `restoreProperOrder` sorts
  `-0.0` before `0.0` (`Double.compare`).
* `rectpacking_padding_sum` (from `x2/x0302`): `drawing + padding.getVertical()`.
-/
namespace Tests.Api.RandomJavaExt

open Tests Elk.Api

private def fixtureDir : System.FilePath := "tests/fixtures/ext"

/-- Fixture names (`<name>.json` without the `.java.*` files), sorted. -/
private def fixtureNames : IO (Array String) := do
  let mut names : Array String := #[]
  for e in ← fixtureDir.readDir do
    if e.fileName.endsWith ".json" && !e.fileName.endsWith ".java.json" then
      names := names.push (e.fileName.dropEnd ".json".length).toString
  return Elk.Core.Util.stableSort names compare

def fixtures : Suite := suite "ext.java" do
  let names ← fixtureNames
  check "fixtures found" (names.size > 0)
  for name in names do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    let errPath := fixtureDir / s!"{name}.java.error"
    let out ← layoutJson input "{}" (pretty := false) (sortKeys := true)
    if ← errPath.pathExists then
      let expected := (← IO.FS.readFile errPath).trimAscii.toString
      match out with
      | .ok _ => report s!"{name}: Java's exception expected" false "layout succeeded"
      | .error e => checkEq s!"{name}: ELK Java's exception text" e expected
    else
      match out with
      | .ok o =>
        let expected ← IO.FS.readFile (fixtureDir / s!"{name}.java.json")
        checkJson s!"{name}: ELK Java layout (tol 0)" o expected
      | .error e => report s!"{name}: layout expected" false e

def suites : Array Suite := #[fixtures]

end Tests.Api.RandomJavaExt
