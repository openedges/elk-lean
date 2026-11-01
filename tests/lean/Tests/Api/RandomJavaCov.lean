import Tests.Framework
import Tests.JsonCompare
import Elk.Api
import Elk.Core.Util.Sort
/-!
Regression tests for agent COV (the layered coverage set `w`: wrapping, comment boxes, hypernodes,
edge labels, splines, BK alignments, merged edges, against ELK Java 0.12.0). Every fixture under
`tests/fixtures/cov/` is laid out with `Elk.Api.layoutJson`; it must fail with the exception text of
unmodified ELK Java 0.12.0 (`<name>.java.error`) or equal Java's layout at tolerance `0`
(`<name>.java.json`). The fixtures are greedy reductions of generated graphs
(`scripts/gen_wrapping_graphs.py`) that keep Java's outcome and on which the elk-lean binary before
COV differed from Java (`docs/robustness-random-graphs.md` section 21).

* `object_option_cuts`, `object_option_label_manager`: `OBJECT` options without `IDataObject`
  class are rejected by Java's JSON importer (`IllegalStateException: IDataType class expected …`).
* `label_dummy_chain_no_incoming_edge` (from `w1/w0019`): `LabelDummySwitcher` walks the long edge
  chain with `getIncomingEdges().iterator().next()` (`NoSuchElementException`).
* `breaking_point_remover_null_spline_route` (from `w1/w0002`): `BreakingPointRemover` joins a `null`
  spline route (`NullPointerException` of `addAll`).
* `long_edge_joiner_fewer_outgoing_edges` (from `w1/w0359`): `LongEdgeJoiner.joinAt` takes the first
  remaining outgoing edge once per incoming edge (`IndexOutOfBoundsException`).
* `end_label_sorter_port_without_cell` (from `w2/w0306`): Java's `EndLabelSorter` (elk-rs sorted label
  dummies instead) dereferences the missing label cell of a port that needs sorting.
* `end_label_sorter_groups` (from `w1/w0121`): the tail labels of two merged edges leaving one port
  are regrouped by edge and ordered by target node id (Java `EndLabelSorter`).
* `layer_sweep_empty_layer` (from `w6/w0488`): an empty breaking point layer reaches
  `LayerSweepTypeDecider.initAtLayerLevel` (`ArrayIndexOutOfBoundsException`).
* `spacing_null_option_breaking_point` (from `w2/w0061`): `Spacings.getLocalSpacing` for a node type
  pair without spacing option (`NullPointerException` in `MapPropertyHolder.getProperty`).
* `label_dummy_switcher_turned_back_edge` (from `w10/w0449`): the layer range of a label dummy whose
  long edge a wrapping step turned back (`ArrayIndexOutOfBoundsException` in `computeLayerWidthSums`).
* `apply_cuts_original_layer_indexes`: `BreakingPointInserter.applyCuts` skips the inserted layers
  like Java's `ListIterator` (hand-made path of 8 nodes with two ARD cuts).
* `comment_box_port_scan_south` (from `w1/w0351`): `CommentPreprocessor` ends the port scan at the
  first southern connection.
* `wrapping_default_aspect_ratio` (from `w1/w0307`): without `elk.aspectRatio` the wrapping
  statistics use Java's layered default `1.6f` widened to `double` (`1.600000023841858`; elk-rs `1.0`).
* `polyline_zero_node_spacing` (from `w1/w0074`): `PolylineEdgeRouter`'s
  `Math.min(1, edgeSpacing / nodeSpacing)` for a node spacing of `0`.
-/
namespace Tests.Api.RandomJavaCov

open Tests Elk.Api

private def fixtureDir : System.FilePath := "tests/fixtures/cov"

/-- Fixture names (`<name>.json` without the `.java.*` files), sorted. -/
private def fixtureNames : IO (Array String) := do
  let mut names : Array String := #[]
  for e in ← fixtureDir.readDir do
    if e.fileName.endsWith ".json" && !e.fileName.endsWith ".java.json" then
      names := names.push (e.fileName.dropEnd ".json".length).toString
  return Elk.Core.Util.stableSort names compare

def fixtures : Suite := suite "cov.java" do
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

end Tests.Api.RandomJavaCov
