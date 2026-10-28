import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
Regression tests for the layered arithmetic and processor details aligned with ELK Java 0.12.0
(agent LEDGE, random-graph classes `LEDGE`/`LPOS`/`LSIZE`, `docs/robustness-random-graphs.md`).
Every fixture under `tests/fixtures/ledge/` is a reduced random graph (the layered unit that differed,
wrapped in a layered root) laid out with `Elk.Api.layoutJson` and compared at tolerance `0` with the
layout of unmodified ELK Java 0.12.0 (`<name>.java.json`, `scripts/run_java_baseline.sh`). Each one
failed before its fix:

* `orthogonal_float_xpos`: `OrthogonalEdgeRouter` keeps only `xpos` in `float`; `startPos` and
  `routingWidth` are `double` (a bend point `141.9000015258789`, not `141.89999389648438`).
* `bk_port_offset_order`: `BKAligner.insideBlockShift`, `BKAlignedLayout.calculateDelta` and the
  threshold strategy add `port.position.y` and `port.anchor.y` one after the other.
* `self_loop_label_offset`: `OrthogonalSelfLoopRouter.placeLabels` subtracts
  `edgeLabelDistance + size` as one sum.
* `self_loop_topmost_port`: `LabelPlacer` picks the topmost port by `position.y` (no anchor).
* `self_loop_label_coordinates`: `LabelPlacer.computeCoordinates` runs before the routing slot
  assignment, whose label overlap test reads the label block's `x`.
* `inverted_port_long_edge_ends`: `InvertedPortProcessor.setLongEdgeSourceAndTarget` (the dummies'
  long edge ends group the label dummies in `LabelSideSelector`).
* `hierarchical_port_dummy_margins`: `HierarchicalPortOrthogonalEdgeRouter.restoreDummy` computes the
  margins of the restored north/south dummies.
* `self_loop_sequenced_slots`, `self_loop_inline_center` (hand-made, the JSON form of the
  `layered.intermediate.selfLoopRouter` hand graphs): the RIGHT/LEFT aligned label blocks of two
  sequenced north loops do not overlap, so both loops share slot 0; a centred inline label block on
  the east lane keeps `y = 0` (Java sets only `x` for `CENTER`).
* `ns_port_rounding` (hand-made): `NetworkSimplexPlacer` shifts a port whose `position.y + anchor.y`
  is `-2.5` by `y - Math.round(y)` with Java's half-up rounding (`-2`, C `round` gives `-3`).

`mathRound` pins those `Math.round` semantics (`Float.javaRound`).
-/
namespace Tests.Api.LayeredJavaArithmetic

open Tests Elk.Api Elk.Core.Util

private def fixtureDir : System.FilePath := "tests/fixtures/ledge"

/-- The fixtures (`<name>.json` laid out, `<name>.java.json` ELK Java's layout). -/
def fixtures : Array String := #[
  "orthogonal_float_xpos", "bk_port_offset_order", "self_loop_label_offset", "self_loop_topmost_port",
  "self_loop_label_coordinates", "inverted_port_long_edge_ends", "hierarchical_port_dummy_margins",
  "ns_port_rounding", "self_loop_sequenced_slots", "self_loop_inline_center"]

def layouts : Suite := suite "layered.javaArithmetic" do
  for name in fixtures do
    let input ← IO.FS.readFile (fixtureDir / s!"{name}.json")
    match ← layoutJson input "{}" (pretty := false) (sortKeys := true) with
    | .ok out =>
      let expected ← IO.FS.readFile (fixtureDir / s!"{name}.java.json")
      checkJson s!"{name}: ELK Java layout (tol 0)" out expected
    | .error e => report s!"{name}: layout expected" false e

def mathRound : Suite := suite "layered.javaArithmetic.round" do
  let cases : Array (Float × Int) := #[(2.5, 3), (-2.5, -2), (-0.5, 0), (0.49999999999999994, 0),
    (-1.5, -1), (1.4, 1), (-1.6, -2)]
  for (x, expected) in cases do
    checkEq s!"Math.round({x})" (Float.javaRound x) expected

def suites : Array Suite := #[layouts, mathRound]

end Tests.Api.LayeredJavaArithmetic
