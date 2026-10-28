import Tests.Framework
import Tests.JsonCompare
import Elk.Api
/-!
ELK Java 0.12.0 option semantics of the non-layered algorithms (agent OPT), on the fixtures in
`tests/fixtures/options/` (inputs `<name>.json`; ELK Java outputs `<name>.java.json` from
`ElkJavaBaseline`, or `<name>.error` with Java's `Throwable.toString()`). Every input is laid out with
`Elk.Api.layoutJson` and compared with Java at tolerance `0`.

* `options.java.defaults`: graphs without options — Java reads the options through the redeclared
  `<Algorithm>Options` constants (`new Property<>(CoreOptions.X, X_DEFAULT)` for every
  `supports X = value` of the `.melk`): force padding 50 / node spacing 80 / aspect ratio `1.6f` /
  edge label spacing 5, mrtree padding 20 / edge-node spacing 3 / priority 1 / aspect ratio `1.6f`,
  rectangle packing padding 15 / spacing 15 / aspect ratio 1.3, SPOrE padding 8 / spacing 8 (the
  `plain_*` graphs are agent RJ2's three node probes); the cloneable `ElkPadding` default stored by
  the top-down engine's `CoreOptions.PADDING` read (12) wins over the child algorithm's own default
  (`topdown_*`).
* `options.java.enums`: algorithm options given as strings, parsed like Java (elk-rs has no parser
  for them): force model, stress dimension, mrtree weighting / routing / search order, radial
  compactor / sorter / wedge criteria, rectangle packing strategies, VertiFlex strategy, SPOrE
  processing order; and the Java algorithm paths behind them (mrtree `LEVEL_PROC` and depth first
  component split, radial wedge criteria / `acos` precedence / overlap removal step 1, VertiFlex
  model order split).
* `options.java.exceptions`: Java's exceptions on these paths (`NullPointerException` of the polar
  sorter and of the position translation without `elk.position`, `IllegalArgumentException` of
  `ElkUtil.applyVectorChain` for unrouted mrtree edges, the unset target width of rectangle packing).
-/
namespace Tests.Api.OptionDefaults

open Tests Elk.Api Elk.Json

private def fixtureDir : System.FilePath := "tests/fixtures/options"

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

def defaults : Suite := suite "options.java.defaults" do
  for name in #["plain_force_edge", "plain_force_label", "plain_mrtree_edge", "plain_mrtree_port",
      "plain_radial_edge", "plain_radial_label", "plain_stress_edge", "plain_rectpacking_noedge",
      "force_defaults", "mrtree_defaults", "radial_defaults", "rectpacking_defaults",
      "vertiflex_defaults", "spore_compaction_defaults", "spore_overlap_defaults",
      "topdown_force_root", "topdown_rectpacking_child"] do
    checkAgainstJava name

def enums : Suite := suite "options.java.enums" do
  for name in #["force_eades", "stress_dimension_x", "stress_dimension_y", "mrtree_middle_to_middle",
      "mrtree_weighting_fan", "mrtree_search_bfs", "radial_leaf_number", "radial_radial_compaction",
      "radial_wedge_compaction", "radial_sorter_id", "rectpacking_simple", "rectpacking_trybox",
      "vertiflex_bend", "spore_max_spanning_tree"] do
    checkAgainstJava name

def exceptions : Suite := suite "options.java.exceptions" do
  for name in #["mrtree_routing_none", "radial_sorter_polar_npe", "radial_edge_length_position_npe",
      "rectpacking_target_width_unset"] do
    let expected := (← IO.FS.readFile (fixtureDir / s!"{name}.error")).trimAscii.toString
    match ← layoutFixture name with
    | .ok _ => report s!"{name}: exception expected" false
    | .error e => checkEq s!"{name}: Java exception" (javaExceptionText e) expected

def suites : Array Suite := #[defaults, enums, exceptions]

end Tests.Api.OptionDefaults
