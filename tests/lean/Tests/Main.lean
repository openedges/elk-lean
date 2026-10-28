import Tests.Framework
import Tests.Core.Foundation
import Tests.Core.Options
import Tests.Core.Math
import Tests.Core.Util
import Tests.Core.RustSort
import Tests.Core.JavaSort
import Tests.Core.FastFloat
import Tests.Core.Meta
import Tests.Core.Validation
import Tests.Core.Alg
import Tests.Core.Engine
import Tests.Graph.All
import Tests.Json.All
import Tests.Json.Importer
import Tests.Json.ParserFuzz
import Tests.Json.Zmij
import Tests.Text.All
import Tests.AlgCommon.NetworkSimplex
import Tests.AlgCommon.Compaction
import Tests.AlgCommon.Polyomino
import Tests.AlgCommon.Spore
import Tests.AlgCommon.Geometry
import Tests.AlgCommon.NodeSpacing
import Tests.Layered
import Tests.TopdownPacking
import Tests.Force
import Tests.Disco
import Tests.Spore
import Tests.VertiFlex
import Tests.Radial
import Tests.MrTree
import Tests.RectPacking
import Tests.Api.PerfBenchmark
import Tests.Api.Robustness
import Tests.Api.Sections

/-- Test driver (`lake test`). Add each plugin's `suites` here. `lake test -- --suite <prefix>` runs
only the suites whose name starts with `<prefix>`. -/
def main (args : List String) : IO UInt32 := do
  let suites :=
    Tests.Core.Foundation.suites ++ Tests.Core.Options.suites ++ Tests.Core.Math.suites ++
    Tests.Core.Util.suites ++
    Tests.Core.RustSort.suites ++ Tests.Core.JavaSort.suites ++ Tests.Core.FastFloat.suites ++ Tests.Core.Meta.suites ++ Tests.Core.Validation.suites ++
    Tests.Graph.suites ++ Tests.Json.suites ++ Tests.Json.Importer.suites ++ Tests.Json.ParserFuzz.suites ++
    Tests.Json.Zmij.suites ++ Tests.Text.suites ++
    Tests.AlgCommon.NetworkSimplex.suites ++ Tests.AlgCommon.Compaction.suites ++ Tests.AlgCommon.Polyomino.suites ++
    Tests.AlgCommon.Spore.suites ++ Tests.AlgCommon.Geometry.suites ++ Tests.AlgCommon.NodeSpacing.suites ++
    Tests.Layered.suites ++
    Tests.TopdownPacking.suites ++
    Tests.Force.suites ++
    Tests.Disco.suites ++
    Tests.Spore.suites ++
    Tests.VertiFlex.suites ++
    Tests.Radial.suites ++
    Tests.MrTree.suites ++
    Tests.RectPacking.suites ++
    Tests.Api.PerfBenchmark.suites ++
    Tests.Api.Robustness.suites ++
    Tests.Api.Sections.suites ++
    Tests.Core.Alg.suites ++
    -- keep `Tests.Core.Engine` last: it registers an extra test algorithm (`core.meta.counts` expects 4)
    Tests.Core.Engine.suites
  match args with
  | ["--suite", pre] => Tests.runSuites (suites.filter (·.name.startsWith pre))
  | _ => Tests.runSuites suites
