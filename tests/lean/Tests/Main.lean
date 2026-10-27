import Tests.Framework
import Tests.Core.Foundation
import Tests.Core.Options
import Tests.Core.Math
import Tests.Core.Util
import Tests.Core.Meta
import Tests.Core.Validation
import Tests.Core.Alg
import Tests.Core.Engine
import Tests.Graph.All
import Tests.Json.All
import Tests.Json.Importer
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

/-- Test driver (`lake test`). Add each plugin's `suites` here. -/
def main : IO UInt32 := do
  let suites :=
    Tests.Core.Foundation.suites ++ Tests.Core.Options.suites ++ Tests.Core.Math.suites ++
    Tests.Core.Util.suites ++ Tests.Core.Meta.suites ++ Tests.Core.Validation.suites ++
    Tests.Graph.suites ++ Tests.Json.suites ++ Tests.Json.Importer.suites ++ Tests.Text.suites ++
    Tests.AlgCommon.NetworkSimplex.suites ++ Tests.AlgCommon.Compaction.suites ++ Tests.AlgCommon.Polyomino.suites ++
    Tests.AlgCommon.Spore.suites ++ Tests.AlgCommon.Geometry.suites ++ Tests.AlgCommon.NodeSpacing.suites ++
    Tests.Layered.suites ++
    Tests.TopdownPacking.suites ++
    Tests.Force.suites ++
    Tests.Disco.suites ++
    Tests.Core.Alg.suites ++
    -- keep `Tests.Core.Engine` last: it registers an extra test algorithm (`core.meta.counts` expects 4)
    Tests.Core.Engine.suites
  Tests.runSuites suites
