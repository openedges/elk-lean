import Tests.Framework
import Tests.Core.Foundation
import Tests.Core.Options
import Tests.Core.Math
import Tests.Core.Util
import Tests.Core.Meta
import Tests.Core.Validation
import Tests.Core.Engine
import Tests.Graph.All
import Tests.Json.All
import Tests.Json.Importer
import Tests.Text.All

/-- Test driver (`lake test`). Add each plugin's `suites` here. -/
def main : IO UInt32 := do
  let suites :=
    Tests.Core.Foundation.suites ++ Tests.Core.Options.suites ++ Tests.Core.Math.suites ++
    Tests.Core.Util.suites ++ Tests.Core.Meta.suites ++ Tests.Core.Validation.suites ++
    Tests.Graph.suites ++ Tests.Json.suites ++ Tests.Json.Importer.suites ++ Tests.Text.suites ++
    Tests.Core.Engine.suites
  Tests.runSuites suites
