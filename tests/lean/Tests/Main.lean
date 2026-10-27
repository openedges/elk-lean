import Tests.Framework
import Tests.Core.Foundation
import Tests.Core.Options
import Tests.Core.Math
import Tests.Core.Util
import Tests.Graph.All

/-- Test driver (`lake test`). Add each plugin's `suites` here. -/
def main : IO UInt32 := do
  let suites :=
    Tests.Core.Foundation.suites ++ Tests.Core.Options.suites ++ Tests.Core.Math.suites ++
    Tests.Core.Util.suites ++ Tests.Graph.suites
  Tests.runSuites suites
