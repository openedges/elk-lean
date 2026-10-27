import Tests.Layered.Options
import Tests.Layered.Graph
import Tests.Layered.Transform
/-! Tests of the layered plugin: one file per package. -/
namespace Tests.Layered

def suites : Array Tests.Suite := Options.suites ++ Graph.suites ++ Transform.suites

end Tests.Layered
