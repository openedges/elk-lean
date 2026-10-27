import Tests.Layered.Options
import Tests.Layered.Graph
/-! Tests of the layered plugin: one file per package. -/
namespace Tests.Layered

def suites : Array Tests.Suite := Options.suites ++ Graph.suites

end Tests.Layered
