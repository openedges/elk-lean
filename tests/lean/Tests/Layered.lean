import Tests.Layered.Options
import Tests.Layered.Graph
import Tests.Layered.Transform
import Tests.Layered.P1Cycles
import Tests.Layered.P2Layers
import Tests.Layered.Components
import Tests.Layered.Compound
/-! Tests of the layered plugin: one file per package. -/
namespace Tests.Layered

def suites : Array Tests.Suite := Options.suites ++ Graph.suites ++ Transform.suites ++ P1Cycles.suites ++ P2Layers.suites ++ Components.suites ++ Compound.suites

end Tests.Layered
