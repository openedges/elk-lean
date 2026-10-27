import Tests.Layered.Options
import Tests.Layered.Graph
import Tests.Layered.Transform
import Tests.Layered.P1Cycles
import Tests.Layered.P2Layers
import Tests.Layered.P4NodesPlacers
import Tests.Layered.IntermediateHierarchicalPorts
import Tests.Layered.P3Counting
import Tests.Layered.IntermediateTransform
import Tests.Layered.Components
import Tests.Layered.Compound
/-! Tests of the layered plugin: one file per package. -/
namespace Tests.Layered

def suites : Array Tests.Suite := Options.suites ++ Graph.suites ++ Transform.suites ++ P1Cycles.suites ++ P2Layers.suites ++ P4NodesPlacers.suites ++ IntermediateHierarchicalPorts.suites ++ P3Counting.suites ++ IntermediateTransform.suites ++ Components.suites ++ Compound.suites

end Tests.Layered
