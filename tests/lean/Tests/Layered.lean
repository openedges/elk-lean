import Tests.Layered.Options
import Tests.Layered.Graph
import Tests.Layered.Transform
import Tests.Layered.P1Cycles
import Tests.Layered.P2Layers
import Tests.Layered.P4NodesPlacers
import Tests.Layered.IntermediateHierarchicalPorts
import Tests.Layered.P3Counting
import Tests.Layered.IntermediateTransform
import Tests.Layered.IntermediateEdgePorts
import Tests.Layered.P4NodesBK
import Tests.Layered.IntermediateConstraints
import Tests.Layered.IntermediatePreserveOrder
import Tests.Layered.IntermediateWrapping
import Tests.Layered.Import
import Tests.Layered.IntermediateCompaction
import Tests.Layered.P5Splines
import Tests.Layered.IntermediateLabels
import Tests.Layered.IntermediateSelfLoops
import Tests.Layered.P5Orthogonal
import Tests.Layered.Components
import Tests.Layered.Compound
/-! Tests of the layered plugin: one file per package. -/
namespace Tests.Layered

def suites : Array Tests.Suite := Options.suites ++ Graph.suites ++ Transform.suites ++ P1Cycles.suites ++ P2Layers.suites ++ P4NodesPlacers.suites ++ IntermediateHierarchicalPorts.suites ++ P3Counting.suites ++ IntermediateTransform.suites ++ IntermediateEdgePorts.suites ++ P4NodesBK.suites ++ IntermediateConstraints.suites ++ IntermediatePreserveOrder.suites ++ IntermediateWrapping.suites ++ Import.suites ++ IntermediateCompaction.suites ++ P5Splines.suites ++ IntermediateLabels.suites ++ IntermediateSelfLoops.suites ++ P5Orthogonal.suites ++ Components.suites ++ Compound.suites

end Tests.Layered
