import Elk.Alg.Layered.Intermediate.IntermediateProcessorStrategy
import Elk.Alg.Layered.Intermediate.LabelDummySwitcher
import Elk.Alg.Layered.Intermediate.EdgePortProcessors
import Elk.Alg.Layered.Intermediate.SelfLoopProcessors
import Elk.Alg.Layered.Intermediate.HierarchicalPortProcessors
import Elk.Alg.Layered.Intermediate.GreedySwitch
import Elk.Alg.Layered.Intermediate.TransformProcessors
/-!
# `org.eclipse.elk.alg.layered.intermediate`

Aggregator of the layered intermediate processors. Each processor registers itself in
`IntermediateProcessorStrategy` at initialization, so every module must be imported here for the
pipeline to find it.
-/
