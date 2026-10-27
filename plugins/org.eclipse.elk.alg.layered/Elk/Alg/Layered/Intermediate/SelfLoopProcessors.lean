import Elk.Alg.Layered.Intermediate.Loops
import Elk.Alg.Layered.Intermediate.SelfLoopPreprocessor
import Elk.Alg.Layered.Intermediate.SelfLoopPortRestorer
import Elk.Alg.Layered.Intermediate.SelfLoopPostprocessor
/-!
# Self-loop intermediate processors

Aggregator of the self-loop model (`intermediate.loops`) and the processors
`SelfLoopPreProcessor`, `SelfLoopPortRestorer` and `SelfLoopPostProcessor` (each registers
itself with `IntermediateProcessorStrategy.register` at initialisation). `SelfLoopRouter` and
`loops.routing` are added by the router task.
-/
