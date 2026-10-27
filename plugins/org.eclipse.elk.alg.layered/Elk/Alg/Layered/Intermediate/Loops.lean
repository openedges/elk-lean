import Elk.Alg.Layered.Intermediate.Loops.SelfLoopPort
import Elk.Alg.Layered.Intermediate.Loops.SelfLoopEdge
import Elk.Alg.Layered.Intermediate.Loops.SelfHyperLoopLabels
import Elk.Alg.Layered.Intermediate.Loops.SelfHyperLoop
import Elk.Alg.Layered.Intermediate.Loops.SelfLoopHolder
import Elk.Alg.Layered.Intermediate.Loops.Ops
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops`

Aggregator of the self-loop model (elk-rs `intermediate/loops/mod.rs`): the pure data modules
(stored in `LNodeInternals.selfLoopHolder`) and their arena-reading operations (`Loops.Ops`).
The routing subpackage (`loops/routing`) is added by the self-loop router task.
-/
