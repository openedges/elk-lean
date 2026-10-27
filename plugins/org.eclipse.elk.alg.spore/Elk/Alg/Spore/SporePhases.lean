import Elk.Core.Alg.AlgorithmAssembler
import Elk.Alg.Spore.Graph.Graph
/-!
# `org.eclipse.elk.alg.spore.SPOrEPhases`

Port of `spore_phases.rs` (elk-rs) and `SPOrEPhases.java`: the phases of the SPOrE algorithms,
plus the monad and the phase/assembler type abbreviations shared by the phase packages.

Representation of the algorithm graph: the `Graph` is the state of the algorithm's own monad
`SporeM = StateRefT Graph IO`, so the processors (`LayoutProcessor SporeM Unit`) do not receive
the graph as an argument (`G := Unit`), they read and update the monad state. SPOrE has no
intermediate processors; the processor factory enumeration of the assembler is the placeholder
enum `SporeProcessorFactory` (never instantiated).
-/
namespace Elk.Alg.Spore

open Elk Elk.Core.Alg Elk.Alg.Spore.Graph

/-- `org.eclipse.elk.alg.spore.SPOrEPhases`: the three phases of the SPOrE algorithms. -/
elk_enum SPOrEPhases := p1Structure p2ProcessingOrder p3Execution

/-- Placeholder for the (empty) set of intermediate processor factories of SPOrE: the
`AlgorithmAssembler` is parameterised by an enumeration of processor factories, SPOrE has none. -/
elk_enum SporeProcessorFactory := placeholder

/-- The monad of the SPOrE algorithms: the algorithm graph is the state. -/
abbrev SporeM := StateRefT Graph IO

/-- Runs a SPOrE action on a graph: the result and the final graph. -/
@[inline] def SporeM.run {α : Type} (x : SporeM α) (graph : Graph) : IO (α × Graph) :=
  StateRefT'.run x graph

/-- `ILayoutProcessor<Graph>`. -/
abbrev SporeProcessor := LayoutProcessor SporeM Unit

/-- `ILayoutPhase<SPOrEPhases, Graph>`. -/
abbrev SporePhase := LayoutPhase SporeM SPOrEPhases Unit SporeProcessorFactory

/-- `ILayoutPhaseFactory<SPOrEPhases, Graph>`. -/
abbrev SporePhaseFactory := LayoutPhaseFactory SporeM SPOrEPhases Unit SporeProcessorFactory

/-- `AlgorithmAssembler<SPOrEPhases, Graph>`. -/
abbrev SporeAssembler := AlgorithmAssembler SporeM SPOrEPhases Unit SporeProcessorFactory

/-- `AlgorithmAssembler.create()` for SPOrE (no intermediate processors can be requested). -/
def SporeAssembler.create : IO SporeAssembler :=
  AlgorithmAssembler.create fun _ =>
    throw (IO.userError "java.lang.IllegalStateException: SPOrE has no intermediate processors")

/-- The phase configuration of every SPOrE phase: `LayoutProcessorConfiguration.create()`
(no intermediate processors). -/
def noProcessors : SporeM (Option (LayoutProcessorConfiguration SPOrEPhases SporeProcessorFactory)) :=
  pure (some LayoutProcessorConfiguration.create)

end Elk.Alg.Spore
