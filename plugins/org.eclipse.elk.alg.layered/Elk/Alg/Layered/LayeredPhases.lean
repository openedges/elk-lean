import Elk.Core.Alg
import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Intermediate.IntermediateProcessorStrategy
/-!
# `org.eclipse.elk.alg.layered.LayeredPhases` + the layered processor/phase registries

Processors and phase implementations live in their own modules (ported incrementally); they
register here at module initialisation. `IntermediateProcessorStrategy.create` and the
phase factories look the implementations up and throw `UnsupportedOperationException` for
processors that are not ported yet, so the pipeline can be exercised processor by processor
against the oracle traces.
-/
namespace Elk.Alg.Layered

open Elk.Graph Elk.Core.Alg Elk.Alg.Layered.Graph Elk.Alg.Layered.Intermediate

/-- `LayeredPhases` (Java ordinal order). -/
elk_enum LayeredPhases := p1CycleBreaking p2Layering p3NodeOrdering p4NodePlacement p5EdgeRouting

/-- `ILayoutProcessor<LGraph>`. -/
abbrev LayeredProcessor := LayoutProcessor LayeredM LGraphId
/-- `ILayoutPhase<LayeredPhases, LGraph>`. -/
abbrev LayeredPhase := LayoutPhase LayeredM LayeredPhases LGraphId IntermediateProcessorStrategy
/-- `ILayoutPhaseFactory<LayeredPhases, LGraph>`. -/
abbrev LayeredPhaseFactory := LayoutPhaseFactory LayeredM LayeredPhases LGraphId IntermediateProcessorStrategy
/-- `LayoutProcessorConfiguration<LayeredPhases, LGraph>`. -/
abbrev LayeredProcessorConfiguration := LayoutProcessorConfiguration LayeredPhases IntermediateProcessorStrategy
/-- `AlgorithmAssembler<LayeredPhases, LGraph>`. -/
abbrev LayeredAssembler := AlgorithmAssembler LayeredM LayeredPhases LGraphId IntermediateProcessorStrategy

/-- `NoOpPhase`: a phase that does nothing and requests no processors. -/
def noOpPhase (name : String := "NoOpPhase") : LayeredPhase :=
  { name := name, process := fun _ _ => pure (), getLayoutProcessorConfiguration := fun _ => pure none }

namespace Intermediate.IntermediateProcessorStrategy

/-- Registered processor implementations by ordinal. -/
builtin_initialize registry : IO.Ref (Array (Option LayeredProcessor)) ←
  IO.mkRef (Array.replicate (ElkEnum.count (α := IntermediateProcessorStrategy)) none)

/-- Registers the implementation of a strategy constant (called by the processor modules at
module initialisation). -/
def register (s : IntermediateProcessorStrategy) (p : LayeredProcessor) : IO Unit :=
  registry.modify (·.set! (ElkEnum.ordinal s) (some p))

/-- Whether the processor of `s` has been ported. -/
def isAvailable (s : IntermediateProcessorStrategy) : IO Bool := do
  return ((← registry.get)[ElkEnum.ordinal s]?.bind id).isSome

/-- `ILayoutProcessorFactory.create()`: the registered processor, or an
`UnsupportedOperationException` naming the missing one. -/
def create (s : IntermediateProcessorStrategy) : IO LayeredProcessor := do
  match (← registry.get)[ElkEnum.ordinal s]?.bind id with
  | some p => return p
  | none => throw (IO.userError s!"java.lang.UnsupportedOperationException: Layout processor {ElkEnum.javaName s} is not ported yet.")

end Intermediate.IntermediateProcessorStrategy

namespace LayeredPhases

/-- Registered phase implementations: `[phase ordinal][strategy ordinal]`. -/
builtin_initialize phaseRegistry : IO.Ref (Array (Array (Option (IO LayeredPhase)))) ←
  IO.mkRef (Array.replicate (ElkEnum.count (α := LayeredPhases)) #[])

/-- Registers the phase implementation created for the strategy constant `ordinal` of `phase`
(e.g. `CycleBreakingStrategy.GREEDY` → `GreedyCycleBreaker`). -/
def registerPhase (phase : LayeredPhases) (ordinal : Nat) (create : IO LayeredPhase) : IO Unit :=
  phaseRegistry.modify fun r =>
    let pi := ElkEnum.ordinal phase
    let slots := r[pi]?.getD #[]
    let slots := if slots.size > ordinal then slots else slots ++ Array.replicate (ordinal + 1 - slots.size) none
    r.set! pi (slots.set! ordinal (some create))

/-- The phase factory for strategy constant `ordinal` (of the enumeration `enumName`) of `phase`;
`enumName × ordinal` is the assembler cache key. -/
def strategyFactory (phase : LayeredPhases) (enumName : String) (ordinal : Nat) (javaName : String) : LayeredPhaseFactory :=
  { key := some (enumName, ordinal)
    create := do
      match ((← phaseRegistry.get)[ElkEnum.ordinal phase]?.bind (·[ordinal]?)).bind id with
      | some create => create
      | none => throw (IO.userError s!"java.lang.UnsupportedOperationException: Layout phase {enumName}.{javaName} is not ported yet.") }

end LayeredPhases

end Elk.Alg.Layered
