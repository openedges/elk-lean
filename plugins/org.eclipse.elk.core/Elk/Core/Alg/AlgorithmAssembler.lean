import Elk.Core.Alg.LayoutPhase
import Elk.Core.Alg.EnumBasedFactoryComparator
import Elk.Core.Util.Sort
import Elk.Core.Util.ElkTrace
import Elk.Core.Exceptions
/-!
# `org.eclipse.elk.core.alg.AlgorithmAssembler`

Assembles the processor list of an algorithm from its phases (`P`) and the processor
factories (`F`) they and the configurator request. The assembler is a mutable object in
Java/Rust (phase/processor caches survive across `build` calls), so it is an `IO.Ref`
handle here.
-/
namespace Elk.Core.Alg

open Elk.Graph Elk.Core.Util

/-- Mutable state of an `AlgorithmAssembler<P, G>`. -/
structure AlgorithmAssemblerState (m : Type → Type) (P G F : Type) where
  enableCaching : Bool := true
  failOnMissingPhase : Bool := true
  /-- Processor factory for the enum constants `F`. -/
  processorFactory : LayoutProcessorFactory m G F
  /-- Phase factory per phase ordinal. -/
  phases : Array (Option (LayoutPhaseFactory m P G F))
  /-- `configuredPhases`: phases with a factory. -/
  configuredPhases : Array Bool
  /-- `additionalProcessors`. -/
  additionalProcessors : LayoutProcessorConfiguration P F := {}
  /-- `phaseCache` keyed by the factory's enum identity. -/
  phaseCache : Array ((String × Nat) × LayoutPhase m P G F) := #[]
  /-- `processorCache` by `F` ordinal. -/
  processorCache : Array (Option (LayoutProcessor m G))

/-- `AlgorithmAssembler<P, G>` handle. -/
structure AlgorithmAssembler (m : Type → Type) (P G F : Type) where
  ref : IO.Ref (AlgorithmAssemblerState m P G F)

namespace AlgorithmAssembler

variable {m : Type → Type} {P G F : Type} [ElkEnum P] [ElkEnum F] [BEq F] [Inhabited F]

/-- `AlgorithmAssembler.create()` for the phase enumeration `P` and factory enumeration `F`. -/
def create (processorFactory : LayoutProcessorFactory m G F) : IO (AlgorithmAssembler m P G F) := do
  if ElkEnum.count (α := P) == 0 then
    throw (IO.userError "java.lang.IllegalStateException: There must be at least one phase in the phase enumeration.")
  let ref ← IO.mkRef {
    processorFactory := processorFactory
    phases := Array.replicate (ElkEnum.count (α := P)) none
    configuredPhases := Array.replicate (ElkEnum.count (α := P)) false
    processorCache := Array.replicate (ElkEnum.count (α := F)) none : AlgorithmAssemblerState m P G F }
  return ⟨ref⟩

/-- `withCaching(enabled)`. -/
def withCaching (a : AlgorithmAssembler m P G F) (enabled : Bool) : IO Unit :=
  a.ref.modify fun s => { s with enableCaching := enabled }

/-- `withFailOnMissingPhase(fail)`. -/
def withFailOnMissingPhase (a : AlgorithmAssembler m P G F) (fail : Bool) : IO Unit :=
  a.ref.modify fun s => { s with failOnMissingPhase := fail }

/-- `clearCache()`. -/
def clearCache (a : AlgorithmAssembler m P G F) : IO Unit :=
  a.ref.modify fun s => { s with phaseCache := #[], processorCache := Array.replicate s.processorCache.size none }

/-- `reset()`: forgets phases and additional processors (keeps the caches). -/
def reset (a : AlgorithmAssembler m P G F) : IO Unit :=
  a.ref.modify fun s => { s with
    phases := Array.replicate s.phases.size none
    configuredPhases := Array.replicate s.configuredPhases.size false
    additionalProcessors := {} }

/-- `setPhase(phase, phaseFactory)`. -/
def setPhase (a : AlgorithmAssembler m P G F) (phase : P) (factory : LayoutPhaseFactory m P G F) : IO Unit :=
  a.ref.modify fun s =>
    let i := ElkEnum.ordinal phase
    { s with phases := s.phases.set! i (some factory), configuredPhases := s.configuredPhases.set! i true }

/-- `addProcessorConfiguration(config)`. -/
def addProcessorConfiguration (a : AlgorithmAssembler m P G F) (config : LayoutProcessorConfiguration P F) : IO Unit :=
  a.ref.modify fun s => { s with additionalProcessors := s.additionalProcessors.addAll config }

/-- `retrievePhase(factory)`: cached by enum identity when caching is enabled. -/
private def retrievePhase (a : AlgorithmAssembler m P G F) (factory : LayoutPhaseFactory m P G F) : IO (LayoutPhase m P G F) := do
  let s ← a.ref.get
  if !s.enableCaching then return ← factory.create
  match factory.key with
  | some key =>
    match s.phaseCache.find? (fun e => e.1 == key) with
    | some (_, phase) => return phase
    | none =>
      let phase ← factory.create
      a.ref.modify fun s => { s with phaseCache := s.phaseCache.push (key, phase) }
      return phase
  | none => factory.create

/-- `retrieveProcessor(factory)`: cached by ordinal when caching is enabled. -/
private def retrieveProcessor (a : AlgorithmAssembler m P G F) (factory : F) : IO (LayoutProcessor m G) := do
  let s ← a.ref.get
  let i := ElkEnum.ordinal factory
  if !s.enableCaching then return ← s.processorFactory factory
  match s.processorCache[i]? with
  | some (some p) => return p
  | _ =>
    let p ← s.processorFactory factory
    a.ref.modify fun s => { s with processorCache := s.processorCache.set! i (some p) }
    return p

/-- `SharedProcessorAdapter`/`PhaseProcessorAdapter`: wraps `process` with the
`ELK_TRACE_PROCESSORS`/`ELK_TRACE_PHASES` (+ timing) stderr traces of the Rust port. The switches
are read once at startup (`ElkTrace.global`), so without them the processor is returned unwrapped
(the wrapper would only call `p.process`). -/
private def traced [Monad m] [MonadLiftT IO m] (isPhase : Bool) (p : LayoutProcessor m G) : LayoutProcessor m G :=
  let t := ElkTrace.global
  let traceOn := if isPhase then t.phases else t.processors
  let timingOn := if isPhase then t.phaseTiming else t.processorTiming
  if !traceOn && !timingOn then p else
  { p with process := fun graph monitor => do
      let kind := if isPhase then "phase" else "processor"
      if traceOn then liftM (m := IO) (IO.eprintln s!"{kind}: {p.name}")
      let start ← if timingOn then liftM (m := IO) IO.monoMsNow else pure 0
      p.process graph monitor
      if timingOn then
        let elapsed := (← liftM (m := IO) IO.monoMsNow) - start
        liftM (m := IO) (IO.eprintln s!"{kind}_done: {p.name} ({elapsed} ms)") }

/-- `retrieveProcessors(factories)`: sorted by `EnumBasedFactoryComparator` (stable), then created. -/
private def retrieveProcessors [Monad m] [MonadLiftT IO m] (a : AlgorithmAssembler m P G F) (factories : Array F) : IO (Array (LayoutProcessor m G)) := do
  let sorted := stableSort factories EnumBasedFactoryComparator.compare
  let mut processors := #[]
  for factory in sorted do
    processors := processors.push (traced false (← a.retrieveProcessor factory))
  return processors

/-- `build(graph)`: the processor list — for every phase in enumeration order the
processors slotted before it, then the phase itself; finally the processors after the
last phase. Throws `IllegalStateException` when phases are missing and
`failOnMissingPhase` is set. -/
def build [Monad m] [MonadLiftT IO m] (a : AlgorithmAssembler m P G F) (graph : G) : m (Array (LayoutProcessor m G)) := do
  let s ← liftM (m := IO) a.ref.get
  let variants : Array P := ElkEnum.values
  let configured := s.configuredPhases.foldl (fun n b => if b then n + 1 else n) 0
  if s.failOnMissingPhase && configured < variants.size then
    liftM (m := IO) (throw (IO.userError s!"java.lang.IllegalStateException: Expected {variants.size} phases to be configured; only found {configured}") : IO Unit)
  let mut phases : Array (Option (LayoutPhase m P G F)) := #[]
  for phase in variants do
    match s.phases[ElkEnum.ordinal phase]? with
    | some (some factory) => phases := phases.push (some (← liftM (m := IO) (a.retrievePhase factory)))
    | _ => phases := phases.push none
  let mut processorConfiguration : LayoutProcessorConfiguration P F := {}
  for phase in phases do
    if let some phase := phase then
      if let some config ← phase.getLayoutProcessorConfiguration graph then
        processorConfiguration := processorConfiguration.addAll config
  processorConfiguration := processorConfiguration.addAll s.additionalProcessors
  let mut algorithm : Array (LayoutProcessor m G) := #[]
  for phase in variants do
    let before := processorConfiguration.processorsBefore phase
    algorithm := algorithm ++ (← liftM (m := IO) (a.retrieveProcessors before))
    if let some (some p) := phases[ElkEnum.ordinal phase]? then
      algorithm := algorithm.push (traced true p.toProcessor)
  if let some lastPhase := variants.back? then
    let after := processorConfiguration.processorsAfter lastPhase
    algorithm := algorithm ++ (← liftM (m := IO) (a.retrieveProcessors after))
  return algorithm

end AlgorithmAssembler

end Elk.Core.Alg
