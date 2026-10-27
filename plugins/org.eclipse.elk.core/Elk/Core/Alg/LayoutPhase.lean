import Elk.Core.Alg.LayoutProcessor
import Elk.Core.Alg.LayoutProcessorConfiguration
/-!
# `org.eclipse.elk.core.alg.ILayoutPhase` / `ILayoutPhaseFactory`
-/
namespace Elk.Core.Alg

open Elk.Core.Util

/-- `ILayoutPhase<P, G>`: a processor that also contributes a processor configuration. -/
structure LayoutPhase (m : Type → Type) (P G F : Type) where
  /-- Java simple class name. -/
  name : String
  /-- `process(graph, progressMonitor)`. -/
  process : G → ProgressMonitor → m Unit
  /-- `getLayoutProcessorConfiguration(graph)`. -/
  getLayoutProcessorConfiguration : G → m (Option (LayoutProcessorConfiguration P F))
  /-- `isHierarchyAware()`. -/
  isHierarchyAware : Bool := false

/-- `ILayoutPhaseFactory<P, G>`: an enum constant (`key` = Java enum class name × ordinal,
used as the phase cache key) that creates a phase. -/
structure LayoutPhaseFactory (m : Type → Type) (P G F : Type) where
  /-- Enum identity (`enum_type_id`, `enum_ordinal`); `none` disables caching for this factory. -/
  key : Option (String × Nat)
  /-- `create()`. -/
  create : IO (LayoutPhase m P G F)

/-- `LayoutPhaseFactory` for an `ElkEnum` constant. -/
def LayoutPhaseFactory.ofEnum {m : Type → Type} {P G F ε : Type} [ElkEnum ε]
    (enumName : String) (e : ε) (create : IO (LayoutPhase m P G F)) : LayoutPhaseFactory m P G F :=
  { key := some (enumName, ElkEnum.ordinal e), create := create }

/-- `ILayoutPhase.asProcessor`: the phase viewed as a plain processor. -/
def LayoutPhase.toProcessor {m : Type → Type} {P G F : Type} (phase : LayoutPhase m P G F) : LayoutProcessor m G :=
  { name := phase.name, process := phase.process, isHierarchyAware := phase.isHierarchyAware }

end Elk.Core.Alg
