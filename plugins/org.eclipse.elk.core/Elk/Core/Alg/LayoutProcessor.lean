import Elk.Core.Util.ProgressMonitor
/-!
# `org.eclipse.elk.core.alg.ILayoutProcessor`

A processor is a closure over the algorithm's monad `m` that transforms the graph `G`
(an arena id for arena-based graph models).
-/
namespace Elk.Core.Alg

open Elk.Core.Util

/-- `ILayoutProcessor<G>`: `process(graph, progressMonitor)` plus the Java simple class name
(used by traces and the phase-step recorder). -/
structure LayoutProcessor (m : Type → Type) (G : Type) where
  /-- Java simple class name (e.g. `LongEdgeSplitter`). -/
  name : String
  /-- `process(graph, progressMonitor)`. -/
  process : G → ProgressMonitor → m Unit
  /-- `isHierarchyAware()` (Rust default `false`). -/
  isHierarchyAware : Bool := false

/-- `ILayoutProcessorFactory<G>`: creates a processor from an enum constant `F`
(`IntermediateProcessorStrategy` in layered). Creation runs in `IO` so tests can count it. -/
abbrev LayoutProcessorFactory (m : Type → Type) (G F : Type) := F → IO (LayoutProcessor m G)

end Elk.Core.Alg
