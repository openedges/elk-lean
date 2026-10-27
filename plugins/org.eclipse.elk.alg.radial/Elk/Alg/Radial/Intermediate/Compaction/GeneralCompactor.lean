import Elk.Graph
import Elk.Core.Alg
import Elk.Core.Exceptions
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.Radial.InternalProperties
import Elk.Alg.Radial.Options.CompactionStrategy
import Elk.Alg.Radial.Options.RadialOptions
import Elk.Alg.Radial.Intermediate.Compaction.IRadialCompactor
import Elk.Alg.Radial.Intermediate.Compaction.RadialCompaction
import Elk.Alg.Radial.Intermediate.Compaction.AnnulusWedgeCompaction
/-!
# `org.eclipse.elk.alg.radial.intermediate.compaction.GeneralCompactor`

Port of `general_compactor.rs` (elk-rs): the processor that runs the compactor chosen by
`COMPACTOR`. This module also hosts `CompactionStrategy.create`, the factory half of the Rust
`compaction_strategy.rs`.
-/
namespace Elk.Alg.Radial.Intermediate.Compaction

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Radial.Options

/-- `CompactionStrategy::create()`; `NONE` has no implementation (Rust `panic!`, Java
`IllegalArgumentException`). -/
def createCompactor : CompactionStrategy → RadialM IRadialCompactor
  | .radialCompaction => pure RadialCompaction.compactor
  | .wedgeCompaction => pure AnnulusWedgeCompaction.compactor
  | .none => throwIllegalArgument "No implementation is available for the layout option NONE"

namespace GeneralCompactor

/-- `process(graph, progress_monitor)`. -/
def process (graph : NodeId) (monitor : ProgressMonitor) : RadialM Unit := do
  let _ ← monitor.begin "General Compactor" 1.0
  if ← monitor.isLoggingEnabled then monitor.logGraph "Before"
  let compactor := ((← ElkM.getNode graph).props.get RadialOptions.COMPACTOR).getD CompactionStrategy.none
  let c ← createCompactor compactor
  c.compact graph
  if ← monitor.isLoggingEnabled then monitor.logGraph "After"

/-- The processor (`ILayoutProcessor`). -/
def processor : LayoutProcessor RadialM NodeId :=
  { name := "GeneralCompactor", process := process }

end GeneralCompactor

end Elk.Alg.Radial.Intermediate.Compaction
