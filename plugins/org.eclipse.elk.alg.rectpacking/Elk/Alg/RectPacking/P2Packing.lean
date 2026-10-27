import Elk.Alg.RectPacking.P2Packing.PackingStrategy
import Elk.Alg.RectPacking.P2Packing.InitialPlacement
import Elk.Alg.RectPacking.P2Packing.Compaction
import Elk.Alg.RectPacking.P2Packing.RowFillingAndCompaction
import Elk.Alg.RectPacking.P2Packing.Compactor
import Elk.Alg.RectPacking.P2Packing.SimplePlacement
import Elk.Alg.RectPacking.P2Packing.NoPlacement
/-!
# Packing package (`org.eclipse.elk.alg.rectpacking.p2packing`)

Aggregates the phase-2 modules and defines the factory half of `PackingStrategy` (Rust
`impl ILayoutPhaseFactory for PackingStrategy`), which cannot live next to the enumeration because
the options depend on the enumeration and the phases on the options.
-/
namespace Elk.Alg.RectPacking.P2Packing

open Elk.Core.Alg Elk.Alg.RectPacking

namespace PackingStrategy

/-- `create_phase()`: `COMPACTION` → `Compactor`, `SIMPLE` → `SimplePlacement`, `NONE` →
`NoPlacement`. -/
def createPhase : PackingStrategy → RectPackingPhase
  | .compaction => Compactor.phase
  | .simple => SimplePlacement.phase
  | .none => NoPlacement.phase

/-- `PackingStrategy` as `ILayoutPhaseFactory` (cached by enum identity). -/
def phaseFactory (s : PackingStrategy) : RectPackingPhaseFactory :=
  LayoutPhaseFactory.ofEnum "PackingStrategy" s (pure (createPhase s))

end PackingStrategy

end Elk.Alg.RectPacking.P2Packing
