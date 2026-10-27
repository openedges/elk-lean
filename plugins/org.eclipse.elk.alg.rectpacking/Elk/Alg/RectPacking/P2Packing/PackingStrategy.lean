import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.rectpacking.p2packing.PackingStrategy`

Port of the enumeration of `p2packing/packing_strategy.rs` (elk-rs), needed by the options. The
factory half (`create_phase`: `Compactor`, `SimplePlacement`, `NoPlacement`) belongs to the
packing phase port (F8b).
-/
namespace Elk.Alg.RectPacking.P2Packing

/-- `PackingStrategy`: `COMPACTION` (default), `SIMPLE`, `NONE`. -/
elk_enum PackingStrategy := compaction simple none

end Elk.Alg.RectPacking.P2Packing
