import Elk.Alg.Common.Compaction.OneD.CGraph
/-!
# `org.eclipse.elk.alg.common.compaction.oned.ISpacingsHandler`

Strategy for the spacing between two `CNode`s (elk-rs `i_spacings_handler.rs`), as a structure
of closures (PORTING.md §14). The closures receive the current `CGraph` so that they can
inspect the nodes (Rust passes the `CNodeRef`s). The Rust tuple implementation
`(FH, FV)` corresponds to `SpacingsHandler.mk horizontal vertical`.
-/
namespace Elk.Alg.Common.Compaction.OneD

/-- `ISpacingsHandler`. -/
structure SpacingsHandler where
  /-- `getHorizontalSpacing(cNode1, cNode2)`. -/
  horizontal : CGraph → CNodeId → CNodeId → Float
  /-- `getVerticalSpacing(cNode1, cNode2)`. -/
  vertical : CGraph → CNodeId → CNodeId → Float

namespace SpacingsHandler

/-- `DefaultSpacingsHandler` (Java `ISpacingsHandler.DEFAULT_SPACING_HANDLER`): spacing `0.0`
in both dimensions. -/
def default : SpacingsHandler := ⟨fun _ _ _ => 0.0, fun _ _ _ => 0.0⟩

instance : Inhabited SpacingsHandler := ⟨default⟩

end SpacingsHandler

end Elk.Alg.Common.Compaction.OneD
