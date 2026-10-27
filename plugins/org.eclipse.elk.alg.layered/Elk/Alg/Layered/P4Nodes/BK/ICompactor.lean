import Elk.Alg.Layered.P4Nodes.BK.BKAlignedLayout
/-!
# `org.eclipse.elk.alg.layered.p4nodes.bk.ICompactor` (elk-rs `i_compactor.rs`)
-/
namespace Elk.Alg.Layered.P4Nodes.BK

/-- `ICompactor`: computes the actual coordinates of the blocks and their nodes. First, all
blocks are placed, trying to avoid any crossing of the blocks; then the blocks are shifted
towards each other if there is any space for compaction. The layout is passed by value and
returned updated (Rust `horizontal_compaction(&mut self, bal, ni)`). -/
structure ICompactor where
  /-- `horizontalCompaction(bal)`. -/
  horizontalCompaction : BKAlignedLayout → NeighborhoodInformation → IO BKAlignedLayout

end Elk.Alg.Layered.P4Nodes.BK
