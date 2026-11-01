import Elk.Alg.Common.Compaction.OneD.CGraph
/-!
# `org.eclipse.elk.alg.common.compaction.oned.ILockFunction`

Decides whether a `CNode` is locked in a direction (elk-rs `i_lock_function.rs`). Two forms:

* `fn f`: a closure that receives the current `CGraph` (the Rust closure inspects the `CNodeRef` at
  call time), e.g. `HorizontalGraphCompactor`'s locks;
* `flags locked`: a lock fixed per node, `isLocked(node, _) = locked[node]` (unlocked out of range),
  which reads neither the graph nor the direction (the components compaction's frozen reposition
  flags). The compaction algorithms may evaluate it without building a graph value and may hoist
  it out of loops that do not change the nodes it is asked about.
-/
namespace Elk.Alg.Common.Compaction.OneD

open Elk.Core.Options

/-- `ILockFunction`. -/
inductive LockFunction where
  /-- A lock function reading the current graph (`ILockFunction.isLocked(node, direction)`). -/
  | fn (f : CGraph → CNodeId → Direction → Bool)
  /-- A lock per node: `isLocked(node, _) = locked[node.idx]` (`false` out of range). -/
  | flags (locked : Array Bool)

instance : Inhabited LockFunction := ⟨.flags #[]⟩

namespace LockFunction

/-- `ILockFunction.isLocked(node, direction)` on the current graph `g`. -/
@[inline] def isLocked (lf : LockFunction) (g : CGraph) (n : CNodeId) (d : Direction) : Bool :=
  match lf with
  | .fn f => f g n d
  | .flags locked => locked[n.idx]?.getD false

end LockFunction

end Elk.Alg.Common.Compaction.OneD
