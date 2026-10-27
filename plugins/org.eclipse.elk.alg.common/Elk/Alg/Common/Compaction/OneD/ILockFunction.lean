import Elk.Alg.Common.Compaction.OneD.CGraph
/-!
# `org.eclipse.elk.alg.common.compaction.oned.ILockFunction`

Decides whether a `CNode` is locked in a direction (elk-rs `i_lock_function.rs`). A closure
that receives the current `CGraph` (the Rust closure inspects the `CNodeRef` at call time).
-/
namespace Elk.Alg.Common.Compaction.OneD

open Elk.Core.Options

/-- `ILockFunction.isLocked(node, direction)`. -/
abbrev LockFunction := CGraph → CNodeId → Direction → Bool

end Elk.Alg.Common.Compaction.OneD
