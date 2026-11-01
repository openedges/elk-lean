import Elk.Alg.Common.Compaction.OneD.ISpacingsHandler
import Elk.Alg.Common.Compaction.OneD.ILockFunction
/-!
# `org.eclipse.elk.alg.common.compaction.oned.ICompactionAlgorithm`

A compaction strategy (elk-rs `i_compaction_algorithm.rs`) receives the
`OneDimensionalCompactor` mutably. A Lean structure cannot contain closures over a monad whose
state is that same structure (non-positive occurrence), so the compactor is split:

* `CompactorState` — the part of `OneDimensionalCompactor` the strategies see and change:
  `cGraph`, `lockFun`, `spacingsHandler`, `direction` (the Rust `pub` fields);
* `OneDimensionalCompactor` (module `OneDimensionalCompactor`) extends it with the two
  strategy objects and the `finished` flag (the Rust private fields).

Strategies run in `CompactM := StateRefT CompactorState IO`. This mirrors the Rust code, which
moves the running strategy out of the compactor (`std::mem::replace`) while it executes.

This module also provides the `CompactM` accessors used by the strategies (`getCNode`,
`modifyCNode`, …) and `isLockedNode` / `isLockedGroup` (Rust
`OneDimensionalCompactor::is_locked_node` / `is_locked_group`).
-/
namespace Elk.Alg.Common.Compaction.OneD

open Elk.Core.Options

/-- The strategy-visible part of `OneDimensionalCompactor`. -/
structure CompactorState where
  /-- `OneDimensionalCompactor.cGraph`. -/
  cGraph : CGraph
  /-- `OneDimensionalCompactor.lockFun` (`None` = nothing is locked). -/
  lockFun : Option LockFunction := none
  /-- `OneDimensionalCompactor.spacingsHandler`. -/
  spacingsHandler : SpacingsHandler := SpacingsHandler.default
  /-- `OneDimensionalCompactor.direction` (current compaction direction). -/
  direction : Direction := .undefined
  deriving Inhabited

/-- Monad of the compaction / constraint calculation strategies. -/
abbrev CompactM := StateRefT CompactorState IO

namespace CompactorState

/-- `OneDimensionalCompactor::is_locked_node(node, direction)`. -/
def isLockedNode (s : CompactorState) (node : CNodeId) (direction : Direction) : Bool :=
  match s.lockFun with
  | some f => f.isLocked s.cGraph node direction
  | none => false

/-- `OneDimensionalCompactor::is_locked_group(group, direction)`: some node of the group is
locked. -/
def isLockedGroup (s : CompactorState) (group : CGroupId) (direction : Direction) : Bool :=
  (s.cGraph.cGroup group).cNodes.any fun n => s.isLockedNode n direction

end CompactorState

namespace CompactM

/-- Reads a node (copy). -/
@[inline] def getCNode (n : CNodeId) : CompactM CNode := return (← get).cGraph.cNode n

/-- Reads a group (copy). -/
@[inline] def getCGroup (c : CGroupId) : CompactM CGroup := return (← get).cGraph.cGroup c

/-- Updates a node in place. -/
@[inline] def modifyCNode (n : CNodeId) (f : CNode → CNode) : CompactM Unit :=
  modify fun s => { s with cGraph := s.cGraph.modifyCNode n f }

/-- Updates a group in place. -/
@[inline] def modifyCGroup (c : CGroupId) (f : CGroup → CGroup) : CompactM Unit :=
  modify fun s => { s with cGraph := s.cGraph.modifyCGroup c f }

/-- Ids of all nodes (Rust `compactor.c_graph.borrow().c_nodes.clone()`). -/
@[inline] def cNodeIds : CompactM (Array CNodeId) := return (← get).cGraph.cNodeIds

/-- Ids of all groups (Rust `compactor.c_graph.borrow().c_groups.clone()`). -/
@[inline] def cGroupIds : CompactM (Array CGroupId) := return (← get).cGraph.cGroupIds

/-- The current compaction direction. -/
@[inline] def direction : CompactM Direction := return (← get).direction

/-- `isLockedNode` evaluated on the current state. -/
@[inline] def isLockedNode (n : CNodeId) (d : Direction) : CompactM Bool :=
  return (← get).isLockedNode n d

/-- `isLockedGroup` evaluated on the current state. -/
@[inline] def isLockedGroup (c : CGroupId) (d : Direction) : CompactM Bool :=
  return (← get).isLockedGroup c d

/-- `spacingsHandler.getHorizontalSpacing(n1, n2)` on the current graph. -/
@[inline] def horizontalSpacing (n1 n2 : CNodeId) : CompactM Float := do
  let s ← get
  -- one `return` per handler form: a closure's (boxed) result is passed on without unboxing and
  -- boxing it again after a join
  match s.spacingsHandler with
  | .mk h _ => return h s.cGraph n1 n2
  | .individualMin sp d => return Elk.Core.Util.fmin (SpacingsHandler.individualOf sp d n1) (SpacingsHandler.individualOf sp d n2)

/-- `spacingsHandler.getVerticalSpacing(n1, n2)` on the current graph. -/
@[inline] def verticalSpacing (n1 n2 : CNodeId) : CompactM Float := do
  let s ← get
  match s.spacingsHandler with
  | .mk _ v => return v s.cGraph n1 n2
  | .individualMin sp d => return Elk.Core.Util.fmin (SpacingsHandler.individualOf sp d n1) (SpacingsHandler.individualOf sp d n2)

end CompactM

/-- `ICompactionAlgorithm.compact(compactor)`. -/
structure CompactionAlgorithm where
  /-- Compacts `cGraph` in the current `direction`. -/
  compact : CompactM Unit

end Elk.Alg.Common.Compaction.OneD
