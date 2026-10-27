import Elk.Core.Math
import Elk.Core.Options
import Elk.Alg.Layered.Graph.Ids
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.SelfLoopPort`

Port of elk-rs `intermediate/loops/self_loop_port.rs`. Pure data: the self-loop model is stored
by value in `LNodeInternals.selfLoopHolder`, so this file sits below `InternalProperties` in the
import graph and must not import the layered graph model.

The Rust `Arc<Mutex<_>>` references between the self-loop objects become indices into the
holder-local arrays (`SelfLoopHolder.slPorts`, `.slEdges`, `.slHyperLoops`); the typed index
structures of all three tables are declared here (the lowest file of the package).
-/
namespace Elk.Alg.Layered.Intermediate.Loops

open Elk.Alg.Layered.Graph

/-- Index of a `SelfLoopPort` in `SelfLoopHolder.slPorts` (replaces `SelfLoopPortRef`;
`Arc::ptr_eq` → `==`). -/
structure SelfLoopPortId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of a `SelfLoopEdge` in `SelfLoopHolder.slEdges` (replaces `SelfLoopEdgeRef`). -/
structure SelfLoopEdgeId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of a `SelfHyperLoop` in `SelfLoopHolder.slHyperLoops` (replaces `SelfHyperLoopRef`). -/
structure SelfHyperLoopId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

instance : ToString SelfLoopPortId := ⟨fun i => s!"SLP{i.idx}"⟩
instance : ToString SelfLoopEdgeId := ⟨fun i => s!"SLE{i.idx}"⟩
instance : ToString SelfHyperLoopId := ⟨fun i => s!"SHL{i.idx}"⟩

/-- `SelfLoopPort`: a port which is an end point of at least one self loop. -/
structure SelfLoopPort where
  /-- `getLPort()`: the layered port this self-loop port represents. -/
  lPort : LPortId
  /-- `hadOnlySelfLoops()`: whether the port had at least one connected edge and all of them
  were self loops when the holder was created (computed by `SelfLoopPort::new`). -/
  hadOnlySelfLoops : Bool := false
  /-- `getIncomingSLEdges()`. -/
  incomingSLEdges : Array SelfLoopEdgeId := #[]
  /-- `getOutgoingSLEdges()`. -/
  outgoingSLEdges : Array SelfLoopEdgeId := #[]
  /-- `isHidden()` / `setHidden(hidden)`. -/
  isHidden : Bool := false
  deriving Inhabited, Repr

namespace SelfLoopPort

/-- `getSLNetFlow()` (Rust `sl_net_flow`): incoming minus outgoing self-loop edges. -/
def slNetFlow (p : SelfLoopPort) : Int :=
  (p.incomingSLEdges.size : Int) - (p.outgoingSLEdges.size : Int)

end SelfLoopPort

end Elk.Alg.Layered.Intermediate.Loops
