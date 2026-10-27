import Elk.Alg.Layered.Intermediate.Loops.SelfLoopPort
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.SelfLoopEdge`

Port of elk-rs `intermediate/loops/self_loop_edge.rs` (pure data; see `SelfLoopPort`).
`SelfLoopEdge::new` (which also registers the edge with its end ports) is
`SelfLoopHolder.addSLEdge` because the ports live in the holder's table.
-/
namespace Elk.Alg.Layered.Intermediate.Loops

open Elk.Alg.Layered.Graph

/-- `SelfLoopEdge`: represents a single self loop edge. -/
structure SelfLoopEdge where
  /-- `getLEdge()`. -/
  lEdge : LEdgeId
  /-- `getSLHyperLoop()`: the hyper loop the edge belongs to (Rust `Weak`, set once). -/
  slHyperLoop : Option SelfHyperLoopId := none
  /-- `getSLSource()`. -/
  slSource : SelfLoopPortId
  /-- `getSLTarget()`. -/
  slTarget : SelfLoopPortId
  deriving Inhabited, Repr

namespace SelfLoopEdge

/-- `setSLHyperLoop(slLoop)`: Rust only sets the loop when none is set yet. -/
def setSLHyperLoop (e : SelfLoopEdge) (slLoop : SelfHyperLoopId) : SelfLoopEdge :=
  if e.slHyperLoop.isNone then { e with slHyperLoop := some slLoop } else e

end SelfLoopEdge

end Elk.Alg.Layered.Intermediate.Loops
