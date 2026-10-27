import Elk.Alg.Layered.Graph.Monad
import Elk.Alg.Layered.Intermediate.Loops.SelfLoopHolder
/-!
# Arena operations of the self-loop model (`intermediate.loops`)

The methods of `SelfLoopHolder`, `SelfLoopPort`, `SelfHyperLoop` and `SelfHyperLoopLabels` that
read or write the layered graph (elk-rs `self_loop_holder.rs`, `self_hyper_loop.rs`,
`self_hyper_loop_labels.rs`). The data modules cannot import the graph model (the holder is a
field of `LNodeInternals`), so these live here: pure readers take the `LGraphArena`, writers run
in `LayeredM`. The holder itself is read with `SelfLoopHolder.get?` and written back with
`SelfLoopHolder.update` (a `modifyNode` on the owning node).
-/
namespace Elk.Alg.Layered.Intermediate.Loops

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace SelfLoopHolder

/-- `node.getProperty(InternalProperties.SELF_LOOP_HOLDER)`. -/
@[inline] def get? (n : LNodeId) : LayeredM (Option SelfLoopHolder) := do
  return (← getNode n).internal.selfLoopHolder

/-- `node.setProperty(InternalProperties.SELF_LOOP_HOLDER, holder)`. -/
@[inline] def store (n : LNodeId) (h : Option SelfLoopHolder) : LayeredM Unit :=
  modifyNode n fun x => { x with internal := { x.internal with selfLoopHolder := h } }

/-- Applies `f` to the holder stored on `n` (no-op without holder). -/
@[inline] def update (n : LNodeId) (f : SelfLoopHolder → SelfLoopHolder) : LayeredM Unit :=
  modifyNode n fun x => { x with internal := { x.internal with selfLoopHolder := x.internal.selfLoopHolder.map f } }

/-- `needs_self_loop_processing(node)`: a normal node with at least one outgoing self loop. -/
def needsSelfLoopProcessing (a : LGraphArena) (n : LNodeId) : Bool :=
  (a.node n).type == .normal && (a.nodeOutgoingEdges n).any (a.edgeIsSelfLoop ·)

/-- The `had_only_self_loops` flag of `SelfLoopPort::new(lPort)`: at least one connected edge and
all connected edges are self loops. -/
def portHadOnlySelfLoops (a : LGraphArena) (p : LPortId) : Bool :=
  let connected := (a.port p).connectedEdges
  !connected.isEmpty && connected.all (a.edgeIsSelfLoop ·)

/-- `SelfLoopHolder::new(node)` + `initialize`: the holder built from the node's outgoing self
loops (`LNode.getOutgoingEdges()` order; loops without both ends are skipped). -/
def create (a : LGraphArena) (n : LNodeId) : SelfLoopHolder :=
  let selfLoops := (a.nodeOutgoingEdges n).filterMap fun e =>
    if !a.edgeIsSelfLoop e then none
    else
      let ed := a.edge e
      match ed.source, ed.target with
      | some s, some t => some (e, s, t)
      | _, _ => none
  SelfLoopHolder.build n selfLoops (portHadOnlySelfLoops a) (fun e => (a.edge e).labels) (fun l => (a.label l).size)

/-- `install(node)`: creates the holder and stores it as `SELF_LOOP_HOLDER` on the node. Throws
(Rust `assert!`) when the node does not need self-loop processing. -/
def install (n : LNodeId) : LayeredM SelfLoopHolder := do
  if !(← withArena (needsSelfLoopProcessing · n)) then
    throw (IO.userError "java.lang.IllegalStateException: assertion failed: SelfLoopHolder::needs_self_loop_processing(node)")
  let h ← withArena (create · n)
  store n (some h)
  return h

/-- `sl_port_side(slPort)`: the side of the self-loop port's `LPort`. -/
@[inline] def portSide (a : LGraphArena) (h : SelfLoopHolder) (p : SelfLoopPortId) : PortSide :=
  (a.port (h.lPortOf p)).side

/-- `SelfHyperLoop::port_id(slPort)`: the `LPort.id` of the self-loop port. -/
@[inline] def portId (a : LGraphArena) (h : SelfLoopHolder) (p : SelfLoopPortId) : Int :=
  (a.port (h.lPortOf p)).id

/-- `sl_port_net_flow(slPort)` (elk-rs `self_loop_port_restorer.rs`): `LPort.getNetFlow()` of the
self-loop port's `LPort` (its current, non-hidden edges). -/
@[inline] def portNetFlow (a : LGraphArena) (h : SelfLoopHolder) (p : SelfLoopPortId) : Int :=
  (a.port (h.lPortOf p)).netFlow

/-- `SelfHyperLoop.compute_ports_per_side()` for hyper loop `l` (current `LPort` sides). -/
def computePortsPerSide (a : LGraphArena) (h : SelfLoopHolder) (l : SelfHyperLoopId) : SelfLoopHolder :=
  h.modifySLHyperLoop l (·.computePortsPerSide (portSide a h))

/-- `SelfHyperLoop.sort_ports_by_id()` for hyper loop `l` (stable, by `LPort.id`). -/
def sortPortsById (a : LGraphArena) (h : SelfLoopHolder) (l : SelfHyperLoopId) : SelfLoopHolder :=
  h.modifySLHyperLoop l (·.sortPortsById (portId a h))

/-- `loop_port_sides(slLoop)` (elk-rs `self_loop_port_restorer.rs`): the distinct defined sides
of the loop's ports in `slPorts` order. -/
def loopPortSides (a : LGraphArena) (h : SelfLoopHolder) (l : SelfHyperLoopId) : Array PortSide := Id.run do
  let mut sides : Array PortSide := #[]
  for p in (h.slHyperLoop l).slPorts do
    let side := portSide a h p
    if side != .undefined && !sides.contains side then sides := sides.push side
  return sides

/-- `SelfHyperLoopLabels.applyPlacement(offset)` for the labels of hyper loop `l`: writes the
computed positions to the arena labels (no-op without labels). -/
def applyLabelPlacement (h : SelfLoopHolder) (l : SelfHyperLoopId) (offset : KVector) : LayeredM Unit := do
  let some labels := (h.slHyperLoop l).slLabels | return
  let positions ← withArena fun a => labels.placement offset (fun lb => (a.label lb).size)
  for (lb, pos) in positions do
    modifyLabel lb fun x => { x with position := pos }

end SelfLoopHolder

end Elk.Alg.Layered.Intermediate.Loops
