import Elk.Alg.Layered.Intermediate.Loops.SelfHyperLoop
import Elk.Graph.ArrayModify
/-!
# `org.eclipse.elk.alg.layered.intermediate.loops.SelfLoopHolder`

Port of elk-rs `intermediate/loops/self_loop_holder.rs` (pure data; see `SelfLoopPort`). The
holder is stored by value in `LNodeInternals.selfLoopHolder` (`InternalProperties.SELF_LOOP_HOLDER`)
and owns the tables of all self-loop objects of its node:

- `slPorts` — the Rust `sl_ports: Vec<(LPortRef, SelfLoopPortRef)>` map. Entries are created in
  insertion order and never removed, so the table index *is* the map order and
  `slPortMap` (`(LPortId × SelfLoopPortId)` pairs) is derived from it;
- `slEdges` — every `SelfLoopEdge` (in creation order, i.e. the node's outgoing self loops);
- `slHyperLoops` — `sl_hyper_loops` in creation order.

The construction (`SelfLoopHolder::initialize`) is the pure `SelfLoopHolder.build`, which takes the
graph facts it reads as arguments; `Loops.Ops.SelfLoopHolder.install` gathers them from the arena.
-/
namespace Elk.Alg.Layered.Intermediate.Loops

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph

/-- `SelfLoopHolder`: holds the self loop data of one node. -/
structure SelfLoopHolder where
  /-- `getLNode()`. -/
  lNode : LNodeId
  /-- `getSLHyperLoops()` (index = `SelfHyperLoopId`). -/
  slHyperLoops : Array SelfHyperLoop := #[]
  /-- The self-loop ports (index = `SelfLoopPortId`, insertion order of `getSLPortMap()`). -/
  slPorts : Array SelfLoopPort := #[]
  /-- The self-loop edges (index = `SelfLoopEdgeId`). -/
  slEdges : Array SelfLoopEdge := #[]
  /-- `arePortsHidden()` / `setPortsHidden(hidden)`. -/
  arePortsHidden : Bool := false
  /-- `getRoutingSlotCount()` per `PortSide` ordinal. -/
  routingSlotCount : Array Int := Array.replicate PORT_SIDE_COUNT 0
  deriving Inhabited, Repr

namespace SelfLoopHolder

/-- The self-loop port with index `p`. -/
@[inline] def slPort (h : SelfLoopHolder) (p : SelfLoopPortId) : SelfLoopPort := h.slPorts[p.idx]!
/-- The self-loop edge with index `e`. -/
@[inline] def slEdge (h : SelfLoopHolder) (e : SelfLoopEdgeId) : SelfLoopEdge := h.slEdges[e.idx]!
/-- The hyper loop with index `l`. -/
@[inline] def slHyperLoop (h : SelfLoopHolder) (l : SelfHyperLoopId) : SelfHyperLoop := h.slHyperLoops[l.idx]!

@[inline] def modifySLPort (h : SelfLoopHolder) (p : SelfLoopPortId) (f : SelfLoopPort → SelfLoopPort) : SelfLoopHolder :=
  { h with slPorts := h.slPorts.modifyIn p.idx f }
@[inline] def modifySLEdge (h : SelfLoopHolder) (e : SelfLoopEdgeId) (f : SelfLoopEdge → SelfLoopEdge) : SelfLoopHolder :=
  { h with slEdges := h.slEdges.modifyIn e.idx f }
@[inline] def modifySLHyperLoop (h : SelfLoopHolder) (l : SelfHyperLoopId) (f : SelfHyperLoop → SelfHyperLoop) : SelfLoopHolder :=
  { h with slHyperLoops := h.slHyperLoops.modifyIn l.idx f }

/-- The ids of all hyper loops (in `slHyperLoops` order). -/
def hyperLoopIds (h : SelfLoopHolder) : Array SelfHyperLoopId :=
  (Array.range h.slHyperLoops.size).map (⟨·⟩)

/-- `sl_port_values()`: the self-loop ports in map order. -/
def slPortValues (h : SelfLoopHolder) : Array SelfLoopPortId :=
  (Array.range h.slPorts.size).map (⟨·⟩)

/-- `getSLPortMap()` / `sl_port_map()`: `LPort` → self-loop port, insertion order. -/
def slPortMap (h : SelfLoopHolder) : Array (LPortId × SelfLoopPortId) :=
  (Array.range h.slPorts.size).map fun i => ((h.slPorts[i]!).lPort, ⟨i⟩)

/-- Map lookup `getSLPortMap().get(lPort)`. -/
def slPortOf? (h : SelfLoopHolder) (lPort : LPortId) : Option SelfLoopPortId :=
  (h.slPorts.findIdx? (·.lPort == lPort)).map (⟨·⟩)

/-- `getLPort()` of a self-loop port. -/
@[inline] def lPortOf (h : SelfLoopHolder) (p : SelfLoopPortId) : LPortId := (h.slPort p).lPort

/-- `all_self_loop_edges()`: the `LEdge`s of all hyper loops (loop order, then edge order). -/
def allSelfLoopEdges (h : SelfLoopHolder) : Array LEdgeId :=
  h.slHyperLoops.foldl (fun acc l => acc ++ l.slEdges.map fun e => (h.slEdge e).lEdge) #[]

/-- `self_loop_port_for(holder, lPort)`: the existing self-loop port of `lPort`, or a new one
appended to the map (`SelfLoopPort::new`; `hadOnlySelfLoops` is the precomputed flag). -/
def selfLoopPortFor (h : SelfLoopHolder) (lPort : LPortId) (hadOnlySelfLoops : Bool) : SelfLoopHolder × SelfLoopPortId :=
  match h.slPortOf? lPort with
  | some p => (h, p)
  | none =>
    let id : SelfLoopPortId := ⟨h.slPorts.size⟩
    ({ h with slPorts := h.slPorts.push { lPort := lPort, hadOnlySelfLoops := hadOnlySelfLoops } }, id)

/-- `SelfLoopEdge::new(lEdge, slSource, slTarget)`: creates the edge and appends it to the
source's outgoing and then the target's incoming self-loop edges. -/
def addSLEdge (h : SelfLoopHolder) (lEdge : LEdgeId) (slSource slTarget : SelfLoopPortId) : SelfLoopHolder × SelfLoopEdgeId :=
  let id : SelfLoopEdgeId := ⟨h.slEdges.size⟩
  let h := { h with slEdges := h.slEdges.push { lEdge := lEdge, slSource := slSource, slTarget := slTarget } }
  let h := h.modifySLPort slSource fun p => { p with outgoingSLEdges := p.outgoingSLEdges.push id }
  let h := h.modifySLPort slTarget fun p => { p with incomingSLEdges := p.incomingSLEdges.push id }
  (h, id)

/-- `SelfHyperLoop::add_self_loop_edge(loop, slEdge)` on the loop `loop` of the holder (the loop
need not be in `slHyperLoops` yet, hence the explicit value and id): ignores edges already in
the loop, sets the edge's hyper loop, adds the end ports (source, then target) and the edge's
labels (`labelsOf` = `LEdge.getLabels()`, `sizeOf` = label sizes). -/
def addSelfLoopEdgeToLoop (h : SelfLoopHolder) (loop : SelfHyperLoop) (loopId : SelfHyperLoopId)
    (e : SelfLoopEdgeId) (labelsOf : LEdgeId → Array LLabelId) (sizeOf : LLabelId → KVector) :
    SelfLoopHolder × SelfHyperLoop := Id.run do
  if loop.slEdges.contains e then return (h, loop)
  let h := h.modifySLEdge e (·.setSLHyperLoop loopId)
  let edge := h.slEdge e
  let mut loop := { loop with slEdges := loop.slEdges.push e }
  if !loop.slPorts.contains edge.slSource then loop := { loop with slPorts := loop.slPorts.push edge.slSource }
  if !loop.slPorts.contains edge.slTarget then loop := { loop with slPorts := loop.slPorts.push edge.slTarget }
  let labels := labelsOf edge.lEdge
  if !labels.isEmpty then
    let current := loop.slLabels.getD {}
    loop := { loop with slLabels := some (current.addLLabels labels sizeOf) }
  return (h, loop)

/-- `initialize_hyper_loop(startPort, visited)`: breadth-first search over the self-loop edges
(outgoing, then incoming of each dequeued port) collecting one hyper loop. Returns the loop
(id `loopId`, not yet appended) and the updated visited flags (by `SelfLoopPortId`). -/
def initializeHyperLoop (h : SelfLoopHolder) (start : SelfLoopPortId) (loopId : SelfHyperLoopId)
    (visited : Array Bool) (labelsOf : LEdgeId → Array LLabelId) (sizeOf : LLabelId → KVector) :
    SelfLoopHolder × SelfHyperLoop × Array Bool := Id.run do
  let mut h := h
  let mut loop : SelfHyperLoop := {}
  let mut visited := visited.set! start.idx true
  let mut queue : Array SelfLoopPortId := #[start]
  let mut head := 0
  -- every port enters the queue at most once, so `slPorts.size + 1` rounds suffice
  for _ in [0:h.slPorts.size + 1] do
    if head ≥ queue.size then break
    let current := queue[head]!
    head := head + 1
    let port := h.slPort current
    for e in port.outgoingSLEdges ++ port.incomingSLEdges do
      let (h', loop') := h.addSelfLoopEdgeToLoop loop loopId e labelsOf sizeOf
      h := h'
      loop := loop'
      let edge := h.slEdge e
      if !visited[edge.slSource.idx]! then
        visited := visited.set! edge.slSource.idx true
        queue := queue.push edge.slSource
      if !visited[edge.slTarget.idx]! then
        visited := visited.set! edge.slTarget.idx true
        queue := queue.push edge.slTarget
  return (h, loop, visited)

/-- `SelfLoopHolder::new(node)` + `initialize(holder)`.

* `selfLoops`: the node's outgoing self loops (`LNode.getOutgoingEdges()` order, edges with both
  ends) as `(edge, source port, target port)`;
* `hadOnlySelfLoops lPort`: `SelfLoopPort::new`'s flag (≥ 1 connected edge, all self loops);
* `labelsOf`, `sizeOf`: edge labels and label sizes.

Creates the self-loop ports/edges in edge order (source port before target port), then groups
the edges into hyper loops by a BFS started from every not yet visited port in map order. -/
def build (lNode : LNodeId) (selfLoops : Array (LEdgeId × LPortId × LPortId)) (hadOnlySelfLoops : LPortId → Bool)
    (labelsOf : LEdgeId → Array LLabelId) (sizeOf : LLabelId → KVector) : SelfLoopHolder := Id.run do
  let mut h : SelfLoopHolder := { lNode := lNode }
  for (edge, source, target) in selfLoops do
    let (h1, slSource) := h.selfLoopPortFor source (hadOnlySelfLoops source)
    let (h2, slTarget) := h1.selfLoopPortFor target (hadOnlySelfLoops target)
    let (h3, _) := h2.addSLEdge edge slSource slTarget
    h := h3
  let mut visited : Array Bool := Array.replicate h.slPorts.size false
  for p in h.slPortValues do
    if visited[p.idx]! then continue
    let loopId : SelfHyperLoopId := ⟨h.slHyperLoops.size⟩
    let (h', loop, visited') := h.initializeHyperLoop p loopId visited labelsOf sizeOf
    visited := visited'
    h := { h' with slHyperLoops := h'.slHyperLoops.push loop }
  return h

end SelfLoopHolder

end Elk.Alg.Layered.Intermediate.Loops
