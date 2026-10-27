import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.P3Order.CrossMinSnapshot
import Elk.Alg.Layered.P3Order.ISweepPortDistributor
import Elk.Alg.Layered.P3Order.Counting.BinaryIndexedTree
import Elk.Core.Util.Sort
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.layered.p3order.AbstractBarycenterPortDistributor`

Port ranks and barycenter port distribution (elk-rs `abstract_barycenter_port_distributor.rs`).
The two concrete rank strategies of Java's subclasses (`NodeRelativePortDistributor`,
`LayerTotalPortDistributor`) are selected by `PortRankStrategy`, like in elk-rs.

State: the mutable Rust fields (`port_ranks`, `node_positions`, `port_barycenter`, `n_ports`)
form one `BarycenterPortDistributorState` behind an `IO.Ref`; the scratch fields
(`min_barycenter`, `max_barycenter`, `in_layer_ports`, the partition buffers) are locals.
Ranks and barycenters are indexed by port id (`LPort.id` as assigned by the `IInitializable`s,
or the snapshot's captured id), node positions by `[layer index][node id]`.

Two code paths, as in elk-rs:
- **snapshot path** (a `CrossMinSnapshot` was handed over with `setSnapshot`; the
  `GraphInfoHolder` does this through the barycenter heuristic): ids, port sides, edge
  end points, owner layers and the *port order captured when the snapshot was built* are read
  from the snapshot. In particular `distributePorts` partitions the captured port order.
  Rust's `distribute_ports` takes the snapshot out of `self.snapshot` while it runs, so the
  helpers it calls that test `self.snapshot` run their lock fallbacks: `sort_ports` sorts the
  *current* port order (index tie-break, `sortPortsLock`; `sort_ports_snap`/`sortPortsSnap` is
  unreachable from there) and `deal_with_north_south_ports` reads the live dummy ports.
  Ranks iterate the node's current ports mapped to captured ids.
- **lock path** (no snapshot): everything is read from the live arena; ties keep the current
  port order.
The `PORT_CONSTRAINTS`/`PORT_DUMMY`/`ORIGIN` reads (elk-rs `ArenaSync` or lock) read the arena.
Rust's unreachable snapshot branches of the lock-only helpers (`iterate_ports_snap`, the
snapshot checks in `calculate_in_layer_ports_barycenter_values` and
`position_of_node_port_owner_in_layer`) are not ported.

Numerics follow Rust: ranks and the rank sum are computed in `f64` and stored rounded to
`f32` (`f32t`; Java computes in `float`), barycenter sums and the in-layer values use `f32`
arithmetic (every operation rounded with `Float.toF32`), `min`/`max` are `f64::min/max`.
The `ELK_TRACE` timing and port-rank dumps are not reproduced. Port ids beyond `u32` (wrapped
negative ids) never grow the arrays (Rust would abort).
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Graph Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open Elk.Alg.Layered.P3Order.Counting LayeredM

/-- elk-rs `PortRankStrategy`: the rank computation of the concrete distributor. -/
inductive PortRankStrategy where
  /-- `NodeRelativePortDistributor`: every node consumes rank `1`. -/
  | nodeRelative
  /-- `LayerTotalPortDistributor`: every port consumes rank `1`. -/
  | layerTotal
  deriving BEq, Repr, Inhabited

/-- The mutable fields of `AbstractBarycenterPortDistributor`. -/
structure BarycenterPortDistributorState where
  /-- `port_ranks` (by port id, `f32` values). -/
  portRanks : Array Float := #[]
  /-- `node_positions[layer][node id]`: position of the node in the layer. -/
  nodePositions : Array (Array Nat) := #[]
  /-- `port_barycenter` (by port id, `f32` values). -/
  portBarycenter : Array Float := #[]
  /-- `n_ports`: the next port id handed out by `initAtPortLevel`. -/
  nPorts : Nat := 0
  deriving Inhabited

namespace BarycenterPortDistributorState

/-- Rust `f32t`: `v as f32 as f64` (Java `float[]` storage). -/
@[inline] def f32t (v : Float) : Float := v.toF32

/-- Rust `x as i32` of a `usize`. -/
@[inline] def toI32 (n : Nat) : Int :=
  -- `n mod 2^32` reinterpreted as two's complement, without `Nat` literals above `2^32` (the C
  -- backend parses those from strings with GMP on every evaluation)
  let m := n.toUInt32
  if m >= 2147483648 then -(((0 : UInt32) - m).toNat : Int) else (m.toNat : Int)

/-- Rust `Vec::resize(n, 0.0)`. -/
@[inline] def resizeFloats (arr : Array Float) (n : Nat) : Array Float :=
  if n <= arr.size then arr.extract 0 n else arr ++ Array.replicate (n - arr.size) 0.0

/-- `ensure_port_capacity(port_id)`: grows both id-indexed arrays to `pid + 1`. -/
def ensurePortCapacity (st : BarycenterPortDistributorState) (pid : Nat) : BarycenterPortDistributorState :=
  if pid >= st.portRanks.size && pid >>> 32 == 0 then
    { st with portRanks := resizeFloats st.portRanks (pid + 1), portBarycenter := resizeFloats st.portBarycenter (pid + 1) }
  else st

/-- `port_ranks[pid] = v`. -/
@[inline] def setRank (st : BarycenterPortDistributorState) (pid : Nat) (v : Float) : BarycenterPortDistributorState :=
  -- take the array out first so that it is updated in place (`{ st with f := st.f.set … }` keeps
  -- a second reference alive during the update and copies the array)
  let ranks := st.portRanks
  let st := { st with portRanks := #[] }
  { st with portRanks := ranks.setIfInBounds pid v }

/-- `port_ranks.get(pid).unwrap_or(0.0)`. -/
@[inline] def rankOf (st : BarycenterPortDistributorState) (pid : Nat) : Float := st.portRanks[pid]?.getD 0.0

/-- `port_barycenter[pid] = v`. -/
@[inline] def setBarycenter (st : BarycenterPortDistributorState) (pid : Nat) (v : Float) : BarycenterPortDistributorState :=
  let bary := st.portBarycenter
  let st := { st with portBarycenter := #[] }
  { st with portBarycenter := bary.setIfInBounds pid v }

/-- `port_barycenter.get(pid).unwrap_or(0.0)`. -/
@[inline] def barycenterOf (st : BarycenterPortDistributorState) (pid : Nat) : Float := st.portBarycenter[pid]?.getD 0.0

/-- `node_positions.get(layer).and_then(|p| p.get(node)).unwrap_or(node)`. -/
@[inline] def positionIn (st : BarycenterPortDistributorState) (layerIndex nodeIndex : Nat) : Nat :=
  ((st.nodePositions[layerIndex]?).bind (·[nodeIndex]?)).getD nodeIndex

/-- Ensures capacity for the largest of `pids` (the snapshot rank paths). -/
def ensureForAll (st : BarycenterPortDistributorState) (pids : Array Nat) : BarycenterPortDistributorState :=
  match pids.foldl (fun m p => some (match m with | some x => max x p | none => p)) none with
  | some maxPid => st.ensurePortCapacity maxPid
  | none => st

end BarycenterPortDistributorState

open BarycenterPortDistributorState

/-! ## Port ranks -/

/-- `calculate_port_ranks_node_relative`, snapshot path: `pids` are the captured ids of the
node's current ports. -/
def ranksNodeRelativeSnap (s : CrossMinSnapshot) (pids : Array Nat) (st : BarycenterPortDistributorState)
    (rankSum : Float) (portType : PortType) : BarycenterPortDistributorState × Float := Id.run do
  let mut st := st.ensureForAll pids
  match portType with
  | .input =>
    let mut inputCount : Nat := 0
    let mut northInputCount : Nat := 0
    for pid in pids do
      if !(s.portPredecessors pid).isEmpty then
        inputCount := inputCount + 1
        if s.portSideOf pid == .north then northInputCount := northInputCount + 1
    if inputCount == 0 then return (st, 1.0)
    let incr := 1.0 / (inputCount.toFloat + 1.0)
    let mut northPos := rankSum + northInputCount.toFloat * incr
    let mut restPos := rankSum + 1.0 - incr
    for pid in pids do
      if (s.portPredecessors pid).isEmpty then continue
      if s.portSideOf pid == .north then
        st := st.setRank pid (f32t northPos)
        northPos := northPos - incr
      else
        st := st.setRank pid (f32t restPos)
        restPos := restPos - incr
    return (st, 1.0)
  | .output =>
    let mut outputCount : Nat := 0
    for pid in pids do
      if !(s.portSuccessors pid).isEmpty then outputCount := outputCount + 1
    if outputCount == 0 then return (st, 1.0)
    let incr := 1.0 / (outputCount.toFloat + 1.0)
    let mut pos := rankSum + incr
    for pid in pids do
      if (s.portSuccessors pid).isEmpty then continue
      st := st.setRank pid (f32t pos)
      pos := pos + incr
    return (st, 1.0)
  | .undefined => return (st, 1.0)

/-- `calculate_port_ranks_node_relative`, lock path (live ports, `ports_by_type`). -/
def ranksNodeRelativeLock (a : LGraphArena) (node : LNodeId) (st : BarycenterPortDistributorState)
    (rankSum : Float) (portType : PortType) : BarycenterPortDistributorState × Float := Id.run do
  let ports := (a.node node).ports
  let mut st := st
  match portType with
  | .input =>
    let mut inputCount : Nat := 0
    let mut northInputCount : Nat := 0
    for port in ports do
      let pt := a.port port
      if !pt.incomingEdges.isEmpty then
        inputCount := inputCount + 1
        if pt.side == .north then northInputCount := northInputCount + 1
    if inputCount == 0 then return (st, 1.0)
    let incr := 1.0 / (inputCount.toFloat + 1.0)
    let mut northPos := rankSum + northInputCount.toFloat * incr
    let mut restPos := rankSum + 1.0 - incr
    for port in a.nodePortsByType node .input do
      let pt := a.port port
      let pid := asUsize pt.id
      st := st.ensurePortCapacity pid
      if pt.side == .north then
        st := st.setRank pid (f32t northPos)
        northPos := northPos - incr
      else
        st := st.setRank pid (f32t restPos)
        restPos := restPos - incr
    return (st, 1.0)
  | .output =>
    let mut outputCount : Nat := 0
    for port in ports do
      if !(a.port port).outgoingEdges.isEmpty then outputCount := outputCount + 1
    if outputCount == 0 then return (st, 1.0)
    let incr := 1.0 / (outputCount.toFloat + 1.0)
    let mut pos := rankSum + incr
    for port in a.nodePortsByType node .output do
      let pid := asUsize (a.port port).id
      st := st.ensurePortCapacity pid
      st := st.setRank pid (f32t pos)
      pos := pos + incr
    return (st, 1.0)
  | .undefined => return (st, 1.0)

/-- `calculate_port_ranks_layer_total`, snapshot path. -/
def ranksLayerTotalSnap (s : CrossMinSnapshot) (pids : Array Nat) (st : BarycenterPortDistributorState)
    (rankSum : Float) (portType : PortType) : BarycenterPortDistributorState × Float := Id.run do
  let mut st := st.ensureForAll pids
  match portType with
  | .input =>
    let mut inputCount : Nat := 0
    let mut northInputCount : Nat := 0
    for pid in pids do
      if !(s.portPredecessors pid).isEmpty then
        inputCount := inputCount + 1
        if s.portSideOf pid == .north then northInputCount := northInputCount + 1
    if inputCount == 0 then return (st, 0.0)
    let mut northPos := rankSum + northInputCount.toFloat
    let mut restPos := rankSum + inputCount.toFloat
    for pid in pids do
      if (s.portPredecessors pid).isEmpty then continue
      if s.portSideOf pid == .north then
        st := st.setRank pid (f32t northPos)
        northPos := northPos - 1.0
      else
        st := st.setRank pid (f32t restPos)
        restPos := restPos - 1.0
    return (st, inputCount.toFloat)
  | .output =>
    let mut pos : Float := 0.0
    for pid in pids do
      if (s.portSuccessors pid).isEmpty then continue
      pos := pos + 1.0
      st := st.setRank pid (f32t (rankSum + pos))
    return (st, pos)
  | .undefined => return (st, 0.0)

/-- `calculate_port_ranks_layer_total`, lock path. -/
def ranksLayerTotalLock (a : LGraphArena) (node : LNodeId) (st : BarycenterPortDistributorState)
    (rankSum : Float) (portType : PortType) : BarycenterPortDistributorState × Float := Id.run do
  let ports := (a.node node).ports
  let mut st := st
  match portType with
  | .input =>
    let mut inputCount : Nat := 0
    let mut northInputCount : Nat := 0
    for port in ports do
      let pt := a.port port
      if !pt.incomingEdges.isEmpty then
        inputCount := inputCount + 1
        if pt.side == .north then northInputCount := northInputCount + 1
    if inputCount == 0 then return (st, 0.0)
    let mut northPos := rankSum + northInputCount.toFloat
    let mut restPos := rankSum + inputCount.toFloat
    for port in a.nodePortsByType node .input do
      let pt := a.port port
      let pid := asUsize pt.id
      st := st.ensurePortCapacity pid
      if pt.side == .north then
        st := st.setRank pid (f32t northPos)
        northPos := northPos - 1.0
      else
        st := st.setRank pid (f32t restPos)
        restPos := restPos - 1.0
    return (st, inputCount.toFloat)
  | .output =>
    let mut pos : Float := 0.0
    for port in a.nodePortsByType node .output do
      pos := pos + 1.0
      let pid := asUsize (a.port port).id
      st := st.ensurePortCapacity pid
      st := st.setRank pid (f32t (rankSum + pos))
    return (st, pos)
  | .undefined => return (st, 0.0)

/-- `calculate_port_ranks_for_node(node, rank_sum, port_type)`: the rank consumed by the node. -/
def ranksForNode (strategy : PortRankStrategy) (snap : Option CrossMinSnapshot) (a : LGraphArena) (node : LNodeId)
    (st : BarycenterPortDistributorState) (rankSum : Float) (portType : PortType) : BarycenterPortDistributorState × Float :=
  match strategy, snap with
  | .nodeRelative, some s => ranksNodeRelativeSnap s ((a.node node).ports.map s.portId) st rankSum portType
  | .nodeRelative, none => ranksNodeRelativeLock a node st rankSum portType
  | .layerTotal, some s => ranksLayerTotalSnap s ((a.node node).ports.map s.portId) st rankSum portType
  | .layerTotal, none => ranksLayerTotalLock a node st rankSum portType

/-! ## Barycenter values -/

/-- Rust `port_same_layer(port, node)`: the port's owner lies in the node's layer. -/
def portSameLayer (a : LGraphArena) (port : LPortId) (node : LNodeId) : Bool :=
  match (a.port port).owner with
  | none => false
  | some owner =>
    match (a.node owner).layer, (a.node node).layer with
    | some pl, some nl => pl == nl
    | _, _ => false

/-- `position_of(node)`: `node_positions[layer index][node id]` (snapshot or live ids). -/
def positionOf (snap : Option CrossMinSnapshot) (a : LGraphArena) (st : BarycenterPortDistributorState) (node : LNodeId) : Nat :=
  match snap with
  | some s => st.positionIn (s.nodeLayerIndex node) (s.nodeId node)
  | none =>
    let layerIndex := match (a.node node).layer with
      | some l => asUsize (a.layer l).id
      | none => 0
    st.positionIn layerIndex (asUsize (a.node node).id)

/-- Whether the dummy port's `ORIGIN` is `port`. -/
@[inline] private def originIs (a : LGraphArena) (dummyPort port : LPortId) : Bool :=
  match (a.port dummyPort).internal.origin with
  | some (.lPort origin) => origin == port
  | _ => false

/-- `deal_with_north_south_ports(absurdly_large_float, port, port_dummy)`: the sort key of a
north/south port from the input/output role of its dummy's ports. -/
def dealWithNorthSouthPorts (snap : Option CrossMinSnapshot) (a : LGraphArena) (st : BarycenterPortDistributorState)
    (absurdlyLargeFloat : Float) (port : LPortId) (portDummy : LNodeId) : Float := Id.run do
  let mut input := false
  let mut output := false
  match snap with
  | some s =>
    for dpid in s.nodePorts (s.nodeFlatIndex portDummy) do
      let originMatches := match s.portRefOpt dpid with
        | some dp => originIs a dp port
        | none => false
      if !originMatches then continue
      if !(s.portSuccessors dpid).isEmpty then output := true
      else if !(s.portPredecessors dpid).isEmpty then input := true
  | none =>
    for dp in (a.node portDummy).ports do
      if !originIs a dp port then continue
      let dpt := a.port dp
      if !dpt.outgoingEdges.isEmpty then output := true
      else if !dpt.incomingEdges.isEmpty then input := true
  let side := match snap with
    | some s => s.portSideOf (s.portId port)
    | none => (a.port port).side
  let exclusive := input != output
  if input && exclusive then
    let pos := (positionOf snap a st portDummy).toFloat
    return if side == .north then -pos else absurdlyLargeFloat - pos
  else if output && exclusive then
    return (positionOf snap a st portDummy).toFloat + 1.0
  else if input && output then
    return if side == .north then 0.0 else absurdlyLargeFloat / 2.0
  else
    return 0.0

/-- The end of the Rust port loop: `sum / degree` (or the north/south sum) is stored and the
running `f64` min/max are updated. -/
def recordBarycenter (st : BarycenterPortDistributorState) (pid : Nat) (degree : Int) (sum : Float) (northSouth : Bool)
    (minB maxB : Float) : BarycenterPortDistributorState × Float × Float :=
  let st := st.ensurePortCapacity pid
  if degree > 0 then
    let value := f32t (sum / f32t (Float.ofInt degree))
    (st.setBarycenter pid value, fmin minB value, fmax maxB value)
  else if northSouth then (st.setBarycenter pid sum, minB, maxB)
  else (st, minB, maxB)

/-- The barycenter of an in-layer port (`calculate_in_layer_ports_*`, `f32` arithmetic):
`none` for ports on the north/south sides. -/
def inLayerValue (side : PortSide) (sum conns nodeIndexInLayer layerSize : Int) (minB maxB : Float) : Option Float :=
  let barycenter := f32t (f32t (Float.ofInt sum) / f32t (Float.ofInt conns))
  let nodeIndexF := f32t (Float.ofInt nodeIndexInLayer)
  let layerSizeF := f32t (Float.ofInt layerSize)
  match side with
  | .east =>
    some (if barycenter < nodeIndexF then f32t (f32t minB - barycenter)
      else f32t (f32t maxB + f32t (layerSizeF - barycenter)))
  | .west =>
    some (if barycenter < nodeIndexF then f32t (f32t maxB + barycenter)
      else f32t (f32t minB - f32t (layerSizeF - barycenter)))
  | _ => none

/-! ### Snapshot path -/

/-- The ranks of the far ends of a non-north/south port (`+` successors, `-` predecessors);
`none` as soon as a far end lies in the node's layer (Rust `continue 'port_iteration`). -/
def connectedRankSumSnap (s : CrossMinSnapshot) (st : BarycenterPortDistributorState) (pid nodeLayer : Nat) : Option Float := Id.run do
  let mut sum : Float := 0.0
  for target in s.portSuccessors pid do
    if s.portOwnerLayer target == nodeLayer then return none
    sum := f32t (sum + f32t (st.rankOf target))
  for source in s.portPredecessors pid do
    if s.portOwnerLayer source == nodeLayer then return none
    sum := f32t (sum - f32t (st.rankOf source))
  return some sum

/-- The port loop of `distribute_ports_for_iter_snap`: barycenters of `pids`, the in-layer
ports and the min/max barycenter. -/
def iteratePortsSnap (s : CrossMinSnapshot) (a : LGraphArena) (st : BarycenterPortDistributorState) (node : LNodeId)
    (pids : Array Nat) (layerSize : Nat) : BarycenterPortDistributorState × Array Nat × Float × Float := Id.run do
  let absurdlyLargeFloat := f32t (2 * layerSize + 1).toFloat
  let nodeLayer := s.nodeLayerIndex node
  let mut st := st
  let mut inLayer : Array Nat := #[]
  let mut minB : Float := 0.0
  let mut maxB : Float := 0.0
  for pid in pids do
    let side := s.portSideOf pid
    let northSouth := side == .north || side == .south
    let mut sum : Float := 0.0
    if northSouth then
      let some portRef := s.portRefOpt pid | continue
      let some dummy := (a.port portRef).internal.portDummy | continue
      -- Rust: `self.snapshot` is taken while distributing, so the lock path runs
      sum := f32t (sum + f32t (dealWithNorthSouthPorts none a st absurdlyLargeFloat portRef dummy))
    else
      match connectedRankSumSnap s st pid nodeLayer with
      | none =>
        inLayer := inLayer.push pid
        continue
      | some v => sum := v
    let degree : Int := (s.portPredecessors pid).size + (s.portSuccessors pid).size
    (st, minB, maxB) := recordBarycenter st pid degree sum northSouth minB maxB
  return (st, inLayer, minB, maxB)

/-- `calculate_in_layer_ports_snap(node, node_id, layer_index, layer_size)`. -/
def inLayerPortsSnap (s : CrossMinSnapshot) (st : BarycenterPortDistributorState) (node : LNodeId) (nodeId : Int)
    (layerIndex layerSize : Nat) (pids : Array Nat) (minB maxB : Float) : BarycenterPortDistributorState := Id.run do
  let nodeIdUsize : Nat := if nodeId < 0 then 0 else nodeId.toNat
  let nodeIndexInLayer : Int := toI32 (st.positionIn layerIndex nodeIdUsize) + 1
  let layerSizeI : Int := toI32 layerSize + 1
  let nodeFlat := s.nodeFlatIndex node
  let nodeLayer := s.nodeLayerOf nodeFlat
  let mut st := st
  for pid in pids do
    let mut sum : Int := 0
    let mut inLayerConnections : Int := 0
    for connected in s.portPredecessors pid ++ s.portSuccessors pid do
      if s.portOwnerLayer connected == nodeLayer then
        if s.portOwnerFlat connected == nodeFlat then
          sum := sum + nodeIndexInLayer
        else
          let connectedNid := s.nodeGraphIdOf (s.portOwnerFlat connected)
          sum := sum + (toI32 (st.positionIn layerIndex connectedNid) + 1)
        inLayerConnections := inLayerConnections + 1
    if inLayerConnections == 0 then continue
    st := st.ensurePortCapacity pid
    if let some v := inLayerValue (s.portSideOf pid) sum inLayerConnections nodeIndexInLayer layerSizeI minB maxB then
      st := st.setBarycenter pid v
  return st

/-- `distribute_ports_for_iter_snap(node, port_ids, node_id, layer_index, layer_size)`. -/
def distributePortsForIterSnap (s : CrossMinSnapshot) (a : LGraphArena) (st : BarycenterPortDistributorState) (node : LNodeId)
    (pids : Array Nat) (nodeId : Int) (layerIndex layerSize : Nat) : BarycenterPortDistributorState :=
  let (st, inLayer, minB, maxB) := iteratePortsSnap s a st node pids layerSize
  if inLayer.isEmpty then st else inLayerPortsSnap s st node nodeId layerIndex layerSize inLayer minB maxB

/-- Rust comparator on two barycenters of the same side: `0.0` (no barycenter) first, then
`partial_cmp` (NaN compares equal). -/
def compareBarycenters (b1 b2 : Float) : Ordering :=
  if b1 == 0.0 && b2 == 0.0 then .eq
  else if b1 == 0.0 then .lt
  else if b2 == 0.0 then .gt
  else Float.comparePartial b1 b2

/-- `sort_ports_snap(node)`: the *captured* port order stably sorted by (side, barycenter).
Unreachable in elk-rs (`sort_ports` only reaches it while `self.snapshot` is set, but its only
caller with a snapshot, `distribute_ports`, has taken the snapshot out); kept for reference. -/
def sortPortsSnap (s : CrossMinSnapshot) (st : BarycenterPortDistributorState) (node : LNodeId) : Array LPortId :=
  let pids := s.nodePorts (s.nodeFlatIndex node)
  let sorted := stableSort pids fun x y =>
    let sx := s.portSideOf x
    let sy := s.portSideOf y
    if sx != sy then compare (ElkEnum.ordinal sx) (ElkEnum.ordinal sy)
    else compareBarycenters (st.barycenterOf x) (st.barycenterOf y)
  sorted.filterMap s.portRefOpt

/-! ### Lock path -/

/-- Like `connectedRankSumSnap` on the live edges (edges without a far end are skipped). -/
def connectedRankSumLock (a : LGraphArena) (st : BarycenterPortDistributorState) (port : LPortId) (node : LNodeId) :
    Option Float := Id.run do
  let mut sum : Float := 0.0
  let pt := a.port port
  for e in pt.outgoingEdges do
    let some connected := (a.edge e).target | continue
    if portSameLayer a connected node then return none
    sum := f32t (sum + f32t (st.rankOf (asUsize (a.port connected).id)))
  for e in pt.incomingEdges do
    let some connected := (a.edge e).source | continue
    if portSameLayer a connected node then return none
    sum := f32t (sum - f32t (st.rankOf (asUsize (a.port connected).id)))
  return some sum

/-- Rust `layer_size(node)`: node count of the node's layer (`0` without a layer). -/
def layerSizeOf (a : LGraphArena) (node : LNodeId) : Nat :=
  match (a.node node).layer with
  | some l => (a.layer l).nodes.size
  | none => 0

/-- `iterate_ports_lock` (via `iterate_ports_and_collect_in_layer_ports`). -/
def iteratePortsLock (a : LGraphArena) (st : BarycenterPortDistributorState) (node : LNodeId) (ports : Array LPortId) :
    BarycenterPortDistributorState × Array LPortId × Float × Float := Id.run do
  let absurdlyLargeFloat := f32t (2 * layerSizeOf a node + 1).toFloat
  let mut st := st
  let mut inLayer : Array LPortId := #[]
  let mut minB : Float := 0.0
  let mut maxB : Float := 0.0
  for port in ports do
    let pt := a.port port
    let pid := asUsize pt.id
    let northSouth := pt.side == .north || pt.side == .south
    let mut sum : Float := 0.0
    if northSouth then
      let some dummy := pt.internal.portDummy | continue
      sum := f32t (sum + f32t (dealWithNorthSouthPorts none a st absurdlyLargeFloat port dummy))
    else
      match connectedRankSumLock a st port node with
      | none =>
        inLayer := inLayer.push port
        continue
      | some v => sum := v
    (st, minB, maxB) := recordBarycenter st pid pt.degree sum northSouth minB maxB
  return (st, inLayer, minB, maxB)

/-- Rust `position_of_node_port_owner_in_layer(port, layer_index)` (live ids; `0` without owner). -/
def positionOfPortOwnerInLayer (a : LGraphArena) (st : BarycenterPortDistributorState) (port : LPortId) (layerIndex : Nat) : Nat :=
  match (a.port port).owner with
  | some owner => st.positionIn layerIndex (asUsize (a.node owner).id)
  | none => 0

/-- `calculate_in_layer_ports_barycenter_values(node, node_id, layer_index, layer_size)`. -/
def inLayerPortsLock (a : LGraphArena) (st : BarycenterPortDistributorState) (node : LNodeId) (nodeId : Int)
    (layerIndex layerSize : Nat) (ports : Array LPortId) (minB maxB : Float) : BarycenterPortDistributorState := Id.run do
  let nodeIdUsize : Nat := if nodeId < 0 then 0 else nodeId.toNat
  let nodeIndexInLayer : Int := toI32 (st.positionIn layerIndex nodeIdUsize) + 1
  let layerSizeI : Int := toI32 layerSize + 1
  let mut st := st
  for port in ports do
    let mut sum : Int := 0
    let mut inLayerConnections : Int := 0
    for connected in a.portConnectedPorts port do
      if portSameLayer a connected node then
        if (a.port connected).owner == some node then
          sum := sum + nodeIndexInLayer
        else
          sum := sum + (toI32 (positionOfPortOwnerInLayer a st connected layerIndex) + 1)
        inLayerConnections := inLayerConnections + 1
    if inLayerConnections == 0 then continue
    let pt := a.port port
    let pid := asUsize pt.id
    st := st.ensurePortCapacity pid
    if let some v := inLayerValue pt.side sum inLayerConnections nodeIndexInLayer layerSizeI minB maxB then
      st := st.setBarycenter pid v
  return st

/-- `distribute_ports_for_iter(node, ports, node_id, layer_index, layer_size)`. -/
def distributePortsForIterLock (a : LGraphArena) (st : BarycenterPortDistributorState) (node : LNodeId)
    (ports : Array LPortId) (nodeId : Int) (layerIndex layerSize : Nat) : BarycenterPortDistributorState :=
  let (st, inLayer, minB, maxB) := iteratePortsLock a st node ports
  if inLayer.isEmpty then st else inLayerPortsLock a st node nodeId layerIndex layerSize inLayer minB maxB

/-- `sort_ports(node)` (lock path): the current ports sorted by (side, barycenter, index). -/
def sortPortsLock (a : LGraphArena) (st : BarycenterPortDistributorState) (node : LNodeId) : Array LPortId :=
  let keyed := (a.node node).ports.mapIdx fun idx p =>
    let pt := a.port p
    (pt.side, st.barycenterOf (asUsize pt.id), idx, p)
  let sorted := stableSort keyed fun (side1, bary1, idx1, _) (side2, bary2, idx2, _) =>
    let ord := if side1 != side2 then compare (ElkEnum.ordinal side1) (ElkEnum.ordinal side2)
      else compareBarycenters bary1 bary2
    if ord == .eq then compare idx1 idx2 else ord
  sorted.map fun (_, _, _, p) => p

/-! ## The distributor -/

/-- `AbstractBarycenterPortDistributor` (with its rank strategy). -/
structure AbstractBarycenterPortDistributor where
  /-- `strategy`. -/
  strategy : PortRankStrategy
  /-- The mutable fields. -/
  state : IO.Ref BarycenterPortDistributorState
  /-- `snapshot` (`set_snapshot`). -/
  snapshot : IO.Ref (Option CrossMinSnapshot)

namespace AbstractBarycenterPortDistributor

/-- `AbstractBarycenterPortDistributor::new(num_layers, strategy)`. -/
def new (numLayers : Nat) (strategy : PortRankStrategy) : BaseIO AbstractBarycenterPortDistributor := do
  return {
    strategy
    state := ← IO.mkRef { nodePositions := Array.replicate numLayers #[] }
    snapshot := ← IO.mkRef none }

/-- `set_snapshot(snapshot)` (`BarycenterPortDistributor` trait). -/
def setSnapshot (d : AbstractBarycenterPortDistributor) (s : CrossMinSnapshot) : BaseIO Unit := d.snapshot.set (some s)

/-- `port_ranks()` (a copy). -/
def portRanks (d : AbstractBarycenterPortDistributor) : BaseIO (Array Float) := do
  return (← d.state.get).portRanks

/-- `port_barycenter` (a copy; testing/debugging). -/
def portBarycenters (d : AbstractBarycenterPortDistributor) : BaseIO (Array Float) := do
  return (← d.state.get).portBarycenter

/-- `calculate_port_ranks(layer, port_type)` on an explicit state. -/
def calculatePortRanksOn (d : AbstractBarycenterPortDistributor) (st : BarycenterPortDistributorState)
    (layer : Array LNodeId) (portType : PortType) : LayeredM BarycenterPortDistributorState := do
  let a ← get
  let snap ← d.snapshot.get
  let mut st := st
  let mut consumedRank : Float := 0.0
  for node in layer do
    let (st', consumed) := ranksForNode d.strategy snap a node st consumedRank portType
    st := st'
    consumedRank := consumedRank + consumed
  return st

/-- `calculate_port_ranks(layer, port_type)`: ranks of the layer's ports of the given type,
written to the rank array. -/
def calculatePortRanks (d : AbstractBarycenterPortDistributor) (layer : Array LNodeId) (portType : PortType) :
    LayeredM Unit := do
  let st ← d.state.swap {}
  let st ← d.calculatePortRanksOn st layer portType
  d.state.set st

/-- Writes a sorted port list (`*ports_mut() = ports; cache_port_sides()`). -/
private def setPorts (node : LNodeId) (ports : Array LPortId) : LayeredM Unit := do
  modifyNode node fun x => { x with ports := ports }
  cachePortSides node

/-- `distribute_ports_snap(node, side, layer_index, layer_size)`. -/
private def distributePortsSnap (s : CrossMinSnapshot) (st : BarycenterPortDistributorState) (node : LNodeId)
    (side : PortSide) (layerIndex layerSize : Nat) : LayeredM BarycenterPortDistributorState := do
  let a ← get
  let flat := s.nodeFlatIndex node
  let nodeId := toI32 (s.nodeGraphIdOf flat)
  let constraints := (a.node node).props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  let portIds := s.nodePorts flat
  let sideIds := portIds.filter (s.portSideOf · == side)
  let southIds := portIds.filter (s.portSideOf · == .south)
  let northIds := portIds.filter (s.portSideOf · == .north)
  if constraints.isOrderFixed then return st
  let st := distributePortsForIterSnap s a st node sideIds nodeId layerIndex layerSize
  let st := distributePortsForIterSnap s a st node southIds nodeId layerIndex layerSize
  let st := distributePortsForIterSnap s a st node northIds nodeId layerIndex layerSize
  -- Rust `sort_ports(node)` runs while `distribute_ports` holds the snapshot taken out of
  -- `self.snapshot`, so its lock fallback sorts the *current* port order (index tie-break)
  setPorts node (sortPortsLock a st node)
  return st

/-- `distribute_ports(node, side, layer_index, layer_size)` (lock path). -/
private def distributePortsLock (st : BarycenterPortDistributorState) (node : LNodeId) (side : PortSide)
    (layerIndex layerSize : Nat) : LayeredM BarycenterPortDistributorState := do
  let a ← get
  let nd := a.node node
  let constraints := nd.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  let sidePorts := nd.ports.filter fun p => (a.port p).side == side
  let southPorts := nd.ports.filter fun p => (a.port p).side == .south
  let northPorts := nd.ports.filter fun p => (a.port p).side == .north
  if constraints.isOrderFixed then return st
  let st := distributePortsForIterLock a st node sidePorts nd.id layerIndex layerSize
  let st := distributePortsForIterLock a st node southPorts nd.id layerIndex layerSize
  let st := distributePortsForIterLock a st node northPorts nd.id layerIndex layerSize
  setPorts node (sortPortsLock a st node)
  return st

/-- `distribute_ports(node, side, layer_index, layer_size)`: unless the port order is fixed, the
barycenters of the ports on `side`, `SOUTH` and `NORTH` are computed and the ports sorted. -/
def distributePorts (snap : Option CrossMinSnapshot) (st : BarycenterPortDistributorState) (node : LNodeId)
    (side : PortSide) (layerIndex layerSize : Nat) : LayeredM BarycenterPortDistributorState :=
  match snap with
  | some s => distributePortsSnap s st node side layerIndex layerSize
  | none => distributePortsLock st node side layerIndex layerSize

/-- `update_node_positions(node_order, current_index)`. -/
def updateNodePositions (snap : Option CrossMinSnapshot) (a : LGraphArena) (st : BarycenterPortDistributorState)
    (order : Array (Array LNodeId)) (currentIndex : Nat) : BarycenterPortDistributorState :=
  if currentIndex < st.nodePositions.size then
    let layer := order[currentIndex]?.getD #[]
    { st with nodePositions := st.nodePositions.modify currentIndex fun positions => Id.run do
        let mut positions := positions
        for h : index in [0:layer.size] do
          let node := layer[index]
          let nid := match snap with
            | some s => s.nodeId node
            | none => asUsize (a.node node).id
          if nid >= positions.size && nid >>> 32 == 0 then
            positions := positions ++ Array.replicate (nid + 1 - positions.size) 0
          positions := positions.setIfInBounds nid index
        return positions }
  else st

/-- `has_nested_graph(node)`. -/
def hasNestedGraph (snap : Option CrossMinSnapshot) (a : LGraphArena) (node : LNodeId) : Bool :=
  match snap with
  | some s => s.nodeHasNestedGraph (s.nodeFlatIndex node)
  | none => (a.node node).nestedGraph.isSome

/-- `is_not_first_layer(length, current_index, is_forward)`. -/
@[inline] def isNotFirstLayer (length currentIndex : Nat) (isForward : Bool) : Bool :=
  if isForward then currentIndex != 0 else currentIndex + 1 < length

/-- `port_type_for(is_forward)`. -/
@[inline] def portTypeFor (isForward : Bool) : PortType := if isForward then .output else .input

/-- `distribute_ports_while_sweeping(node_order, current_index, is_forward_sweep)`: ranks of the
fixed layer, distribution on the free layer's sweep side, ranks of the free layer and
distribution on the fixed layer's opposite side (nodes without nested graph); in the first
layer only the free layer is distributed. Always `false` (the distributor does not count). -/
def distributePortsWhileSweeping (d : AbstractBarycenterPortDistributor) (order : Array (Array LNodeId))
    (currentIndex : Nat) (isForwardSweep : Bool) : LayeredM Bool := do
  let snap ← d.snapshot.get
  let mut st ← d.state.swap {}
  st := updateNodePositions snap (← get) st order currentIndex
  let freeLayer := order[currentIndex]?.getD #[]
  let side : PortSide := if isForwardSweep then .west else .east
  if isNotFirstLayer order.size currentIndex isForwardSweep then
    let fixedLayerIndex := if isForwardSweep then currentIndex - 1 else currentIndex + 1
    let fixedLayer := order[fixedLayerIndex]?.getD #[]
    st ← d.calculatePortRanksOn st fixedLayer (portTypeFor isForwardSweep)
    for node in freeLayer do
      st ← distributePorts snap st node side currentIndex freeLayer.size
    st ← d.calculatePortRanksOn st freeLayer (portTypeFor !isForwardSweep)
    for node in fixedLayer do
      if !hasNestedGraph snap (← get) node then
        st ← distributePorts snap st node side.opposed fixedLayerIndex fixedLayer.size
  else
    for node in freeLayer do
      st ← distributePorts snap st node side currentIndex freeLayer.size
  d.state.set st
  return false

/-- `init_at_layer_level(layer_index, node_order)`. -/
def initAtLayerLevel (d : AbstractBarycenterPortDistributor) (l : Nat) (order : Array (Array LNodeId)) : LayeredM Unit := do
  let len := (order[l]?.map (·.size)).getD 0
  d.state.modify fun st =>
    let positions := if l >= st.nodePositions.size then st.nodePositions ++ Array.replicate (l + 1 - st.nodePositions.size) #[]
      else st.nodePositions
    { st with nodePositions := positions.setIfInBounds l (Array.replicate len 0) }

/-- `init_at_node_level(layer_index, node_index, node_order)`: `node.id := nodeIndex` and the
initial position. -/
def initAtNodeLevel (d : AbstractBarycenterPortDistributor) (l n : Nat) (order : Array (Array LNodeId)) : LayeredM Unit := do
  let some node := (order[l]?).bind (·[n]?) | return
  modifyNode node fun x => { x with id := n }
  d.state.modify fun st => { st with
    nodePositions := st.nodePositions.modify l fun positions =>
      let positions := if n >= positions.size then positions ++ Array.replicate (n + 1 - positions.size) 0 else positions
      positions.setIfInBounds n n }

/-- `init_at_port_level(layer_index, node_index, port_index, node_order)`: `port.id := nPorts++`. -/
def initAtPortLevel (d : AbstractBarycenterPortDistributor) (l n p : Nat) (order : Array (Array LNodeId)) : LayeredM Unit := do
  let some node := (order[l]?).bind (·[n]?) | return
  let some port := (← getNode node).ports[p]? | return
  let id := (← d.state.get).nPorts
  modifyPort port fun x => { x with id := id }
  d.state.modify fun st => { st with nPorts := st.nPorts + 1 }

/-- `init_after_traversal()`: zeroed rank and barycenter arrays of `nPorts` entries. -/
def initAfterTraversal (d : AbstractBarycenterPortDistributor) : LayeredM Unit :=
  d.state.modify fun st => { st with
    portRanks := Array.replicate st.nPorts 0.0, portBarycenter := Array.replicate st.nPorts 0.0 }

/-- The `IInitializable` implementation. -/
def initializable (d : AbstractBarycenterPortDistributor) : Initializable where
  initAtLayerLevel := d.initAtLayerLevel
  initAtNodeLevel := d.initAtNodeLevel
  initAtPortLevel := d.initAtPortLevel
  initAfterTraversal := d.initAfterTraversal

/-- The `ISweepPortDistributor` implementation. -/
def toSweepPortDistributor (d : AbstractBarycenterPortDistributor) : SweepPortDistributor where
  initializable := d.initializable
  distributePortsWhileSweeping := d.distributePortsWhileSweeping

end AbstractBarycenterPortDistributor

end Elk.Alg.Layered.P3Order
