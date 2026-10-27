import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.P3Order.CrossMinSnapshot
import Elk.Alg.Layered.P3Order.ISweepPortDistributor
import Elk.Alg.Layered.P3Order.Counting.BinaryIndexedTree
import Elk.Alg.Layered.P3Order.Counting.CrossMinUtil
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

Performance (no Rust counterpart): ranks and barycenters are `FloatArray`s (unboxed), the
snapshot path's loops are tail recursive over the state (whose scratch fields hold the running
min/max barycenter and the in-layer ports, so nothing is allocated per port), `sort_ports`
sorts the port list directly (the index tie-break of the keyed sort is implied by the stable
sort), and a node is only rewritten when the sorted order or its side cache differs from the
current one (`cachePortSides` would then not change it).
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
  portRanks : FloatArray := FloatArray.empty
  /-- `node_positions[layer][node id]`: position of the node in the layer. -/
  nodePositions : Array (Array Nat) := #[]
  /-- `port_barycenter` (by port id, `f32` values). -/
  portBarycenter : FloatArray := FloatArray.empty
  /-- `n_ports`: the next port id handed out by `initAtPortLevel`. -/
  nPorts : Nat := 0
  /-- Scratch of the snapshot port iteration: `min_barycenter`. -/
  minBarycenter : Float := 0.0
  /-- Scratch of the snapshot port iteration: `max_barycenter`. -/
  maxBarycenter : Float := 0.0
  /-- Scratch of the snapshot port iteration: `in_layer_port_ids`. -/
  inLayerPortIds : Array Nat := #[]
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

/-- `n` zeros. -/
def zeros (n : Nat) : FloatArray := Id.run do
  let mut arr := FloatArray.emptyWithCapacity n
  for _ in [0:n] do
    arr := arr.push 0.0
  return arr

/-- Rust `Vec::resize(n, 0.0)`. -/
def resizeFloats (arr : FloatArray) (n : Nat) : FloatArray := Id.run do
  if n <= arr.size then
    let mut out := FloatArray.emptyWithCapacity n
    for i in [0:n] do
      out := out.push (arr.get! i)
    return out
  else
    let mut arr := arr
    for _ in [0:n - arr.size] do
      arr := arr.push 0.0
    return arr

/-- `ensure_port_capacity(port_id)`: grows both id-indexed arrays to `pid + 1`. -/
def ensurePortCapacity (st : BarycenterPortDistributorState) (pid : Nat) : BarycenterPortDistributorState :=
  if pid >= st.portRanks.size && pid >>> 32 == 0 then
    { st with portRanks := resizeFloats st.portRanks (pid + 1), portBarycenter := resizeFloats st.portBarycenter (pid + 1) }
  else st

/-- `port_ranks[pid] = v` (no-op out of range). -/
@[inline] def setRank (st : BarycenterPortDistributorState) (pid : Nat) (v : Float) : BarycenterPortDistributorState :=
  { st with portRanks := st.portRanks.set! pid v }

/-- `port_ranks.get(pid).unwrap_or(0.0)`. -/
@[inline] def rankOf (st : BarycenterPortDistributorState) (pid : Nat) : Float := st.portRanks.get! pid

/-- `port_barycenter[pid] = v` (no-op out of range). -/
@[inline] def setBarycenter (st : BarycenterPortDistributorState) (pid : Nat) (v : Float) : BarycenterPortDistributorState :=
  { st with portBarycenter := st.portBarycenter.set! pid v }

/-- `port_barycenter.get(pid).unwrap_or(0.0)`. -/
@[inline] def barycenterOf (st : BarycenterPortDistributorState) (pid : Nat) : Float := st.portBarycenter.get! pid

/-- `node_positions.get(layer).and_then(|p| p.get(node)).unwrap_or(node)`. -/
@[inline] def positionIn (st : BarycenterPortDistributorState) (layerIndex nodeIndex : Nat) : Nat :=
  if h : layerIndex < st.nodePositions.size then
    let positions := st.nodePositions[layerIndex]
    if h2 : nodeIndex < positions.size then positions[nodeIndex] else nodeIndex
  else nodeIndex

/-- Ensures capacity for the largest of `pids` (the snapshot rank paths). -/
def ensureForAll (st : BarycenterPortDistributorState) (pids : Array Nat) : BarycenterPortDistributorState :=
  match pids[0]? with
  | some first => st.ensurePortCapacity (pids.foldl max first)
  | none => st

end BarycenterPortDistributorState

open BarycenterPortDistributorState

/-! ## Port ranks -/

/-! ### Snapshot path

The node's *current* ports mapped to captured ids (`ports.map s.portId` in elk-rs), walked in
place by tail-recursive loops. -/

/-- Whether the captured port has incoming edges with a source (`port_predecessors` non-empty). -/
@[inline] def hasPredecessors (s : CrossMinSnapshot) (pid : Nat) : Bool :=
  if h : pid < s.portIns.size then !s.portIns[pid].isEmpty else false

/-- Whether the captured port has outgoing edges with a target (`port_successors` non-empty). -/
@[inline] def hasSuccessors (s : CrossMinSnapshot) (pid : Nat) : Bool :=
  if h : pid < s.portOuts.size then !s.portOuts[pid].isEmpty else false

/-- Whether the captured port lies on the north side. -/
@[inline] def isNorthPort (s : CrossMinSnapshot) (pid : Nat) : Bool :=
  if h : pid < s.portSides.size then sideIs s.portSides[pid] .north else false

/-- The largest captured id of `ports[i:]` (at least `acc`). -/
partial def maxPortIdFrom (s : CrossMinSnapshot) (ports : Array LPortId) (i acc : Nat) : Nat :=
  if h : i < ports.size then maxPortIdFrom s ports (i + 1) (max acc (s.portId ports[i])) else acc

/-- Number of ports of `ports[i:]` with predecessors (`north`: only northern ones). -/
partial def countWithPredecessors (s : CrossMinSnapshot) (ports : Array LPortId) (north : Bool) (i acc : Nat) : Nat :=
  if h : i < ports.size then
    let pid := s.portId ports[i]
    let counts := hasPredecessors s pid && (!north || isNorthPort s pid)
    countWithPredecessors s ports north (i + 1) (if counts then acc + 1 else acc)
  else acc

/-- Number of ports of `ports[i:]` with successors. -/
partial def countWithSuccessors (s : CrossMinSnapshot) (ports : Array LPortId) (i acc : Nat) : Nat :=
  if h : i < ports.size then
    countWithSuccessors s ports (i + 1) (if hasSuccessors s (s.portId ports[i]) then acc + 1 else acc)
  else acc

/-- The input rank assignment of both strategies: northern ports get `northPos` (then
`- step`), the others `restPos` (then `- step`). -/
partial def assignInputRanks (s : CrossMinSnapshot) (ports : Array LPortId) (i : Nat) (step northPos restPos : Float)
    (ranks : FloatArray) : FloatArray :=
  if h : i < ports.size then
    let pid := s.portId ports[i]
    if hasPredecessors s pid then
      if isNorthPort s pid then
        assignInputRanks s ports (i + 1) step (northPos - step) restPos (ranks.set! pid (f32t northPos))
      else
        assignInputRanks s ports (i + 1) step northPos (restPos - step) (ranks.set! pid (f32t restPos))
    else assignInputRanks s ports (i + 1) step northPos restPos ranks
  else ranks

/-- The node-relative output rank assignment: `pos`, then `+ incr`. -/
partial def assignOutputRanksNodeRelative (s : CrossMinSnapshot) (ports : Array LPortId) (i : Nat) (incr pos : Float)
    (ranks : FloatArray) : FloatArray :=
  if h : i < ports.size then
    let pid := s.portId ports[i]
    if hasSuccessors s pid then
      assignOutputRanksNodeRelative s ports (i + 1) incr (pos + incr) (ranks.set! pid (f32t pos))
    else assignOutputRanksNodeRelative s ports (i + 1) incr pos ranks
  else ranks

/-- The layer-total output rank assignment: `rankSum + pos` with `pos` counting from `1`. -/
partial def assignOutputRanksLayerTotal (s : CrossMinSnapshot) (ports : Array LPortId) (i : Nat) (rankSum pos : Float)
    (ranks : FloatArray) : FloatArray :=
  if h : i < ports.size then
    let pid := s.portId ports[i]
    if hasSuccessors s pid then
      let pos := pos + 1.0
      assignOutputRanksLayerTotal s ports (i + 1) rankSum pos (ranks.set! pid (f32t (rankSum + pos)))
    else assignOutputRanksLayerTotal s ports (i + 1) rankSum pos ranks
  else ranks

/-- The port counts of a node for the rank computation: inputs (ports with predecessors), northern
inputs, outputs (ports with successors) and the largest captured id `+ 1`. -/
structure RankCounts where
  inputs : Nat
  northInputs : Nat
  outputs : Nat
  maxIdPlusOne : Nat

/-- The `RankCounts` of the node's current `ports`. A node without nested graph only ever has its
captured ports (in some order: the distributor sorts them), so its counts are the snapshot's; the
port list of a hierarchical node can be rewritten (`sortPortsByDummyPositionsInLastLayer`), so it is
counted. -/
@[inline] def rankCounts (s : CrossMinSnapshot) (node : LNodeId) (ports : Array LPortId) : RankCounts :=
  let flat1 := s.nodeMap.get node.idx
  let flat := flat1 - 1
  if flat1 != 0 && !s.nodeHasNestedGraph flat && flat < s.nodeMaxPortIds.size then
    { inputs := s.nodeInputCounts[flat]!, northInputs := s.nodeNorthInputCounts[flat]!,
      outputs := s.nodeOutputCounts[flat]!, maxIdPlusOne := s.nodeMaxPortIds[flat]! }
  else
    { inputs := countWithPredecessors s ports false 0 0, northInputs := countWithPredecessors s ports true 0 0,
      outputs := countWithSuccessors s ports 0 0,
      maxIdPlusOne := if h : 0 < ports.size then maxPortIdFrom s ports 1 (s.portId ports[0]) + 1 else 0 }

/-- `ensure_port_capacity` for the largest captured id of the node's ports (`ensureForAll`). -/
@[inline] def ensureForCounts (k : RankCounts) (st : BarycenterPortDistributorState) : BarycenterPortDistributorState :=
  if k.maxIdPlusOne == 0 then st else st.ensurePortCapacity (k.maxIdPlusOne - 1)

/-- `calculate_port_ranks_node_relative`, snapshot path, on the node's current `ports`: the
updated state (the node consumes rank `1`). -/
def ranksNodeRelativeSnap (s : CrossMinSnapshot) (k : RankCounts) (ports : Array LPortId)
    (st : BarycenterPortDistributorState) (rankSum : Float) (portType : PortType) : BarycenterPortDistributorState :=
  let st := ensureForCounts k st
  match portType with
  | .input =>
    if k.inputs == 0 then st
    else
      let incr := 1.0 / (k.inputs.toFloat + 1.0)
      let ranks := assignInputRanks s ports 0 incr (rankSum + k.northInputs.toFloat * incr) (rankSum + 1.0 - incr)
        st.portRanks
      { st with portRanks := ranks }
  | .output =>
    if k.outputs == 0 then st
    else
      let incr := 1.0 / (k.outputs.toFloat + 1.0)
      { st with portRanks := assignOutputRanksNodeRelative s ports 0 incr (rankSum + incr) st.portRanks }
  | .undefined => st

/-- `calculate_port_ranks_layer_total`, snapshot path, on the node's current `ports`. -/
def ranksLayerTotalSnap (s : CrossMinSnapshot) (k : RankCounts) (ports : Array LPortId)
    (st : BarycenterPortDistributorState) (rankSum : Float) (portType : PortType) : BarycenterPortDistributorState :=
  let st := ensureForCounts k st
  match portType with
  | .input =>
    if k.inputs == 0 then st
    else
      let ranks := assignInputRanks s ports 0 1.0 (rankSum + k.northInputs.toFloat) (rankSum + k.inputs.toFloat)
        st.portRanks
      { st with portRanks := ranks }
  | .output => { st with portRanks := assignOutputRanksLayerTotal s ports 0 rankSum 0.0 st.portRanks }
  | .undefined => st

/-- The rank consumed by a node in the snapshot path (`1` node-relative; layer-total: the
number of input ports with predecessors, resp. output ports with successors). -/
@[inline] def consumedRankOf (strategy : PortRankStrategy) (k : RankCounts) (portType : PortType) : Float :=
  match strategy, portType with
  | .nodeRelative, _ => 1.0
  | .layerTotal, .input => k.inputs.toFloat
  | .layerTotal, .output => k.outputs.toFloat
  | .layerTotal, .undefined => 0.0

/-- The rank consumed by a node in the snapshot path. -/
def consumedRankSnap (strategy : PortRankStrategy) (s : CrossMinSnapshot) (node : LNodeId) (ports : Array LPortId)
    (portType : PortType) : Float :=
  consumedRankOf strategy (rankCounts s node ports) portType

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

/-- `calculate_port_ranks_for_node(node, rank_sum, port_type)`: the updated state and the rank
consumed by the node. -/
def ranksForNode (strategy : PortRankStrategy) (snap : Option CrossMinSnapshot) (a : LGraphArena) (node : LNodeId)
    (st : BarycenterPortDistributorState) (rankSum : Float) (portType : PortType) : BarycenterPortDistributorState × Float :=
  match strategy, snap with
  | .nodeRelative, some s =>
    let ports := (a.node node).ports
    (ranksNodeRelativeSnap s (rankCounts s node ports) ports st rankSum portType, 1.0)
  | .nodeRelative, none => ranksNodeRelativeLock a node st rankSum portType
  | .layerTotal, some s =>
    let ports := (a.node node).ports
    let k := rankCounts s node ports
    (ranksLayerTotalSnap s k ports st rankSum portType, consumedRankOf .layerTotal k portType)
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

/-- `node_positions.get(layer).and_then(|p| p.get(node)).unwrap_or(node)` on the positions table. -/
@[inline] def positionInTable (positions : Array (Array Nat)) (layerIndex nodeIndex : Nat) : Nat :=
  if h : layerIndex < positions.size then
    let row := positions[layerIndex]
    if h2 : nodeIndex < row.size then row[nodeIndex] else nodeIndex
  else nodeIndex

/-- `position_of(node)` on the positions table (snapshot or live ids). -/
def positionOfIn (snap : Option CrossMinSnapshot) (a : LGraphArena) (positions : Array (Array Nat)) (node : LNodeId) : Nat :=
  match snap with
  | some s => positionInTable positions (s.nodeLayerIndex node) (s.nodeId node)
  | none =>
    let layerIndex := match (a.node node).layer with
      | some l => asUsize (a.layer l).id
      | none => 0
    positionInTable positions layerIndex (asUsize (a.node node).id)

/-- `position_of(node)`: `node_positions[layer index][node id]` (snapshot or live ids). -/
def positionOf (snap : Option CrossMinSnapshot) (a : LGraphArena) (st : BarycenterPortDistributorState) (node : LNodeId) : Nat :=
  positionOfIn snap a st.nodePositions node

/-- Whether the dummy port's `ORIGIN` is `port`. -/
@[inline] private def originIs (a : LGraphArena) (dummyPort port : LPortId) : Bool :=
  match (a.port dummyPort).internal.origin with
  | some (.lPort origin) => origin == port
  | _ => false

/-- `deal_with_north_south_ports(absurdly_large_float, port, port_dummy)`: the sort key of a
north/south port from the input/output role of its dummy's ports (on the positions table). -/
def dealWithNorthSouthPortsIn (snap : Option CrossMinSnapshot) (a : LGraphArena) (positions : Array (Array Nat))
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
    let pos := (positionOfIn snap a positions portDummy).toFloat
    return if side == .north then -pos else absurdlyLargeFloat - pos
  else if output && exclusive then
    return (positionOfIn snap a positions portDummy).toFloat + 1.0
  else if input && output then
    return if side == .north then 0.0 else absurdlyLargeFloat / 2.0
  else
    return 0.0

/-- `deal_with_north_south_ports(absurdly_large_float, port, port_dummy)`. -/
@[inline] def dealWithNorthSouthPorts (snap : Option CrossMinSnapshot) (a : LGraphArena) (st : BarycenterPortDistributorState)
    (absurdlyLargeFloat : Float) (port : LPortId) (portDummy : LNodeId) : Float :=
  dealWithNorthSouthPortsIn snap a st.nodePositions absurdlyLargeFloat port portDummy

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

/-- Whether a far end of `targets[i:]` lies in layer `nodeLayer` (Rust `continue 'port_iteration`). -/
partial def anyEndInLayer (s : CrossMinSnapshot) (targets : Array Nat) (nodeLayer i : Nat) : Bool :=
  if h : i < targets.size then
    if s.portOwnerLayer targets[i] == nodeLayer then true else anyEndInLayer s targets nodeLayer (i + 1)
  else false

/-- `f32` sum of the ranks of `targets[i:]` (`add`: added, else subtracted). -/
partial def rankSumOf (ranks : FloatArray) (targets : Array Nat) (add : Bool) (i : Nat) (sum : Float) : Float :=
  if h : i < targets.size then
    let r := f32t (ranks.get! targets[i])
    rankSumOf ranks targets add (i + 1) (if add then f32t (sum + r) else f32t (sum - r))
  else sum

/-- The port loop of `distribute_ports_for_iter_snap` over the captured ports `pids[i:]` on
`side`: barycenters (`bary`), the running min/max barycenter and the in-layer ports. The state is
split into its fields so that nothing is allocated per port; `ranks` and `bary` are only resized
together (`ensure_port_capacity`, which does not happen for the captured ids of the graph). -/
partial def iteratePortsSnapLoop (s : CrossMinSnapshot) (a : LGraphArena) (pids : Array Nat) (side : PortSide)
    (absurdlyLargeFloat : Float) (nodeLayer : Nat) (positions : Array (Array Nat)) (i : Nat)
    (ranks bary : FloatArray) (minB maxB : Float) (inLayer : Array Nat) : BarycenterPortDistributorState :=
  if h : i < pids.size then
    let pid := pids[i]
    let pside := s.portSideOf pid
    if !sideIs pside side then
      iteratePortsSnapLoop s a pids side absurdlyLargeFloat nodeLayer positions (i + 1) ranks bary minB maxB inLayer
    else
      let preds := s.portPredecessors pid
      let succs := s.portSuccessors pid
      let northSouth := sideIs pside .north || sideIs pside .south
      -- the sum, or `none` to skip the port (no dummy) / collect it (in-layer)
      let sum? : Option Float :=
        if northSouth then
          match s.portRefOpt pid with
          | none => none
          | some portRef =>
            match (a.port portRef).internal.portDummy with
            | none => none
            | some dummy =>
              -- Rust: `self.snapshot` is taken while distributing, so the lock path runs
              some (f32t (floatZero + f32t (dealWithNorthSouthPortsIn none a positions absurdlyLargeFloat portRef dummy)))
        else if anyEndInLayer s succs nodeLayer 0 || anyEndInLayer s preds nodeLayer 0 then none
        else some (rankSumOf ranks preds false 0 (rankSumOf ranks succs true 0 floatZero))
      match sum? with
      | none =>
        let inLayer := if northSouth then inLayer else inLayer.push pid
        iteratePortsSnapLoop s a pids side absurdlyLargeFloat nodeLayer positions (i + 1) ranks bary minB maxB inLayer
      | some sum =>
        -- `ensure_port_capacity(pid)`
        let grow := pid >= ranks.size && pid >>> 32 == 0
        let ranks := if grow then resizeFloats ranks (pid + 1) else ranks
        let bary := if grow then resizeFloats bary (pid + 1) else bary
        let degree := preds.size + succs.size
        if degree > 0 then
          let value := f32t (sum / f32t degree.toUInt64.toFloat)
          iteratePortsSnapLoop s a pids side absurdlyLargeFloat nodeLayer positions (i + 1) ranks (bary.set! pid value)
            (fminInline minB value) (fmaxInline maxB value) inLayer
        else if northSouth then
          iteratePortsSnapLoop s a pids side absurdlyLargeFloat nodeLayer positions (i + 1) ranks (bary.set! pid sum)
            minB maxB inLayer
        else
          iteratePortsSnapLoop s a pids side absurdlyLargeFloat nodeLayer positions (i + 1) ranks bary minB maxB inLayer
  else { portRanks := ranks, portBarycenter := bary, nodePositions := positions, minBarycenter := minB,
         maxBarycenter := maxB, inLayerPortIds := inLayer }

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

/-- `distribute_ports_for_iter_snap(node, port_ids, node_id, layer_index, layer_size)` for the
captured ports `portIds` on `side` (Rust partitions them into a buffer first; without such ports
nothing changes). -/
def distributePortsForSideSnap (s : CrossMinSnapshot) (a : LGraphArena) (st : BarycenterPortDistributorState)
    (node : LNodeId) (flat : Nat) (portIds : Array Nat) (side : PortSide) (nodeId : Int) (layerIndex layerSize : Nat) :
    BarycenterPortDistributorState :=
  if s.nodeSideMask flat &&& sideBit side == 0 then st
  else
    match st with
    | { portRanks, nodePositions, portBarycenter, nPorts, .. } =>
      let st := iteratePortsSnapLoop s a portIds side (f32t (2 * layerSize + 1).toFloat) (s.nodeLayerIndex node)
        nodePositions 0 portRanks portBarycenter floatZero floatZero #[]
      let st := { st with nPorts }
      if st.inLayerPortIds.isEmpty then st
      else
        let inLayer := st.inLayerPortIds
        let minB := st.minBarycenter
        let maxB := st.maxBarycenter
        inLayerPortsSnap s { st with inLayerPortIds := #[] } node nodeId layerIndex layerSize inLayer minB maxB

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

/-- The `sort_ports` comparator: by side, then `compareBarycenters` of the ports' barycenters. -/
@[inline] def comparePortsBySideAndBarycenter (a : LGraphArena) (bary : FloatArray) (p q : LPortId) : Ordering :=
  let pt := a.port p
  let qt := a.port q
  let s1 := sideCode pt.side
  let s2 := sideCode qt.side
  if s1 != s2 then compare s1 s2
  else compareBarycenters (bary.get! (asUsize pt.id)) (bary.get! (asUsize qt.id))

/-- Whether `ports[i:]` is already ordered by `comparePortsBySideAndBarycenter` with no NaN barycenter,
given the side code and barycenter of `ports[i - 1]`. Without NaN the comparator is a total
preorder, so the stable sort returns such a list unchanged. -/
partial def portsSortedFrom (a : LGraphArena) (bary : FloatArray) (ports : Array LPortId) (i : Nat)
    (prevSide : UInt8) (prevBary : Float) : Bool :=
  if h : i < ports.size then
    let pt := a.port ports[i]
    let side := sideCode pt.side
    let b := bary.get! (asUsize pt.id)
    if b != b then false
    else
      let ord := if prevSide != side then compare prevSide side else compareBarycenters prevBary b
      if ord == .gt then false else portsSortedFrom a bary ports (i + 1) side b
  else true

/-- Whether `ports` is already ordered (see `portsSortedFrom`). -/
def portsSorted (a : LGraphArena) (bary : FloatArray) (ports : Array LPortId) : Bool :=
  if h : 0 < ports.size then
    let pt := a.port ports[0]
    let b := bary.get! (asUsize pt.id)
    if b != b then false else portsSortedFrom a bary ports 1 (sideCode pt.side) b
  else true

/-- `sort_ports(node)` (lock path): the current ports sorted by (side, barycenter, index). The
stable sort only ever compares an element with one that was before it in the input, so the index
tie-break never decides and the ports are sorted directly by (side, barycenter); an already sorted
list is returned as it is. -/
def sortPortsLock (a : LGraphArena) (st : BarycenterPortDistributorState) (node : LNodeId) : Array LPortId :=
  let ports := (a.node node).ports
  let bary := st.portBarycenter
  if ports.size < 2 || portsSorted a bary ports then ports
  else stableSortSmall ports (comparePortsBySideAndBarycenter a bary)

/-- Whether ports `xs[i:]` and `ys[i:]` are the same. -/
partial def samePortsFrom (xs ys : Array LPortId) (i : Nat) : Bool :=
  if h : i < xs.size then
    if h2 : i < ys.size then xs[i].idx == ys[i].idx && samePortsFrom xs ys (i + 1) else false
  else true

/-- Whether two port lists are the same. -/
@[inline] def samePorts (xs ys : Array LPortId) : Bool := xs.size == ys.size && samePortsFrom xs ys 0

/-- End of the maximal run of ports on `side` starting before `j`. -/
partial def runEnd (a : LGraphArena) (ports : Array LPortId) (side : PortSide) (j : Nat) : Nat :=
  if h : j < ports.size then
    if sideIs (a.port ports[j]).side side then runEnd a ports side (j + 1) else j
  else j

/-- The final test of `runsMatch`: per side ordinal `o ≥ k`, a side with a run must have matched its
last run, a side without one must have no cached entry. -/
partial def sidesMatch (idx : Array (Option (Nat × Nat))) (k : Nat) (seen bad : UInt8) : Bool :=
  if k < 5 then
    let bit : UInt8 := (1 : UInt8) <<< k.toUInt8
    let ok := if seen &&& bit != 0 then bad &&& bit == 0
      else match idx[k]? with
        | some none => true
        | _ => false
    ok && sidesMatch idx (k + 1) seen bad
  else true

/-- Whether `LNode.findPortIndices()` of `ports` equals `idx`: walks the maximal side runs from
`ports[i]` (the entry of a side is its last run), `seen`/`bad` flag the sides with a run and those
whose last run so far does not match. -/
partial def runsMatch (a : LGraphArena) (ports : Array LPortId) (idx : Array (Option (Nat × Nat))) (i : Nat)
    (seen bad : UInt8) : Bool :=
  if h : i < ports.size then
    let side := (a.port ports[i]).side
    let o := ElkEnum.ordinal side
    let l := runEnd a ports side (i + 1)
    let ok := match idx[o]? with
      | some (some (first, last)) => first == i && last == l
      | _ => false
    let bit : UInt8 := (1 : UInt8) <<< o.toUInt8
    runsMatch a ports idx l (seen ||| bit) (if ok then bad &&& ~~~bit else bad ||| bit)
  else sidesMatch idx 0 seen bad

/-- Whether `cachePortSides()` on a node with port list `ports` would leave its cache unchanged:
the cache is enabled and its stored indices equal `findPortIndices()` of `ports`. -/
def portSideCacheMatches (a : LGraphArena) (nd : LNode) (ports : Array LPortId) : Bool :=
  if !nd.portSidesCached then false
  else match nd.portSideIndices with
    | none => false
    | some idx => idx.size == 5 && runsMatch a ports idx 0 0 0

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

/-- `port_ranks()` (shared until the next update). -/
def portRanksF (d : AbstractBarycenterPortDistributor) : BaseIO FloatArray := do
  return (← d.state.get).portRanks

/-- `port_ranks()` (a copy). -/
def portRanks (d : AbstractBarycenterPortDistributor) : BaseIO (Array Float) := do
  return (← d.state.get).portRanks.data

/-- `port_barycenter` (a copy; testing/debugging). -/
def portBarycenters (d : AbstractBarycenterPortDistributor) : BaseIO (Array Float) := do
  return (← d.state.get).portBarycenter.data

/-- The node loop of `calculate_port_ranks` in the snapshot path. -/
partial def calculatePortRanksSnapLoop (strategy : PortRankStrategy) (s : CrossMinSnapshot) (a : LGraphArena)
    (layer : Array LNodeId) (portType : PortType) (i : Nat) (rankSum : Float) (st : BarycenterPortDistributorState) :
    BarycenterPortDistributorState :=
  if h : i < layer.size then
    let node := layer[i]
    let ports := (a.node node).ports
    let k := rankCounts s node ports
    let st := match strategy with
      | .nodeRelative => ranksNodeRelativeSnap s k ports st rankSum portType
      | .layerTotal => ranksLayerTotalSnap s k ports st rankSum portType
    calculatePortRanksSnapLoop strategy s a layer portType (i + 1) (rankSum + consumedRankOf strategy k portType) st
  else st

/-- `calculate_port_ranks(layer, port_type)` on an explicit state. -/
def calculatePortRanksPure (strategy : PortRankStrategy) (snap : Option CrossMinSnapshot) (a : LGraphArena)
    (st : BarycenterPortDistributorState) (layer : Array LNodeId) (portType : PortType) : BarycenterPortDistributorState :=
  match snap with
  | some s => calculatePortRanksSnapLoop strategy s a layer portType 0 0.0 st
  | none => Id.run do
    let mut st := st
    let mut consumedRank : Float := 0.0
    for node in layer do
      let (st', consumed) := ranksForNode strategy none a node st consumedRank portType
      st := st'
      consumedRank := consumedRank + consumed
    return st

/-- `calculate_port_ranks(layer, port_type)` on an explicit state. -/
def calculatePortRanksOn (d : AbstractBarycenterPortDistributor) (st : BarycenterPortDistributorState)
    (layer : Array LNodeId) (portType : PortType) : LayeredM BarycenterPortDistributorState := do
  return calculatePortRanksPure d.strategy (← d.snapshot.get) (← get) st layer portType

/-- `calculate_port_ranks(layer, port_type)`: ranks of the layer's ports of the given type,
written to the rank array. -/
def calculatePortRanks (d : AbstractBarycenterPortDistributor) (layer : Array LNodeId) (portType : PortType) :
    LayeredM Unit := do
  let st ← d.state.swap {}
  let st ← d.calculatePortRanksOn st layer portType
  d.state.set st

/-- Writes a sorted port list (`*ports_mut() = ports; cache_port_sides()`). The node is left
untouched when the list and its side cache would not change, and the cache is not recomputed when
it already matches the new list. -/
private def setPorts (node : LNodeId) (ports : Array LPortId) : LayeredM Unit := do
  let a ← get
  let nd := a.node node
  let samePortList := samePorts nd.ports ports
  let cacheMatches := portSideCacheMatches a nd ports
  if samePortList && cacheMatches then return
  if cacheMatches then
    modifyNode node fun x => { x with ports := ports }
  else
    modifyNode node fun x => { x with ports := ports }
    cachePortSides node

/-- `distribute_ports_snap(node, side, layer_index, layer_size)`. -/
private def distributePortsSnap (s : CrossMinSnapshot) (st : BarycenterPortDistributorState) (node : LNodeId)
    (side : PortSide) (layerIndex layerSize : Nat) : LayeredM BarycenterPortDistributorState := do
  let a ← get
  let constraints := (a.node node).props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  if constraints.isOrderFixed then return st
  let flat := s.nodeFlatIndex node
  let nodeId := toI32 (s.nodeGraphIdOf flat)
  let portIds := s.nodePorts flat
  let st := distributePortsForSideSnap s a st node flat portIds side nodeId layerIndex layerSize
  let st := distributePortsForSideSnap s a st node flat portIds .south nodeId layerIndex layerSize
  let st := distributePortsForSideSnap s a st node flat portIds .north nodeId layerIndex layerSize
  -- Rust `sort_ports(node)` runs while `distribute_ports` holds the snapshot taken out of
  -- `self.snapshot`, so its lock fallback sorts the *current* port order (index tie-break)
  let sorted := sortPortsLock a st node
  setPorts node sorted
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

/-- The loop of `update_node_positions`: `positions[node id] := index` for `layer[index:]`. -/
partial def updateNodePositionsLoop (snap : Option CrossMinSnapshot) (a : LGraphArena) (layer : Array LNodeId)
    (index : Nat) (positions : Array Nat) : Array Nat :=
  if h : index < layer.size then
    let node := layer[index]
    let nid := match snap with
      | some s => s.nodeId node
      | none => asUsize (a.node node).id
    let positions := if nid >= positions.size && nid >>> 32 == 0 then
        positions ++ Array.replicate (nid + 1 - positions.size) 0
      else positions
    updateNodePositionsLoop snap a layer (index + 1) (positions.setIfInBounds nid index)
  else positions

/-- `update_node_positions(node_order, current_index)`. -/
def updateNodePositions (snap : Option CrossMinSnapshot) (a : LGraphArena) (st : BarycenterPortDistributorState)
    (order : Array (Array LNodeId)) (currentIndex : Nat) : BarycenterPortDistributorState :=
  if currentIndex < st.nodePositions.size then
    let layer := order[currentIndex]?.getD #[]
    { st with nodePositions := st.nodePositions.modify currentIndex (updateNodePositionsLoop snap a layer 0 ·) }
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
    portRanks := zeros st.nPorts, portBarycenter := zeros st.nPorts }

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
