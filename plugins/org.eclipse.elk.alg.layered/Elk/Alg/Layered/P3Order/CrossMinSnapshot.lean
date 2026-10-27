import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
import Std.Data.HashMap
/-!
# elk-rs `p3order/cross_min_snapshot.rs` (no Java counterpart)

elk-rs builds this flat, index-based snapshot of the current node order after the
`IInitializable`s assigned all ids, and uses it for lock-free lookups during crossing
minimisation. In Lean the arena is read directly (PORTING.md §15.1), but the snapshot's flat
node indices and captured ids are observable (e.g. `SweepCopy`), so it is kept as a pure
structure with the same API. All values are captured at build time.

Index spaces: the *flat node index* numbers the nodes of `order` layer by layer; a *port id*
is the port's `LPort.id` (Rust `graph_element().id as u32`), expected in `[0, nPorts)`. The
CSR arrays of the Rust version are plain nested arrays here.

The node → flat index and port → port id maps (Rust `FxHashMap`s keyed by `Arc` addresses) are
`IdIndex`es: dense arrays over the arena index range of the captured elements, or a hash map
when that range is much larger than the number of elements (nested graphs whose dummies were
created late).

Lean-only precomputed values (no Rust counterpart; all derived from the captured data):
`portFlags` (per port id: predecessors, successors, a far end in the owner's layer, side code) and
`nodeOrderFixed` (per flat node: `PORT_CONSTRAINTS.isOrderFixed` at build time). The crossing
minimisation only permutes the ports of a node without nested graph and changes neither port
ids, port sides, edges nor the `PORT_CONSTRAINTS` of such a node (only the parent node of a nested
graph gets `FIXED_ORDER` and a rewritten port list), so for these nodes the captured values equal
the live ones while the snapshot is used.
-/
namespace Elk.Alg.Layered.P3Order

open Elk Elk.Core.Options Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- The bit of a side in a side mask (`1 <<< ElkEnum.ordinal side`). -/
@[inline] def sideBit : PortSide → UInt8
  | .undefined => 1
  | .north => 2
  | .east => 4
  | .south => 8
  | .west => 16

/-- Rust `x as u32` of an `i32` id: `(v % 2^32).toNat`, computed in `UInt32` (`2^32` is not a
small `Int`, so `%` by it would run through GMP). -/
@[inline] private def toU32 (v : Int) : Nat :=
  match v with
  | .ofNat n => n.toUInt32.toNat
  | .negSucc m => ((0 : UInt32) - (m + 1).toUInt32).toNat

/-- A map from arena indices to `Nat` values: `get i` is `value + 1`, or `0` for absent keys. -/
structure IdIndex where
  /-- The smallest key (dense representation). -/
  base : Nat := 0
  /-- `value + 1` per key `base + i` (`0`: absent). -/
  dense : Array Nat := #[]
  /-- The map of the sparse representation. -/
  sparse : Std.HashMap Nat Nat := {}
  /-- Whether `dense` is used. -/
  isDense : Bool := true
  deriving Inhabited

namespace IdIndex

/-- Builds the index of `(key, value)` pairs (a later pair overrides an earlier one with the same key,
like `HashMap.insert`). -/
def ofPairs (keys values : Array Nat) : IdIndex := Id.run do
  if keys.isEmpty then return {}
  let mut lo := keys[0]!
  let mut hi := keys[0]!
  for k in keys do
    if k < lo then lo := k
    if k > hi then hi := k
  let range := hi + 1 - lo
  if range <= 4 * keys.size + 1024 then
    let mut dense := Array.replicate range 0
    for h : i in [0:keys.size] do
      dense := dense.set! (keys[i] - lo) (values[i]! + 1)
    return { base := lo, dense, isDense := true }
  else
    let mut sparse : Std.HashMap Nat Nat := {}
    for h : i in [0:keys.size] do
      sparse := sparse.insert keys[i] values[i]!
    return { sparse, isDense := false }

/-- `value + 1` of key `k`, `0` when absent. -/
@[inline] def get (m : IdIndex) (k : Nat) : Nat :=
  if m.isDense then
    if k >= m.base then
      let i := k - m.base
      if h : i < m.dense.size then m.dense[i] else 0
    else 0
  else
    match m.sparse[k]? with
    | some v => v + 1
    | none => 0

end IdIndex

/-- `CrossMinSnapshot`. -/
structure CrossMinSnapshot where
  /-- node → flat node index. -/
  nodeMap : IdIndex := {}
  /-- port → port id (captured `LPort.id`). -/
  portMap : IdIndex := {}
  /-- per flat node: captured `LNode.id` (its position in the layer). -/
  nodeGraphIds : Array Nat := #[]
  /-- per flat node: layer index. -/
  nodeLayers : Array Nat := #[]
  /-- per flat node: node type. -/
  nodeTypes : Array NodeType := #[]
  /-- per flat node: whether it has a nested graph. -/
  nodeNested : Array Bool := #[]
  /-- per flat node: port ids in port order. -/
  nodePortIds : Array (Array Nat) := #[]
  /-- per flat node: the sides of its captured ports (bit `ElkEnum.ordinal side`, Lean only). -/
  nodeSideMasks : Array UInt8 := #[]
  /-- per flat node: number of captured ports with predecessors (Lean only, rank precomputation). -/
  nodeInputCounts : Array Nat := #[]
  /-- per flat node: number of captured northern ports with predecessors. -/
  nodeNorthInputCounts : Array Nat := #[]
  /-- per flat node: number of captured ports with successors. -/
  nodeOutputCounts : Array Nat := #[]
  /-- per flat node: largest captured port id `+ 1` (`0` without ports). -/
  nodeMaxPortIds : Array Nat := #[]
  /-- per flat node: `PORT_CONSTRAINTS.isOrderFixed` at build time (`1`/`0`; Lean only). -/
  nodeOrderFixed : ByteArray := ByteArray.empty
  /-- per flat node: bit `0` (`1`) a predecessor, bit `1` (`2`) a successor of a captured port lies in
  the node's layer, bit `2` (`4`) the node has `BARYCENTER_ASSOCIATES` (not changed during the
  crossing minimisation) (Lean only). -/
  nodeEndFlags : ByteArray := ByteArray.empty
  /-- per flat node: number of predecessors of its captured ports (Lean only). -/
  nodePredCounts : Array Nat := #[]
  /-- per flat node: number of successors of its captured ports (Lean only). -/
  nodeSuccCounts : Array Nat := #[]
  /-- per port id: bit `0` (`1`) predecessors, bit `1` (`2`) successors, bit `2` (`4`) a far end in the
  owner's layer, bits `3..5` the side code (`ElkEnum.ordinal`) (Lean only). -/
  portFlags : ByteArray := ByteArray.empty
  /-- `portIns`/`portOuts` flattened (Lean only): the far ends of port id `p` are
  `endIds[endStart[p]:endStart[p + 1]]`, the predecessors before `endMid[p]`, then the successors. -/
  endIds : Array Nat := #[]
  /-- per port id (and one more entry): start of its far ends in `endIds`. -/
  endStart : Array Nat := #[0]
  /-- per port id: start of its successors in `endIds`. -/
  endMid : Array Nat := #[]
  /-- per port id: side. -/
  portSides : Array PortSide := #[]
  /-- per port id: flat index of the owner. -/
  portOwners : Array Nat := #[]
  /-- per port id: source port ids of the incoming edges. -/
  portIns : Array (Array Nat) := #[]
  /-- per port id: target port ids of the outgoing edges. -/
  portOuts : Array (Array Nat) := #[]
  /-- per flat node: the node. -/
  nodeRefs : Array LNodeId := #[]
  /-- per port id: the port. -/
  portRefs : Array (Option LPortId) := #[]
  /-- `n_nodes()`. -/
  nNodes : Nat := 0
  /-- `n_ports()`. -/
  nPorts : Nat := 0
  deriving Inhabited

namespace CrossMinSnapshot

/-- `CrossMinSnapshot::build(order, n_ports)` on an arena. -/
def ofArena (a : LGraphArena) (order : Array (Array LNodeId)) (nPorts : Nat) : CrossMinSnapshot := Id.run do
  let mut s : CrossMinSnapshot := {
    portSides := Array.replicate nPorts .undefined, portOwners := Array.replicate nPorts 0,
    portIns := Array.replicate nPorts #[], portOuts := Array.replicate nPorts #[],
    portRefs := Array.replicate nPorts none, nPorts := nPorts }
  let mut nodeKeys : Array Nat := #[]
  let mut nodeValues : Array Nat := #[]
  let mut portKeys : Array Nat := #[]
  let mut portValues : Array Nat := #[]
  let mut flat := 0
  for h : layerIndex in [0:order.size] do
    for node in order[layerIndex] do
      let nd := a.node node
      nodeKeys := nodeKeys.push node.idx
      nodeValues := nodeValues.push flat
      s := { s with
        nodeRefs := s.nodeRefs.push node,
        nodeGraphIds := s.nodeGraphIds.push (toU32 nd.id), nodeLayers := s.nodeLayers.push layerIndex,
        nodeTypes := s.nodeTypes.push nd.type, nodeNested := s.nodeNested.push nd.nestedGraph.isSome }
      let mut portIds : Array Nat := #[]
      for port in nd.ports do
        let pt := a.port port
        let pid := toU32 pt.id
        portKeys := portKeys.push port.idx
        portValues := portValues.push pid
        portIds := portIds.push pid
        if pid < nPorts then
          let preds := pt.incomingEdges.filterMap fun e => (a.edge e).source.map fun sp => toU32 (a.port sp).id
          let succs := pt.outgoingEdges.filterMap fun e => (a.edge e).target.map fun tp => toU32 (a.port tp).id
          let f := flat
          s := { s with
            portSides := s.portSides.set! pid pt.side, portOwners := s.portOwners.set! pid f,
            portRefs := s.portRefs.set! pid (some port),
            portIns := s.portIns.modify pid (fun l => if l.isEmpty then preds else l ++ preds),
            portOuts := s.portOuts.modify pid (fun l => if l.isEmpty then succs else l ++ succs) }
      s := { s with nodePortIds := s.nodePortIds.push portIds }
      flat := flat + 1
  -- the side masks of the final `port_side_of` values
  let masks := s.nodePortIds.map fun pids =>
    pids.foldl (fun m pid => m ||| sideBit (s.portSides[pid]?.getD .undefined)) (0 : UInt8)
  let hasIn (pid : Nat) : Bool := !(s.portIns[pid]?.getD #[]).isEmpty
  let hasOut (pid : Nat) : Bool := !(s.portOuts[pid]?.getD #[]).isEmpty
  let isNorth (pid : Nat) : Bool := (s.portSides[pid]?.getD .undefined) == .north
  let inCounts := s.nodePortIds.map fun pids => (pids.filter hasIn).size
  let northInCounts := s.nodePortIds.map fun pids => (pids.filter fun pid => hasIn pid && isNorth pid).size
  let outCounts := s.nodePortIds.map fun pids => (pids.filter hasOut).size
  let maxIds := s.nodePortIds.map fun pids => pids.foldl (fun m pid => max m (pid + 1)) 0
  -- Lean-only flags (see the module doc)
  let ownerLayer (pid : Nat) : Nat := s.nodeLayers[s.portOwners[pid]?.getD 0]?.getD 0
  let endInLayer (ends : Array Nat) (li : Nat) : Bool := ends.any fun e => ownerLayer e == li
  let mut portFlags := ByteArray.emptyWithCapacity nPorts
  for pid in [0:nPorts] do
    let ins := s.portIns[pid]?.getD #[]
    let outs := s.portOuts[pid]?.getD #[]
    let li := ownerLayer pid
    let hasIns : UInt8 := if ins.isEmpty then 0 else 1
    let hasOuts : UInt8 := if outs.isEmpty then 0 else 2
    let inLayer : UInt8 := if endInLayer outs li || endInLayer ins li then 4 else 0
    let sideOrd : UInt8 := (ElkEnum.ordinal (s.portSides[pid]?.getD .undefined)).toUInt8
    let f : UInt8 := hasIns ||| hasOuts ||| inLayer ||| (sideOrd <<< 3)
    portFlags := portFlags.push f
  let mut nodeOrderFixed := ByteArray.emptyWithCapacity flat
  let mut nodeEndFlags := ByteArray.emptyWithCapacity flat
  let mut predCounts : Array Nat := Array.emptyWithCapacity flat
  let mut succCounts : Array Nat := Array.emptyWithCapacity flat
  for h : f in [0:s.nodeRefs.size] do
    let nd := a.node s.nodeRefs[f]
    let fixed := (nd.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined).isOrderFixed
    nodeOrderFixed := nodeOrderFixed.push (if fixed then 1 else 0)
    let li := s.nodeLayers[f]?.getD 0
    let pids := s.nodePortIds[f]?.getD #[]
    let predInLayer := pids.any fun pid => endInLayer (s.portIns[pid]?.getD #[]) li
    let succInLayer := pids.any fun pid => endInLayer (s.portOuts[pid]?.getD #[]) li
    let assoc : UInt8 := if nd.internal.barycenterAssociates.isEmpty then 0 else 4
    nodeEndFlags := nodeEndFlags.push ((if predInLayer then 1 else 0) ||| (if succInLayer then 2 else 0) ||| assoc)
    predCounts := predCounts.push (pids.foldl (fun acc pid => acc + (s.portIns[pid]?.getD #[]).size) 0)
    succCounts := succCounts.push (pids.foldl (fun acc pid => acc + (s.portOuts[pid]?.getD #[]).size) 0)
  let mut endIds : Array Nat := #[]
  let mut endStart : Array Nat := Array.emptyWithCapacity (nPorts + 1)
  let mut endMid : Array Nat := Array.emptyWithCapacity nPorts
  for pid in [0:nPorts] do
    endStart := endStart.push endIds.size
    endIds := endIds ++ (s.portIns[pid]?.getD #[])
    endMid := endMid.push endIds.size
    endIds := endIds ++ (s.portOuts[pid]?.getD #[])
  endStart := endStart.push endIds.size
  return { s with nNodes := flat, nodeSideMasks := masks, nodeMap := IdIndex.ofPairs nodeKeys nodeValues,
                  nodeInputCounts := inCounts, nodeNorthInputCounts := northInCounts, nodeOutputCounts := outCounts,
                  nodeMaxPortIds := maxIds, nodeOrderFixed, nodeEndFlags, nodePredCounts := predCounts,
                  nodeSuccCounts := succCounts, portFlags, endIds, endStart, endMid,
                  portMap := IdIndex.ofPairs portKeys portValues }

/-- `CrossMinSnapshot::build(order, n_ports)`: built from the current arena. -/
def build (order : Array (Array LNodeId)) (nPorts : Nat) : LayeredM CrossMinSnapshot := do
  return ofArena (← get) order nPorts

/-- `port_id(port)`: the captured id (`0` for unknown ports). -/
@[inline] def portId (s : CrossMinSnapshot) (port : LPortId) : Nat := s.portMap.get port.idx - 1

/-- `node_id(node)`: the captured `LNode.id` (`0` for unknown nodes). -/
@[inline] def nodeId (s : CrossMinSnapshot) (node : LNodeId) : Nat :=
  match s.nodeMap.get node.idx with
  | 0 => 0
  | f + 1 => s.nodeGraphIds[f]?.getD 0

/-- `node_layer_index(node)` (`0` for unknown nodes). -/
@[inline] def nodeLayerIndex (s : CrossMinSnapshot) (node : LNodeId) : Nat :=
  match s.nodeMap.get node.idx with
  | 0 => 0
  | f + 1 => s.nodeLayers[f]?.getD 0

/-- `node_flat_index(node)` (`0` for unknown nodes). -/
@[inline] def nodeFlatIndex (s : CrossMinSnapshot) (node : LNodeId) : Nat := s.nodeMap.get node.idx - 1

/-- `same_layer(a, b)`. -/
@[inline] def sameLayer (s : CrossMinSnapshot) (a b : LNodeId) : Bool := s.nodeLayerIndex a == s.nodeLayerIndex b

/-- The sides of the captured ports of a flat node (`sideBit` mask; `0` out of range). -/
@[inline] def nodeSideMask (s : CrossMinSnapshot) (flatNode : Nat) : UInt8 :=
  if h : flatNode < s.nodeSideMasks.size then s.nodeSideMasks[flatNode] else 0

/-- `node_ports(flat)`: port ids of a node in port order (empty out of range; Rust panics). -/
@[inline] def nodePorts (s : CrossMinSnapshot) (flatNode : Nat) : Array Nat := s.nodePortIds[flatNode]?.getD #[]

/-- `port_predecessors(port_id)`. -/
@[inline] def portPredecessors (s : CrossMinSnapshot) (portId : Nat) : Array Nat := s.portIns[portId]?.getD #[]

/-- `port_successors(port_id)`. -/
@[inline] def portSuccessors (s : CrossMinSnapshot) (portId : Nat) : Array Nat := s.portOuts[portId]?.getD #[]

/-- `port_owner_flat(port_id)` (`0` out of range). -/
@[inline] def portOwnerFlat (s : CrossMinSnapshot) (portId : Nat) : Nat := s.portOwners[portId]?.getD 0

/-- `port_owner_layer(port_id)` (`0` out of range). -/
@[inline] def portOwnerLayer (s : CrossMinSnapshot) (portId : Nat) : Nat := s.nodeLayers[s.portOwnerFlat portId]?.getD 0

/-- `port_side_of(port_id)` (`UNDEFINED` out of range). -/
@[inline] def portSideOf (s : CrossMinSnapshot) (portId : Nat) : PortSide := s.portSides[portId]?.getD .undefined

/-- `node_has_nested_graph(flat)`. -/
@[inline] def nodeHasNestedGraph (s : CrossMinSnapshot) (flatNode : Nat) : Bool := s.nodeNested[flatNode]?.getD false

/-- `node_type_of(flat)` (`NORMAL` out of range). -/
@[inline] def nodeTypeOf (s : CrossMinSnapshot) (flatNode : Nat) : NodeType := s.nodeTypes[flatNode]?.getD .normal

/-- `node_graph_id_of(flat)`: the captured `LNode.id` (`0` out of range). -/
@[inline] def nodeGraphIdOf (s : CrossMinSnapshot) (flatNode : Nat) : Nat := s.nodeGraphIds[flatNode]?.getD 0

/-- `node_layer_of(flat)` (`0` out of range). -/
@[inline] def nodeLayerOf (s : CrossMinSnapshot) (flatNode : Nat) : Nat := s.nodeLayers[flatNode]?.getD 0

/-- `node_ref(flat)`: the node of a flat index (`⟨0⟩` out of range; Rust panics). -/
@[inline] def nodeRef (s : CrossMinSnapshot) (flatNode : Nat) : LNodeId := s.nodeRefs[flatNode]?.getD default

/-- `port_ref_opt(port_id)`. -/
@[inline] def portRefOpt (s : CrossMinSnapshot) (portId : Nat) : Option LPortId := (s.portRefs[portId]?).bind id

/-- The range `[lo, hi)` of the far ends of a port id in `endIds` (`lo = hi` out of range). -/
@[inline] def endLo (s : CrossMinSnapshot) (portId : Nat) : Nat :=
  if portId < s.endMid.size then s.endStart[portId]! else 0

/-- See `endLo`. -/
@[inline] def endHi (s : CrossMinSnapshot) (portId : Nat) : Nat :=
  if portId < s.endMid.size then s.endStart[portId + 1]! else 0

/-- The end of the predecessors (start of the successors) of a port id in `endIds`. -/
@[inline] def endSplit (s : CrossMinSnapshot) (portId : Nat) : Nat :=
  if h : portId < s.endMid.size then s.endMid[portId] else 0

/-- The `portFlags` of a port id (`0` out of range: no edges, side `UNDEFINED`). -/
@[inline] def portFlag (s : CrossMinSnapshot) (portId : Nat) : UInt8 :=
  if h : portId < s.portFlags.size then s.portFlags[portId] else 0

/-- Whether a flat node's `PORT_CONSTRAINTS` fixed the port order at build time. -/
@[inline] def nodeOrderFixedAt (s : CrossMinSnapshot) (flatNode : Nat) : Bool :=
  if h : flatNode < s.nodeOrderFixed.size then s.nodeOrderFixed[flatNode] != 0 else false

/-- The `nodeEndFlags` of a flat node (`0` out of range). -/
@[inline] def nodeEndFlag (s : CrossMinSnapshot) (flatNode : Nat) : UInt8 :=
  if h : flatNode < s.nodeEndFlags.size then s.nodeEndFlags[flatNode] else 0

end CrossMinSnapshot

end Elk.Alg.Layered.P3Order
