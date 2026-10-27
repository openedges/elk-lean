import Elk.Alg.Layered.Graph
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
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Options Elk.Alg.Layered.Graph

/-- Rust `x as u32` of an `i32` id. -/
@[inline] private def toU32 (v : Int) : Nat := (v % 4294967296).toNat

/-- `CrossMinSnapshot`. -/
structure CrossMinSnapshot where
  /-- node → flat node index. -/
  nodeMap : Std.HashMap LNodeId Nat := {}
  /-- port → port id (captured `LPort.id`). -/
  portMap : Std.HashMap LPortId Nat := {}
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
  let mut flat := 0
  for h : layerIndex in [0:order.size] do
    for node in order[layerIndex] do
      let nd := a.node node
      s := { s with
        nodeMap := s.nodeMap.insert node flat, nodeRefs := s.nodeRefs.push node,
        nodeGraphIds := s.nodeGraphIds.push (toU32 nd.id), nodeLayers := s.nodeLayers.push layerIndex,
        nodeTypes := s.nodeTypes.push nd.type, nodeNested := s.nodeNested.push nd.nestedGraph.isSome }
      let mut portIds : Array Nat := #[]
      for port in nd.ports do
        let pt := a.port port
        let pid := toU32 pt.id
        s := { s with portMap := s.portMap.insert port pid }
        portIds := portIds.push pid
        if pid < nPorts then
          let preds := pt.incomingEdges.filterMap fun e => (a.edge e).source.map fun sp => toU32 (a.port sp).id
          let succs := pt.outgoingEdges.filterMap fun e => (a.edge e).target.map fun tp => toU32 (a.port tp).id
          let f := flat
          s := { s with
            portSides := s.portSides.set! pid pt.side, portOwners := s.portOwners.set! pid f,
            portRefs := s.portRefs.set! pid (some port),
            portIns := s.portIns.modify pid (· ++ preds), portOuts := s.portOuts.modify pid (· ++ succs) }
      s := { s with nodePortIds := s.nodePortIds.push portIds }
      flat := flat + 1
  return { s with nNodes := flat }

/-- `CrossMinSnapshot::build(order, n_ports)`: built from the current arena. -/
def build (order : Array (Array LNodeId)) (nPorts : Nat) : LayeredM CrossMinSnapshot := do
  return ofArena (← get) order nPorts

/-- `port_id(port)`: the captured id (`0` for unknown ports). -/
@[inline] def portId (s : CrossMinSnapshot) (port : LPortId) : Nat := s.portMap[port]?.getD 0

/-- `node_id(node)`: the captured `LNode.id` (`0` for unknown nodes). -/
@[inline] def nodeId (s : CrossMinSnapshot) (node : LNodeId) : Nat :=
  match s.nodeMap[node]? with
  | some f => s.nodeGraphIds[f]?.getD 0
  | none => 0

/-- `node_layer_index(node)` (`0` for unknown nodes). -/
@[inline] def nodeLayerIndex (s : CrossMinSnapshot) (node : LNodeId) : Nat :=
  match s.nodeMap[node]? with
  | some f => s.nodeLayers[f]?.getD 0
  | none => 0

/-- `node_flat_index(node)` (`0` for unknown nodes). -/
@[inline] def nodeFlatIndex (s : CrossMinSnapshot) (node : LNodeId) : Nat := s.nodeMap[node]?.getD 0

/-- `same_layer(a, b)`. -/
@[inline] def sameLayer (s : CrossMinSnapshot) (a b : LNodeId) : Bool := s.nodeLayerIndex a == s.nodeLayerIndex b

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

end CrossMinSnapshot

end Elk.Alg.Layered.P3Order
