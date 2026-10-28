import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.P3Order.CrossMinSnapshot
import Elk.Alg.Layered.Intermediate.PortListSorter
import Elk.Core.Util.JavaSort
import Elk.Core.Exceptions
/-!
# `org.eclipse.elk.alg.layered.p3order.SweepCopy`

A copy of the node order and of the port order of every node, taken after a sweep and written
back to the graph for the best sweep (elk-rs `sweep_copy.rs`). elk-rs stores `CrossMinSnapshot`
indices: per layer the *flat node indices*, per node the *port ids* (captured `LPort.id`s), and
maps them back with `snapshot.nodeRef`/`portRefOpt` when the copy is used. Here the copy keeps the
node and port *lists* themselves (the arrays are shared with the current order and the arena, so a
copy costs one pointer per node instead of one lookup per port) together with the snapshot, and
applies the same round trip (`nodeRef ∘ nodeFlatIndex`, `portRefOpt ∘ portId`, which is the
identity for the captured elements) where the indices are read. `nodeIndices`/`portOrders` give
the elk-rs index form. It is a pure value (`copyFromSweep` is the source itself).

## API (for `GraphInfoHolder`/`LayerSweepCrossingMinimizer`)
* `SweepCopy.new order snapshot : LayeredM SweepCopy` (`ofArena` is the pure form);
  `copyFrom` is `new` (Rust reuses the allocations), `copyFromSweep _ source = source`.
* `nodeIndices`: the flat node indices per layer; `nodeRefs`: the nodes they map back to.
* `transferNodeAndPortOrdersToGraph sc graph setPortConstraints snapshot` (Rust
  `transfer_node_and_port_orders_to_graph`; the `_guard` variant is the same in Lean).

## `transferNodeAndPortOrdersToGraph`
For every layer `i` of the graph and every saved node `j` of layer `i`: `node.id := j`, the node's
ports are replaced by the saved ones (port ids without port are dropped), with
`setPortConstraints` an order that is not fixed becomes `FIXED_ORDER`, and the layer slot `j` is
overwritten (or appended). The port side cache is not refreshed (Rust). After a layer, every
`NORTH_SOUTH_PORT` dummy of it corrects the side of its origin port (a north port whose dummy now
lies below its node becomes south and vice versa; an explicitly supplied anchor is mirrored), also
for `FIXED_POS` origins (Java; elk-rs skips them), and the origin and the dummy are collected
(first occurrence order); at the end their ports are re-sorted with Java's
`Collections.sort(ports, PortListSorter.CMP_COMBINED)` — JDK `TimSort` (`javaSortByM`) with the
`PortListSorter` comparator, which is not a consistent order when only some ports of a side have a
`PORT_INDEX` and throws `IllegalStateException: Port side is undefined` for `UNDEFINED` sides
(elk-rs: its stable `sort_by` with `partial_cmp`) — and their port sides re-cached.

## Rust semantics kept where they differ from Java (unobservable on valid input)
* the node count of a layer is the saved count (Java iterates the graph layer's size);
* a dummy without layout unit or without ports is skipped (Java would throw);
* the nodes are re-sorted in first-occurrence order (Java iterates a `HashSet`; the sorts are
  independent, so the order only decides which of two failing sorts throws first, with the same text).
`LayeredOptions.ALLOW_NON_FLOW_PORTS_TO_SWITCH_SIDES` is not read here (nor in Rust).
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

/-- `SweepCopy`. -/
structure SweepCopy where
  /-- `node_order` as nodes (elk-rs: their flat node indices). -/
  nodes : Array (Array LNodeId) := #[]
  /-- `port_orders` as port lists per node per layer (elk-rs: their captured port ids). -/
  ports : Array (Array (Array LPortId)) := #[]
  /-- The snapshot the indices refer to. -/
  snapshot : CrossMinSnapshot := {}
  deriving Inhabited

namespace SweepCopy

/-- The port lists of the nodes of `layer[i:]` pushed onto `out`. -/
private partial def portListsFrom (a : LGraphArena) (layer : Array LNodeId) (i : Nat)
    (out : Array (Array LPortId)) : Array (Array LPortId) :=
  if h : i < layer.size then portListsFrom a layer (i + 1) (out.push (a.node layer[i]).ports) else out

/-- `SweepCopy::new(node_order, snapshot)` on an arena: the nodes and their current port lists. -/
def ofArena (a : LGraphArena) (order : Array (Array LNodeId)) (s : CrossMinSnapshot) : SweepCopy where
  nodes := order
  ports := order.map fun layer => portListsFrom a layer 0 (Array.emptyWithCapacity layer.size)
  snapshot := s

/-- `SweepCopy::new(node_order, snapshot)`. -/
def new (order : Array (Array LNodeId)) (s : CrossMinSnapshot) : LayeredM SweepCopy := do
  return ofArena (← get) order s

/-- `copy_from(node_order, snapshot)`: the same as `new` (Rust reuses its buffers). -/
def copyFrom (_sc : SweepCopy) (order : Array (Array LNodeId)) (s : CrossMinSnapshot) : LayeredM SweepCopy :=
  new order s

/-- `copy_from_sweep(source)`. -/
@[inline] def copyFromSweep (_sc : SweepCopy) (source : SweepCopy) : SweepCopy := source

/-- `node_indices()`: the flat node indices per layer. -/
def nodeIndices (sc : SweepCopy) : Array (Array Nat) := sc.nodes.map (·.map sc.snapshot.nodeFlatIndex)

/-- `port_orders`: the captured port ids per node per layer (`0` for unknown ports, like Rust). -/
def portOrders (sc : SweepCopy) : Array (Array (Array Nat)) := sc.ports.map (·.map (·.map sc.snapshot.portId))

/-- The nodes the flat indices of `nodeIndices` map back to (`snapshot.nodeRef`). -/
def nodeRefs (sc : SweepCopy) : Array (Array LNodeId) :=
  let s := sc.snapshot
  sc.nodes.map (·.map fun n => s.nodeRef (s.nodeFlatIndex n))

/-- Equal flat node indices and port ids (the elk-rs value). -/
instance : BEq SweepCopy where
  beq x y := x.nodeIndices == y.nodeIndices && x.portOrders == y.portOrders

/-- `Collections.sort(ports, PortListSorter.CMP_COMBINED)` for a node with `constraints`: JDK
`TimSort` with `PortListSorter.comparePortsCombined`; `.error` carries the comparator's
`PortListSorter.undefinedSideMessage` or TimSort's `JavaSort.contractViolationMessage`. -/
def sortPortsCombined (a : LGraphArena) (ports : Array LPortId) (constraints : PortConstraints) :
    Except String (Array LPortId) :=
  match javaSortByM (m := Except String) ports (Intermediate.PortListSorter.comparePortsCombined a constraints) with
  | .ok (.ok sorted) => .ok sorted
  | .ok (.error msg) => .error msg
  | .error msg => .error msg

/-- `push_unique(list, node)`. -/
@[inline] def pushUnique (list : Array LNodeId) (n : LNodeId) : Array LNodeId :=
  if list.contains n then list else list.push n

/-- Rust `assert_correct_port_sides(dummy)`: switches the side of the origin port of a north/south
port dummy that ended up on the other side of its node; the origin (`IN_LAYER_LAYOUT_UNIT`), or
`none` without origin or without dummy port. -/
def assertCorrectPortSides (dummy : LNodeId) : LayeredM (Option LNodeId) := do
  let d ← getNode dummy
  let some origin := d.internal.inLayerLayoutUnit | return none
  let dummyId := d.id
  let o ← getNode origin
  let originId := o.id
  let some dummyPort := d.ports[0]? | return none
  let some (.lPort dummyOriginPort) := (← getPort dummyPort).internal.origin | return some origin
  for port in o.ports do
    if port == dummyOriginPort then
      let side := (← getPort port).side
      if side == .north && dummyId > originId then
        modifyPort port fun p =>
          let p := p.setSide .south
          if p.explicitlySuppliedPortAnchor then { p with anchor := { p.anchor with y := p.size.y - p.anchor.y } } else p
      else if side == .south && originId > dummyId then
        modifyPort port fun p =>
          let p := p.setSide .north
          if p.explicitlySuppliedPortAnchor then { p with anchor := { p.anchor with y := -(p.size.y - p.anchor.y) } } else p
      break
  return some origin

/-- One saved node of layer `layerIndex` written back (`apply_to_layers` inner loop): id, ports,
port constraints and the layer slot; whether it is a north/south port dummy. The saved node and
ports go through the snapshot's index round trip (`nodeRef (nodeFlatIndex n)`, `portRefOpt (portId p)`). -/
def applyNode (sc : SweepCopy) (layer : LayerId) (layerIndex nodeIndex : Nat) (saved : LNodeId) (setPortConstraints : Bool)
    (s : CrossMinSnapshot) : LayeredM (LNodeId × Bool) := do
  let node := s.nodeRef (s.nodeFlatIndex saved)
  let savedPorts := ((sc.ports[layerIndex]?).bind (·[nodeIndex]?)).getD #[]
  let ports := savedPorts.filterMap fun p => s.portRefOpt (s.portId p)
  modifyNode node fun x => { x with id := nodeIndex, ports }
  let isNorthSouth := (← getNode node).type == .northSouthPort
  if setPortConstraints then
    let constraints ← getNodePropD node LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
    if !constraints.isOrderFixed then
      setNodeProp node LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedOrder
  modifyLayer layer fun l =>
    if nodeIndex < l.nodes.size then { l with nodes := l.nodes.set! nodeIndex node }
    else { l with nodes := l.nodes.push node }
  return (node, isNorthSouth)

/-- `apply_to_layers(layers, set_port_constraints, snapshot)`. -/
def applyToLayers (sc : SweepCopy) (layers : Array LayerId) (setPortConstraints : Bool) (s : CrossMinSnapshot) :
    LayeredM Unit := do
  let mut updatePortOrder : Array LNodeId := #[]
  for h : layerIndex in [0:layers.size] do
    let layer := layers[layerIndex]
    let saved := sc.nodes[layerIndex]?.getD #[]
    let mut northSouthPortDummies : Array LNodeId := #[]
    for h2 : nodeIndex in [0:saved.size] do
      let (node, isNorthSouth) ← sc.applyNode layer layerIndex nodeIndex saved[nodeIndex] setPortConstraints s
      if isNorthSouth then northSouthPortDummies := northSouthPortDummies.push node
    for dummy in northSouthPortDummies do
      if let some origin ← assertCorrectPortSides dummy then
        updatePortOrder := pushUnique (pushUnique updatePortOrder origin) dummy
  for node in updatePortOrder do
    let constraints ← getNodePropD node LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
    match sortPortsCombined (← get) (← getNode node).ports constraints with
    | .ok sorted => modifyNode node fun x => { x with ports := sorted }
    | .error msg =>
      if msg == Intermediate.PortListSorter.undefinedSideMessage then Elk.Core.throwIllegalState msg
      else throw (IO.userError JavaSort.contractViolationError)
    cachePortSides node

/-- `transfer_node_and_port_orders_to_graph(graph, set_port_constraints, snapshot)` (also
`transfer_node_and_port_orders_to_graph_guard`). -/
def transferNodeAndPortOrdersToGraph (sc : SweepCopy) (graph : LGraphId) (setPortConstraints : Bool)
    (s : CrossMinSnapshot) : LayeredM Unit := do
  sc.applyToLayers (← getGraph graph).layers setPortConstraints s

end SweepCopy

end Elk.Alg.Layered.P3Order
