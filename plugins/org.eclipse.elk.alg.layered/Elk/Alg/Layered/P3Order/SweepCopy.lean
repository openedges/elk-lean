import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.P3Order.CrossMinSnapshot
import Elk.Core.Util.Sort
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.layered.p3order.SweepCopy`

A copy of the node order and of the port order of every node, taken after a sweep and written
back to the graph for the best sweep (elk-rs `sweep_copy.rs`). Like elk-rs the copy stores
`CrossMinSnapshot` indices: per layer the *flat node indices*, per node the *port ids* (captured
`LPort.id`s); `snapshot.nodeRef`/`portRefOpt` map them back. It is a pure value (`copyFromSweep`
is the source itself).

## API (for `GraphInfoHolder`/`LayerSweepCrossingMinimizer`)
* `SweepCopy.new order snapshot : LayeredM SweepCopy` (`ofArena` is the pure form);
  `copyFrom` is `new` (Rust reuses the allocations), `copyFromSweep _ source = source`.
* `nodeIndices`: the flat node indices per layer.
* `transferNodeAndPortOrdersToGraph sc graph setPortConstraints snapshot` (Rust
  `transfer_node_and_port_orders_to_graph`; the `_guard` variant is the same in Lean).

## `transferNodeAndPortOrdersToGraph`
For every layer `i` of the graph and every saved node `j` of layer `i`: `node.id := j`, the node's
ports are replaced by the saved ones (port ids without port are dropped), with
`setPortConstraints` an order that is not fixed becomes `FIXED_ORDER`, and the layer slot `j` is
overwritten (or appended). The port side cache is not refreshed (Rust). After a layer, every
`NORTH_SOUTH_PORT` dummy of it corrects the side of its origin port (a north port whose dummy now
lies below its node becomes south and vice versa; an explicitly supplied anchor is mirrored),
and the origin and the dummy are collected (first occurrence order); at the end their ports are
re-sorted (side, then for fixed orders `PORT_INDEX`/position) and their port sides re-cached.

## Rust semantics kept where they differ from Java
* the node count of a layer is the saved count (Java iterates the graph layer's size);
* no side correction when the origin has `FIXED_POS` port constraints, and a dummy without layout
  unit or without ports is skipped (Java would throw);
* the re-sort uses Rust's `compare_ports` (Java `PortListSorter.CMP_COMBINED`) and visits the
  nodes in first-occurrence order (Java iterates a `HashSet`).
`LayeredOptions.ALLOW_NON_FLOW_PORTS_TO_SWITCH_SIDES` is not read here (nor in Rust).
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

/-- `SweepCopy`. -/
structure SweepCopy where
  /-- `node_order`: flat node indices (`CrossMinSnapshot`) per layer. -/
  nodeOrder : Array (Array Nat) := #[]
  /-- `port_orders`: port ids per node per layer. -/
  portOrders : Array (Array (Array Nat)) := #[]
  deriving Inhabited, BEq, Repr

namespace SweepCopy

/-- `SweepCopy::new(node_order, snapshot)` on an arena: the flat indices of the nodes and the
captured ids of their current ports (`0` for unknown ones, like Rust). -/
def ofArena (a : LGraphArena) (order : Array (Array LNodeId)) (s : CrossMinSnapshot) : SweepCopy where
  nodeOrder := order.map (·.map s.nodeFlatIndex)
  portOrders := order.map (·.map fun n => (a.node n).ports.map s.portId)

/-- `SweepCopy::new(node_order, snapshot)`. -/
def new (order : Array (Array LNodeId)) (s : CrossMinSnapshot) : LayeredM SweepCopy := do
  return ofArena (← get) order s

/-- `copy_from(node_order, snapshot)`: the same as `new` (Rust reuses its buffers). -/
def copyFrom (_sc : SweepCopy) (order : Array (Array LNodeId)) (s : CrossMinSnapshot) : LayeredM SweepCopy :=
  new order s

/-- `copy_from_sweep(source)`. -/
@[inline] def copyFromSweep (_sc : SweepCopy) (source : SweepCopy) : SweepCopy := source

/-- `node_indices()`. -/
@[inline] def nodeIndices (sc : SweepCopy) : Array (Array Nat) := sc.nodeOrder

/-- Rust `compare_ports(p1, p2, constraints)`: by side (ordinal), equal unless the order is fixed,
then with `FIXED_ORDER` different `PORT_INDEX`es, then the position along the side (`x` north,
`y` east, reversed `x` south, reversed `y` west; `partial_cmp`). -/
def comparePorts (a : LGraphArena) (constraints : PortConstraints) (p1 p2 : LPortId) : Ordering :=
  let pt1 := a.port p1
  let pt2 := a.port p2
  let sideCmp := Ord.compare (ElkEnum.ordinal pt1.side) (ElkEnum.ordinal pt2.side)
  if sideCmp != .eq then sideCmp
  else if !constraints.isOrderFixed then .eq
  else
    let byIndex : Option Ordering :=
      if constraints == .fixedOrder then
        match pt1.props.get LayeredOptions.PORT_INDEX, pt2.props.get LayeredOptions.PORT_INDEX with
        | some i1, some i2 => if i1 != i2 then some (Ord.compare i1 i2) else none
        | _, _ => none
      else none
    match byIndex with
    | some o => o
    | none =>
      match pt1.side with
      | .north => Float.comparePartial pt1.position.x pt2.position.x
      | .east => Float.comparePartial pt1.position.y pt2.position.y
      | .south => Float.comparePartial pt2.position.x pt1.position.x
      | .west => Float.comparePartial pt2.position.y pt1.position.y
      | .undefined => .eq

/-- `sort_ports_combined(ports, constraints)`: Rust `sort_by(compare_ports)`; the stable sort is
given the order induced by `compare_ports(..) == Less` (all `sort_by` looks at). -/
def sortPortsCombined (a : LGraphArena) (ports : Array LPortId) (constraints : PortConstraints) : Array LPortId :=
  stableSort ports fun p1 p2 =>
    if comparePorts a constraints p1 p2 == .lt then .lt
    else if comparePorts a constraints p2 p1 == .lt then .gt
    else .eq

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
  let originConstraints := o.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  let originId := o.id
  if originConstraints.isPosFixed then return some origin
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
port constraints and the layer slot; whether it is a north/south port dummy. -/
def applyNode (sc : SweepCopy) (layer : LayerId) (layerIndex nodeIndex : Nat) (flat : Nat) (setPortConstraints : Bool)
    (s : CrossMinSnapshot) : LayeredM (LNodeId × Bool) := do
  let node := s.nodeRef flat
  let savedPorts := ((sc.portOrders[layerIndex]?).bind (·[nodeIndex]?)).getD #[]
  let ports := savedPorts.filterMap s.portRefOpt
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
    let flats := sc.nodeOrder[layerIndex]?.getD #[]
    let mut northSouthPortDummies : Array LNodeId := #[]
    for h2 : nodeIndex in [0:flats.size] do
      let (node, isNorthSouth) ← sc.applyNode layer layerIndex nodeIndex flats[nodeIndex] setPortConstraints s
      if isNorthSouth then northSouthPortDummies := northSouthPortDummies.push node
    for dummy in northSouthPortDummies do
      if let some origin ← assertCorrectPortSides dummy then
        updatePortOrder := pushUnique (pushUnique updatePortOrder origin) dummy
  for node in updatePortOrder do
    let constraints ← getNodePropD node LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
    let sorted := sortPortsCombined (← get) (← getNode node).ports constraints
    modifyNode node fun x => { x with ports := sorted }
    cachePortSides node

/-- `transfer_node_and_port_orders_to_graph(graph, set_port_constraints, snapshot)` (also
`transfer_node_and_port_orders_to_graph_guard`). -/
def transferNodeAndPortOrdersToGraph (sc : SweepCopy) (graph : LGraphId) (setPortConstraints : Bool)
    (s : CrossMinSnapshot) : LayeredM Unit := do
  sc.applyToLayers (← getGraph graph).layers setPortConstraints s

end SweepCopy

end Elk.Alg.Layered.P3Order
