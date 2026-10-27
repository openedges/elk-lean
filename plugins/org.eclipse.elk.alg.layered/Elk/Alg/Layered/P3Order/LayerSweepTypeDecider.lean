import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.P3Order.Counting.IInitializable
import Elk.Alg.Layered.P3Order.Counting.BinaryIndexedTree
/-!
# `org.eclipse.elk.alg.layered.p3order.LayerSweepTypeDecider`

Decides whether a nested graph is crossing-minimised bottom up (on its own, `true`) or swept into
hierarchically from its parent (`false`), elk-rs `layer_sweep_type_decider.rs`. The decision walks
the nodes in layer order and propagates "influences" along the edges: paths that start at a node
without western connections count as *random* influence, paths that start at an external port
dummy as *hierarchical* influence; the graph is laid out bottom up when the normalised difference
`(random - hierarchical) / (random + hierarchical)` reaches the `hierarchicalSweepiness` boundary.

## API (for `GraphInfoHolder`)
* `LayerSweepTypeDecider.new graph parent hasParent crossMinDeterministic : BaseIO LayerSweepTypeDecider`
  (Rust `new(l_graph, parent, has_parent, cross_min_deterministic)`).
* `initializable`: `Layer.id := layer index`, `LNode.id := node index` and fresh node infos.
* `useBottomUpWithBoundary order boundary` (Rust `use_bottom_up_with_boundary`) and `useBottomUp order`
  (which reads `CROSSING_MINIMIZATION_HIERARCHICAL_SWEEPINESS` from the graph).

## Orders and numerics (Rust)
Nodes are visited layer by layer in the order given; within a layer north/south port dummies are
collected and visited after the other nodes of that layer. The outgoing edges of a node are taken
port by port (`LNode.getOutgoingEdges()`), the north/south ports with `getPortSideView(NORTH)` then
`getPortSideView(SOUTH)`. The node infos are indexed by `[Layer.id][LNode.id]` and grown on demand
(Rust `node_info_for`); all counters are `i32` (`Int`), the final ratio is `f64` (`INFINITY` when
there are no paths at all).
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Core.Options Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.P3Order.Counting LayeredM

/-- `LayerSweepTypeDecider.NodeInfo`. -/
structure NodeInfo where
  /-- `connected_edges`. -/
  connectedEdges : Int := 0
  /-- `hierarchical_influence`. -/
  hierarchicalInfluence : Int := 0
  /-- `random_influence`. -/
  randomInfluence : Int := 0
  deriving Inhabited, Repr, BEq

/-- `NodeInfo::transfer(other)`: adds the influences and the connected edge count of `other`. -/
def NodeInfo.transfer (self other : NodeInfo) : NodeInfo :=
  { hierarchicalInfluence := self.hierarchicalInfluence + other.hierarchicalInfluence
    randomInfluence := self.randomInfluence + other.randomInfluence
    connectedEdges := self.connectedEdges + other.connectedEdges }

/-- `LayerSweepTypeDecider`; the node infos live behind an `IO.Ref` (initialised by the
`IInitializable` callbacks, read and updated by `useBottomUpWithBoundary`). -/
structure LayerSweepTypeDecider where
  /-- `node_info[layer id][node id]`. -/
  nodeInfo : IO.Ref (Array (Array NodeInfo))
  /-- `l_graph`. -/
  lGraph : LGraphId
  /-- `parent`: the parent node of the graph. -/
  parent : Option LNodeId
  /-- `has_parent`. -/
  hasParent : Bool
  /-- `cross_min_deterministic`. -/
  crossMinDeterministic : Bool

namespace LayerSweepTypeDecider

/-- `LayerSweepTypeDecider::new(l_graph, parent, has_parent, cross_min_deterministic)`. -/
def new (lGraph : LGraphId) (parent : Option LNodeId) (hasParent crossMinDeterministic : Bool) :
    BaseIO LayerSweepTypeDecider := do
  return { nodeInfo := ← IO.mkRef #[], lGraph, parent, hasParent, crossMinDeterministic }

/-! ## Node info table -/

/-- An index beyond which Rust's `resize` could not allocate (negative ids cast to `usize`); such
keys are ignored instead of growing the table. -/
private def MAX_INDEX : Nat := 1 <<< 32

/-- `layer_id(node)`/`node_id(node)`: `Layer.id as usize` (`0` without a layer) and `LNode.id as usize`. -/
def nodeKey (a : LGraphArena) (n : LNodeId) : Nat × Nat :=
  let nd := a.node n
  let li := match nd.layer with
    | some l => asUsize (a.layer l).id
    | none => 0
  (li, asUsize nd.id)

/-- The growth part of `node_info_for(node)`: the table has a slot `[li][ni]` afterwards. -/
def ensureSlot (info : Array (Array NodeInfo)) (li ni : Nat) : Array (Array NodeInfo) :=
  if li >= MAX_INDEX || ni >= MAX_INDEX then info
  else
    let info := if info.size <= li then info ++ Array.replicate (li + 1 - info.size) #[] else info
    info.modify li fun row => if row.size <= ni then row ++ Array.replicate (ni + 1 - row.size) (default : NodeInfo) else row

/-- The info of slot `[li][ni]` (default when missing). -/
@[inline] def infoAt (info : Array (Array NodeInfo)) (li ni : Nat) : NodeInfo :=
  ((info[li]?).bind (·[ni]?)).getD default

/-- `node_info_for(node)` followed by an update of the info. -/
def updateInfo (info : Array (Array NodeInfo)) (a : LGraphArena) (n : LNodeId) (f : NodeInfo → NodeInfo) :
    Array (Array NodeInfo) :=
  let (li, ni) := nodeKey a n
  (ensureSlot info li ni).modify li (·.modify ni f)

/-- `node_info_for(node)` as a value (the table grows like in Rust). -/
def infoFor (info : Array (Array NodeInfo)) (a : LGraphArena) (n : LNodeId) : Array (Array NodeInfo) × NodeInfo :=
  let (li, ni) := nodeKey a n
  let info := ensureSlot info li ni
  (info, infoAt info li ni)

/-- `transfer_info_to(current_info, target)`: the target's info absorbs `current` and counts one more
connected edge. -/
def transferInfoTo (info : Array (Array NodeInfo)) (a : LGraphArena) (current : NodeInfo) (target : LNodeId) :
    Array (Array NodeInfo) :=
  updateInfo info a target fun t =>
    let t := t.transfer current
    { t with connectedEdges := t.connectedEdges + 1 }

/-- `transfer_info_to_target(current_info, edge)`: the target node of the edge, if any. -/
def transferInfoToTarget (info : Array (Array NodeInfo)) (a : LGraphArena) (current : NodeInfo) (edge : LEdgeId) :
    Array (Array NodeInfo) :=
  match (a.edge edge).target.bind fun p => (a.port p).owner with
  | some target => transferInfoTo info a current target
  | none => info

/-! ## Predicates -/

/-- `fixed_port_order()`: the parent node's `PORT_CONSTRAINTS` fix the order. -/
def fixedPortOrder (d : LayerSweepTypeDecider) (a : LGraphArena) : Bool :=
  match d.parent with
  | some p => ((a.node p).props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined).isOrderFixed
  | none => false

/-- `fewer_than_two_in_out_edges()`: fewer than two east and fewer than two west ports on the
parent node (`true` without parent). -/
def fewerThanTwoInOutEdges (d : LayerSweepTypeDecider) (a : LGraphArena) : Bool :=
  match d.parent with
  | some p => (a.nodePortSideView p .east).size < 2 && (a.nodePortSideView p .west).size < 2
  | none => true

/-- `has_no_eastern_ports(node)` / `has_no_western_ports(node)`: no port on `side`, or none of them
has a connected edge. -/
def hasNoPortsWithEdgesOn (a : LGraphArena) (n : LNodeId) (side : PortSide) : Bool :=
  let ports := a.nodePortSideView n side
  ports.isEmpty || !ports.any fun p => !(a.port p).connectedEdges.isEmpty

/-- `is_eastern_dummy(node)`: the `ORIGIN` of the node is an east port. -/
def isEasternDummy (a : LGraphArena) (n : LNodeId) : Bool :=
  match (a.node n).internal.origin with
  | some (.lPort p) => (a.port p).side == .east
  | _ => false

/-! ## The decision -/

/-- The accumulator of `use_bottom_up_with_boundary`. -/
structure Acc where
  info : Array (Array NodeInfo)
  pathsToRandom : Int := 0
  pathsToHierarchical : Int := 0

/-- The edge loop of a node: every outgoing edge adds the node's influences to the path counts and
transfers the info to the edge's target. -/
def propagateAlongEdges (a : LGraphArena) (acc : Acc) (node : LNodeId) (current : NodeInfo) : Acc := Id.run do
  let mut acc := acc
  for edge in a.nodeOutgoingEdges node do
    acc := { acc with
      pathsToRandom := acc.pathsToRandom + current.randomInfluence
      pathsToHierarchical := acc.pathsToHierarchical + current.hierarchicalInfluence
      info := transferInfoToTarget acc.info a current edge }
  return acc

/-- One node of a layer that is no north/south port dummy (the body of the inner Rust loop). -/
def visitNode (a : LGraphArena) (acc : Acc) (node : LNodeId) : Acc := Id.run do
  let isExternal := (a.node node).type == .externalPort
  let isEastern := isEasternDummy a node
  let hasNoWestern := hasNoPortsWithEdgesOn a node .west
  let hasNoEastern := hasNoPortsWithEdgesOn a node .east
  let (info, info0) := infoFor acc.info a node
  let mut acc := { acc with info }
  let mut current := info0
  if isExternal then
    current := { current with hierarchicalInfluence := 1 }
    if isEastern then
      acc := { acc with pathsToHierarchical := acc.pathsToHierarchical + current.connectedEdges }
  else if hasNoWestern then
    current := { current with randomInfluence := 1 }
  else if hasNoEastern then
    acc := { acc with pathsToRandom := acc.pathsToRandom + current.connectedEdges }
  let cur := current
  acc := { acc with info := updateInfo acc.info a node fun _ => cur }
  acc := propagateAlongEdges a acc node current
  let northSouthPorts := a.nodePortSideView node .north ++ a.nodePortSideView node .south
  for port in northSouthPorts do
    if let some nsDummy := (a.port port).internal.portDummy then
      acc := { acc with
        pathsToRandom := acc.pathsToRandom + current.randomInfluence
        pathsToHierarchical := acc.pathsToHierarchical + current.hierarchicalInfluence
        info := transferInfoTo acc.info a current nsDummy }
  return acc

/-- One layer: the regular nodes, then the collected north/south port dummies. -/
def visitLayer (a : LGraphArena) (acc : Acc) (layer : Array LNodeId) : Acc := Id.run do
  let mut acc := acc
  let mut nsPortDummies : Array LNodeId := #[]
  for node in layer do
    if (a.node node).type == .northSouthPort then
      nsPortDummies := nsPortDummies.push node
    else
      acc := visitNode a acc node
  for node in nsPortDummies do
    let (info, current) := infoFor acc.info a node
    acc := propagateAlongEdges a { acc with info } node current
  return acc

/-- `use_bottom_up_with_boundary(node_order, boundary)`. -/
def useBottomUpWithBoundary (d : LayerSweepTypeDecider) (nodeOrder : Array (Array LNodeId)) (boundary : Float) :
    LayeredM Bool := do
  let a ← get
  if boundary < -1.0 || !d.hasParent || d.fixedPortOrder a || d.fewerThanTwoInOutEdges a then
    return true
  if d.crossMinDeterministic then
    return false
  let info ← d.nodeInfo.swap #[]
  let acc := nodeOrder.foldl (visitLayer a) { info }
  d.nodeInfo.set acc.info
  let allPaths := Float.ofInt (acc.pathsToRandom + acc.pathsToHierarchical)
  let normalized := if allPaths == 0.0 then Elk.Core.Util.Float.posInf
    else Float.ofInt (acc.pathsToRandom - acc.pathsToHierarchical) / allPaths
  return normalized >= boundary

/-- `use_bottom_up(node_order)`: the boundary is the graph's `CROSSING_MINIMIZATION_HIERARCHICAL_SWEEPINESS`. -/
def useBottomUp (d : LayerSweepTypeDecider) (nodeOrder : Array (Array LNodeId)) : LayeredM Bool := do
  let boundary ← getGraphPropD d.lGraph LayeredOptions.CROSSING_MINIMIZATION_HIERARCHICAL_SWEEPINESS 0.0
  d.useBottomUpWithBoundary nodeOrder boundary

/-! ## `IInitializable` -/

/-- `init_at_layer_level(layer_index, node_order)`: `Layer.id := layerIndex`, fresh infos for the layer. -/
def initAtLayerLevel (d : LayerSweepTypeDecider) (l : Nat) (order : Array (Array LNodeId)) : LayeredM Unit := do
  if let some first := (order[l]?).bind (·[0]?) then
    if let some layer := (← getNode first).layer then
      modifyLayer layer fun x => { x with id := l }
  d.nodeInfo.modify fun info =>
    let info := if info.size <= l then info ++ Array.replicate (l + 1 - info.size) #[] else info
    match order[l]? with
    | some nodes => info.set! l (Array.replicate nodes.size (default : NodeInfo))
    | none => info

/-- `init_at_node_level(layer_index, node_index, node_order)`: `LNode.id := nodeIndex`, a fresh info. -/
def initAtNodeLevel (d : LayerSweepTypeDecider) (l n : Nat) (order : Array (Array LNodeId)) : LayeredM Unit := do
  let some node := (order[l]?).bind (·[n]?) | return
  modifyNode node fun x => { x with id := n }
  d.nodeInfo.modify fun info => (ensureSlot info l n).modify l (·.set! n default)

/-- The `IInitializable` implementation (layer and node level). -/
def initializable (d : LayerSweepTypeDecider) : Initializable where
  initAtLayerLevel := d.initAtLayerLevel
  initAtNodeLevel := d.initAtNodeLevel

end LayerSweepTypeDecider

end Elk.Alg.Layered.P3Order
