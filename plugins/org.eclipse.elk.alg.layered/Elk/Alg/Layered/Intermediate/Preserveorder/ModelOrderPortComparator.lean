import Std.Data.HashMap
import Elk.Alg.Layered.Intermediate.Preserveorder.CMGroupModelOrderCalculator
/-!
# `org.eclipse.elk.alg.layered.intermediate.preserveorder.ModelOrderPortComparator`

Port of `ModelOrderPortComparator.java` (elk-rs `model_order_port_comparator.rs`): compares two ports of the
same node by their side, the order of the nodes their incoming edges come from, the model order of
their outgoing edges (or of the long edge target nodes) and the port model order. The comparator is
stateful: every decision is recorded in transitive `biggerThan`/`smallerThan` relations
(`ModelOrderRelations`) that later comparisons consult first.

This module also holds what both comparators share: `ModelOrderRelations` (Rust defines it in
`model_order_node_comparator.rs`; it lives here because the node comparator imports this module and
Lean has no import cycles) and `layerIdOf` (Rust `layer_id`).

## API (for `LayerSweepCrossingMinimizer` and `SortByInputModelProcessor`)
* `ModelOrderPortComparator.new graph previousLayer strategy targetNodeModelOrder portModelOrder`
  (Rust `new`; `graph` is a `ModelOrderGraphContext`, see `CMGroupModelOrderCalculator`).
* `compare c p1 p2 : LayeredM (Int × ModelOrderPortComparator)` — the Rust `i32` result (`-1`, `0`,
  `1`) and the comparator with its updated relations; `compareM p1 p2 : PortComparatorM Int` is the
  same in `StateT ModelOrderPortComparator LayeredM`.
* `clearTransitiveOrdering`, `resetForPreviousLayer`, `resetForPreviousLayerSlice`,
  `resetForNodeTargetModelOrder` are pure updates (Rust `&mut self` methods).

## Java semantics (ELK Java is the reference; elk-rs differed)
* The fourth transitivity check of Java tests `biggerThan(p2) ∋ p1` a second time (a copy of the
  second check), so it never decides; elk-rs tested `smallerThan(p2) ∋ p1`.
* The previous-layer check is `checkReferenceLayer(previousLayer, …)`: the first of the two source
  nodes found in the previous layer decides, also when the other one is not in it (elk-rs decided only
  when both were in it).
* Port and edge (group) model orders are `CMGroupModelOrderCalculator.calculateModelOrderOrGroupModelOrder`
  of the element and the other element: the group offset applies only when both group ids are enforced
  orders (elk-rs checked only the element's), `int` arithmetic.
* The precomputed `targetNodeModelOrder` map is consulted for each long edge target node separately
  (elk-rs only when both ports had one).

Kept from elk-rs: missing edge ends or port owners skip the incoming-edge block (Java would throw a
`NullPointerException`; the layered graph always has them).
-/
namespace Elk.Alg.Layered.Intermediate.Preserveorder

open Elk.Graph Elk.Core.Util Elk.Core.Options Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

/-- Bit `i` of a `Nat` bit set. -/
@[inline] def bitSetBit (i : Nat) : Nat := 1 <<< i

/-- Members of a `Nat` bit set in ascending order (Rust `set_members`: per 64-bit word, the lowest
set bit is isolated and cleared until the word is empty). -/
def bitSetMembers (words : Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut x := words
  let mut base := 0
  while x != 0 do
    let mut w : UInt64 := x.toUInt64
    while w != 0 do
      let lowest := w &&& (0 - w)
      out := out.push (base + lowest.log2.toNat)
      w := w ^^^ lowest
    x := x >>> 64
    base := base + 64
  return out

/-- Rust `ModelOrderRelations<Key>`: Java's `biggerThan`/`smallerThan` maps (`HashMap<K, HashSet<K>>`)
stored as dense bit sets over key indices (Rust uses `Vec<u64>` words, Lean a `Nat` per key). Keys get
indices in order of first use; only set membership is observable. -/
structure ModelOrderRelations (κ : Type) [BEq κ] [Hashable κ] where
  /-- Key → dense index (Rust `indices`). -/
  indices : Std.HashMap κ Nat := {}
  /-- `bigger[i]`: the keys key `i` is bigger than (Java `biggerThan.get(k)`). -/
  bigger : Array Nat := #[]
  /-- `smaller[i]`: the keys key `i` is smaller than (Java `smallerThan.get(k)`). -/
  smaller : Array Nat := #[]

namespace ModelOrderRelations

variable {κ : Type} [BEq κ] [Hashable κ]

instance : Inhabited (ModelOrderRelations κ) := ⟨{}⟩

/-- Rust `index(key)`: the dense index of `key`, allocating empty sets for a new key. -/
def index (r : ModelOrderRelations κ) (key : κ) : Nat × ModelOrderRelations κ :=
  match r.indices.get? key with
  | some i => (i, r)
  | none =>
    let ⟨indices, bigger, smaller⟩ := r
    let i := indices.size
    (i, ⟨indices.insert key i, bigger.push 0, smaller.push 0⟩)

/-- Rust `bigger(left, right)`: `right ∈ biggerThan(left)`. -/
@[inline] def isBigger (r : ModelOrderRelations κ) (left right : Nat) : Bool :=
  (r.bigger[left]?.getD 0).testBit right

/-- Rust `smaller(left, right)`: `right ∈ smallerThan(left)`. -/
@[inline] def isSmaller (r : ModelOrderRelations κ) (left right : Nat) : Bool :=
  (r.smaller[left]?.getD 0).testBit right

/-- Rust `record(bigger, smaller)` = Java `updateBiggerAndSmallerAssociations(bigger, smaller)`:
snapshots `biggerThan(smaller)` and `smallerThan(bigger)` before the direct insertion, then
propagates (also for inconsistent/cyclic observations, exactly as the set-based original). -/
def record (r : ModelOrderRelations κ) (bigger smaller : Nat) : ModelOrderRelations κ := Id.run do
  let ⟨indices, bs, ss⟩ := r
  let below := bs[smaller]?.getD 0
  let above := ss[bigger]?.getD 0
  let mut bs := bs.modify bigger (· ||| bitSetBit smaller)
  let mut ss := ss.modify smaller (· ||| bitSetBit bigger)
  for verySmall in bitSetMembers below do
    bs := bs.modify bigger (· ||| bitSetBit verySmall)
    ss := ss.modify verySmall (fun w => (w ||| bitSetBit bigger) ||| above)
  for veryBig in bitSetMembers above do
    ss := ss.modify smaller (· ||| bitSetBit veryBig)
    bs := bs.modify veryBig (fun w => (w ||| bitSetBit smaller) ||| below)
  return ⟨indices, bs, ss⟩

end ModelOrderRelations

/-- `i32 as usize` (two's complement sign extension to 64 bits). -/
def i32AsUsize (i : Int) : Nat := if i < 0 then (i + 18446744073709551616).toNat else i.toNat

/-- Rust `layer_id(node)`: `layer.id as usize` of the node's layer (`Layer.id`, not its index), `0`
for a node without a layer. -/
def layerIdOf (n : LNodeId) : LayeredM Nat := do
  match (← getNode n).layer with
  | some l => return i32AsUsize (← getLayer l).id
  | none => return 0

/-- `-1`, `0` or `1` (Rust `match a.cmp(&b)`). -/
@[inline] def cmpInt (a b : Int) : Int := if a < b then -1 else if a > b then 1 else 0

/-- Rust `ModelOrderPortComparator`. -/
structure ModelOrderPortComparator where
  /-- `target_node_model_order`: minimal edge model order per long edge target node of the node
  whose ports are sorted (Java `targetNodeModelOrder`, `null` = `none`). -/
  targetNodeModelOrder : Option (Std.HashMap LNodeId Int) := none
  /-- `port_model_order` (`CONSIDER_MODEL_ORDER_PORT_MODEL_ORDER`). -/
  portModelOrder : Bool := false
  /-- `previous_layer`. -/
  previousLayer : Array LNodeId := #[]
  /-- `graph` (the options read through it). -/
  graph : ModelOrderGraphContext := {}
  /-- `strategy` (`CONSIDER_MODEL_ORDER_STRATEGY`). -/
  strategy : OrderingStrategy := .none
  /-- `relations` (Java `biggerThan`/`smallerThan`). -/
  relations : ModelOrderRelations LPortId := {}
  deriving Inhabited

/-- `ModelOrderPortComparator` as a state over `LayeredM`. -/
abbrev PortComparatorM := StateT ModelOrderPortComparator LayeredM

/-- The port data `compare` reads up front (Rust `PortSnapshot`). -/
structure PortSnapshot where
  side : PortSide
  node : Option LNodeId
  incomingFirst : Option LEdgeId
  incomingLen : Nat
  outgoingFirst : Option LEdgeId
  outgoingLen : Nat
  /-- `LONG_EDGE_TARGET_NODE`. -/
  longEdgeTargetNode : Option LNodeId
  /-- `MODEL_ORDER` is set. -/
  hasModelOrder : Bool
  deriving Inhabited

/-- Rust `port_snapshot(port)`. -/
def portSnapshot (p : LPortId) : LayeredM PortSnapshot := do
  let pt ← getPort p
  return { side := pt.side, node := pt.owner
           incomingFirst := pt.incomingEdges[0]?, incomingLen := pt.incomingEdges.size
           outgoingFirst := pt.outgoingEdges[0]?, outgoingLen := pt.outgoingEdges.size
           longEdgeTargetNode := pt.internal.longEdgeTargetNode
           hasModelOrder := pt.internal.modelOrder.isSome }

/-- `CMGroupModelOrderCalculator.calculateModelOrderOrGroupModelOrder(port, other, graph, offset)` for two
ports: `-1` without `MODEL_ORDER`; with an `ENFORCED` group order and both ports'
`GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID`s in the enforced orders `offset * groupId + MODEL_ORDER`
(`int`); otherwise `MODEL_ORDER`. -/
def portModelOrderValue (port other : LPortId) (graph : ModelOrderGraphContext) (offset : Int) : LayeredM Int := do
  let pt ← getPort port
  let some order := pt.internal.modelOrder | return -1
  if graph.enforceGroupModelOrder then
    let groupId := pt.props.getD LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID 0
    let otherGroupId := (← getPort other).props.getD LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID 0
    if graph.enforcedGroupOrders.contains groupId && graph.enforcedGroupOrders.contains otherGroupId then
      return Int.wrap32 (offset * groupId + order)
  return order

/-- The outgoing edge order of `ModelOrderPortComparator.compare`: `calculateModelOrderOrGroupModelOrder(edge,
other, graph, offset)` if the edge has a `MODEL_ORDER` (else `0`), group offset as in `portModelOrderValue`. -/
def edgeModelOrderValue (edge other : LEdgeId) (graph : ModelOrderGraphContext) (offset : Int) : LayeredM Int := do
  let ed ← getEdge edge
  let some order := ed.internal.modelOrder | return 0
  if graph.enforceGroupModelOrder then
    let groupId := ed.props.getD LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID 0
    let otherGroupId := (← getEdge other).props.getD LayeredOptions.GROUP_MODEL_ORDER_CROSSING_MINIMIZATION_ID 0
    if graph.enforcedGroupOrders.contains groupId && graph.enforcedGroupOrders.contains otherGroupId then
      return Int.wrap32 (offset * groupId + order)
  return order

/-- Rust `to_target_node_position_map`. -/
def toTargetNodePositionMap (m : Option (Array (LNodeId × Int))) : Option (Std.HashMap LNodeId Int) :=
  m.map fun orders => orders.foldl (fun acc (k, v) => acc.insert k v) {}

namespace ModelOrderPortComparator

/-- `new ModelOrderPortComparator(graph, previousLayer, strategy, targetNodeModelOrder, portModelOrder)`. -/
def new (graph : ModelOrderGraphContext) (previousLayer : Array LNodeId) (strategy : OrderingStrategy)
    (targetNodeModelOrder : Option (Array (LNodeId × Int))) (portModelOrder : Bool) : ModelOrderPortComparator :=
  { targetNodeModelOrder := toTargetNodePositionMap targetNodeModelOrder, portModelOrder := portModelOrder
    previousLayer := previousLayer
    graph := graph, strategy := strategy }

/-- `clearTransitiveOrdering()`. -/
def clearTransitiveOrdering (c : ModelOrderPortComparator) : ModelOrderPortComparator :=
  { c with relations := {} }

/-- Rust `reset_for_previous_layer(previous_layer)`: new previous layer, no target node map, no relations. -/
def resetForPreviousLayer (c : ModelOrderPortComparator) (previousLayer : Array LNodeId) : ModelOrderPortComparator :=
  { c with previousLayer := previousLayer
           targetNodeModelOrder := none, relations := {} }

/-- Rust `reset_for_previous_layer_slice(previous_layer)` (same as `resetForPreviousLayer`). -/
def resetForPreviousLayerSlice (c : ModelOrderPortComparator) (previousLayer : Array LNodeId) : ModelOrderPortComparator :=
  c.resetForPreviousLayer previousLayer

/-- Rust `reset_for_node_target_model_order(target_node_model_order)`: new target node map, no relations. -/
def resetForNodeTargetModelOrder (c : ModelOrderPortComparator) (targetNodeModelOrder : Option (Array (LNodeId × Int))) :
    ModelOrderPortComparator :=
  { c with targetNodeModelOrder := toTargetNodePositionMap targetNodeModelOrder, relations := {} }

/-- Applies `f` to the relations, keeping them uniquely referenced. -/
@[inline] def withRelations {α : Type} (f : ModelOrderRelations LPortId → α × ModelOrderRelations LPortId) :
    PortComparatorM α :=
  modifyGet fun c =>
    let rel := c.relations
    let c := { c with relations := {} }
    let (a, rel) := f rel
    (a, { c with relations := rel })

/-- Rust `update_bigger_and_smaller(bigger_ori, smaller_ori, reverse_order)`: records
`bigger > smaller`, swapped when `reverseOrder < 0`. -/
def updateBiggerAndSmaller (biggerOri smallerOri : LPortId) (reverseOrder : Int) : PortComparatorM Unit :=
  withRelations fun rel =>
    let (bigger, smaller) := if reverseOrder < 0 then (smallerOri, biggerOri) else (biggerOri, smallerOri)
    let (bi, rel) := rel.index bigger
    let (si, rel) := rel.index smaller
    ((), rel.record bi si)

/-- Rust `check_reference_layer(layer, p1_node, p2_node)`: `-1` if `p1Node` occurs first in `layer`,
`1` if `p2Node` does, else `0`. -/
def checkReferenceLayer (layer : Array LNodeId) (p1Node p2Node : LNodeId) : Int := Id.run do
  for node in layer do
    if node == p1Node then return -1
    else if node == p2Node then return 1
  return 0

/-- `checkReferenceLayer(previousLayer, p1Node, p2Node)`: `-1` if `p1Node` is found first in the previous
layer, `1` if `p2Node` is, `0` if neither is in it. -/
def compareInPreviousLayer (p1Node p2Node : LNodeId) : PortComparatorM Int := do
  return checkReferenceLayer (← get).previousLayer p1Node p2Node

/-- The number of ports of a port's node (`0` without a node). -/
def nodePortCount (n : Option LNodeId) : LayeredM Int := do
  match n with
  | some n => return ((← getNode n).ports.size : Int)
  | none => return 0

/-- The nodes of `n`'s layer, or the previous layer if `n` has no layer (Rust `layer_opt` match in the
long edge case of `compare`). -/
def referenceLayerNodes (n : LNodeId) : PortComparatorM (Array LNodeId) := do
  match (← getNode n).layer with
  | some layer => return (← getLayer layer).nodes
  | none => return (← get).previousLayer

/-- Rust `check_port_model_order(p1, p2, has1, has2)`: compares the port model orders (offset = the
number of ports of `p1`'s node), `0` unless both ports have one. -/
def checkPortModelOrder (p1 p2 : LPortId) (p1HasModelOrder p2HasModelOrder : Bool) : PortComparatorM Int := do
  if p1HasModelOrder && p2HasModelOrder then
    let numberOfPorts ← nodePortCount (← getPort p1).owner
    let graph := (← get).graph
    let p1Order ← portModelOrderValue p1 p2 graph numberOfPorts
    let p2Order ← portModelOrderValue p2 p1 graph numberOfPorts
    return cmpInt p1Order p2Order
  return 0

/-- The transitivity checks at the start of `compare` (indices are allocated for `p1`, then `p2`): Java's
fourth check repeats the second one (`biggerThan.get(p2).contains(p1)`) and so never decides. -/
def relationVerdict (p1 p2 : LPortId) : PortComparatorM (Option Int) := do
  let k1 ← withRelations (·.index p1)
  let k2 ← withRelations (·.index p2)
  let rel := (← get).relations
  if rel.isBigger k1 k2 then return some 1
  if rel.isBigger k2 k1 then return some (-1)
  if rel.isSmaller k1 k2 then return some (-1)
  return none

/-- Records the decision `p1 > p2` (`v > 0`) or `p2 > p1` and returns `±reverseOrder` (the recurring
Rust tail `if v > 0 { update(p1, p2, r); r } else { update(p2, p1, r); -r }`). -/
def recordDecision (p1 p2 : LPortId) (p1Bigger : Bool) (reverseOrder : Int) : PortComparatorM Int := do
  if p1Bigger then
    updateBiggerAndSmaller p1 p2 reverseOrder
    return reverseOrder
  else
    updateBiggerAndSmaller p2 p1 reverseOrder
    return -reverseOrder

/-- The incoming-edge block of `compare` (both ports have incoming edges; `reverseOrder` is already
negated for `WEST`/`NORTH`/`SOUTH`). `none` falls through to the outgoing-edge block. -/
def compareIncoming (p1 p2 : LPortId) (s1 s2 : PortSnapshot) (reverseOrder : Int) : PortComparatorM (Option Int) := do
  let some e1 := s1.incomingFirst | return none
  let some e2 := s2.incomingFirst | return none
  let some p1SourcePort := (← getEdge e1).source | return none
  let some p2SourcePort := (← getEdge e2).source | return none
  let some p1Node := (← getPort p1SourcePort).owner | return none
  let some p2Node := (← getPort p2SourcePort).owner | return none
  if p1Node == p2Node then
    -- both connect to the same node: the first of their source ports on it decides
    for port in (← getNode p1Node).ports do
      if port == p1SourcePort then
        updateBiggerAndSmaller p2 p1 reverseOrder
        return some (-reverseOrder)
      else if port == p2SourcePort then
        updateBiggerAndSmaller p1 p2 reverseOrder
        return some reverseOrder
  let p1NodeType := (← getNode p1Node).type
  let p2NodeType := (← getNode p2Node).type
  let p1Layer ← layerIdOf p1Node
  let p2Layer ← layerIdOf p2Node
  let ownerLayer ← layerIdOf (s1.node.getD p1Node)
  if p1NodeType == .longEdge && p2NodeType == .longEdge && p1Layer == p2Layer && p1Layer == ownerLayer then
    -- both come from long edge dummies in the port's own layer: their order in that layer decides
    let referenceLayer ← referenceLayerNodes p1Node
    let inPrevious := checkReferenceLayer referenceLayer p1Node p2Node
    if inPrevious != 0 then
      let reverseOrder := if s1.side == .east then -reverseOrder else reverseOrder
      return some (← recordDecision p1 p2 (inPrevious > 0) reverseOrder)
  let inPrevious ← compareInPreviousLayer p1Node p2Node
  if inPrevious != 0 then
    return some (← recordDecision p1 p2 (inPrevious > 0) reverseOrder)
  if (← get).portModelOrder then
    let result ← checkPortModelOrder p1 p2 s1.hasModelOrder s2.hasModelOrder
    if result != 0 then
      return some (← recordDecision p1 p2 (result > 0) reverseOrder)
  return none

/-- The outgoing-edge block of `compare` (both ports have outgoing edges; `reverseOrder` is already
negated for `WEST`/`SOUTH`). -/
def compareOutgoing (p1 p2 : LPortId) (s1 s2 : PortSnapshot) (reverseOrder : Int) : PortComparatorM Int := do
  let p1TargetNode := s1.longEdgeTargetNode
  let p2TargetNode := s2.longEdgeTargetNode
  if (← get).strategy == .preferNodes then
    if let (some t1, some t2) := (p1TargetNode, p2TargetNode) then
      let n1 ← getNode t1
      let n2 ← getNode t2
      if n1.internal.modelOrder.isSome && n2.internal.modelOrder.isSome then
        let graph := (← get).graph
        -- Java unboxes `graph.getProperty(MAX_MODEL_ORDER_NODES)` for the `int offset` argument
        if graph.maxModelOrderNodesNull then throw (IO.userError maxModelOrderNodesNullError)
        let p1Order := CMGroupModelOrderCalculator.calculateModelOrderOrGroupModelOrderOf graph n1 n2 graph.maxModelOrderNodes
        let p2Order := CMGroupModelOrderCalculator.calculateModelOrderOrGroupModelOrderOf graph n2 n1 graph.maxModelOrderNodes
        return ← recordDecision p1 p2 (p1Order > p2Order) reverseOrder
  if (← get).portModelOrder then
    let result ← checkPortModelOrder p1 p2 s1.hasModelOrder s2.hasModelOrder
    if result != 0 then
      return ← recordDecision p1 p2 (result > 0) reverseOrder
  let graph := (← get).graph
  let e1 := s1.outgoingFirst.getD default
  let e2 := s2.outgoingFirst.getD default
  let mut p1Order ← edgeModelOrderValue e1 e2 graph ((s1.outgoingLen + s1.incomingLen : Nat) : Int)
  let mut p2Order ← edgeModelOrderValue e2 e1 graph ((s2.outgoingLen + s2.incomingLen : Nat) : Int)
  if let (some t1, some t2) := (p1TargetNode, p2TargetNode) then
    if t1 == t2 then
      return ← recordDecision p1 p2 (p1Order > p2Order) reverseOrder
  -- `targetNodeModelOrder.containsKey(target)` for each target separately (`null` is no key)
  if let some orders := (← get).targetNodeModelOrder then
    if let some t1 := p1TargetNode then
      if let some order := orders.get? t1 then
        p1Order := order
    if let some t2 := p2TargetNode then
      if let some order := orders.get? t2 then
        p2Order := order
  recordDecision p1 p2 (p1Order > p2Order) reverseOrder

/-- The tail of `compare`: incoming before outgoing ports, then port model order, then `p1 < p2`. -/
def compareRemaining (p1 p2 : LPortId) (s1 s2 : PortSnapshot) (reverseOrder : Int) : PortComparatorM Int := do
  if s1.incomingFirst.isSome && s2.outgoingFirst.isSome then
    updateBiggerAndSmaller p1 p2 reverseOrder
    return 1
  else if s1.outgoingFirst.isSome && s2.incomingFirst.isSome then
    updateBiggerAndSmaller p2 p1 reverseOrder
    return -1
  else if s1.hasModelOrder && s2.hasModelOrder then
    let numberOfPorts ← nodePortCount s1.node
    let graph := (← get).graph
    let p1Order ← portModelOrderValue p1 p2 graph numberOfPorts
    let p2Order ← portModelOrderValue p2 p1 graph numberOfPorts
    let reverseOrder := if s1.side == .west || s1.side == .south then -reverseOrder else reverseOrder
    recordDecision p1 p2 (p1Order > p2Order) reverseOrder
  else
    updateBiggerAndSmaller p2 p1 reverseOrder
    return -reverseOrder

/-- Rust `compare(original_p1, original_p2)` in `PortComparatorM`: `-1`, `0` or `1`. -/
def compareM (p1 p2 : LPortId) : PortComparatorM Int := do
  if let some v := (← relationVerdict p1 p2) then return v
  let s1 ← portSnapshot p1
  let s2 ← portSnapshot p2
  if s1.side != s2.side then
    -- NORTH < EAST < SOUTH < WEST (`PortSide` ordinals)
    let result := cmpInt (ElkEnum.ordinal s1.side) (ElkEnum.ordinal s2.side)
    if result > 0 then updateBiggerAndSmaller p1 p2 1 else updateBiggerAndSmaller p2 p1 1
    return result
  let mut reverseOrder : Int := 1
  if s1.incomingFirst.isSome && s2.incomingFirst.isSome then
    if s1.side == .west || s1.side == .north || s1.side == .south then
      reverseOrder := -reverseOrder
    if let some v := (← compareIncoming p1 p2 s1 s2 reverseOrder) then return v
  if s1.outgoingFirst.isSome && s2.outgoingFirst.isSome then
    if s1.side == .west || s1.side == .south then
      reverseOrder := -reverseOrder
    return ← compareOutgoing p1 p2 s1 s2 reverseOrder
  compareRemaining p1 p2 s1 s2 reverseOrder

/-- Rust `compare(p1, p2)` on a comparator value: the result (`-1`, `0`, `1`) and the comparator with
the updated transitive relations. -/
def compare (c : ModelOrderPortComparator) (p1 p2 : LPortId) : LayeredM (Int × ModelOrderPortComparator) :=
  (compareM p1 p2).run c

end ModelOrderPortComparator

end Elk.Alg.Layered.Intermediate.Preserveorder
