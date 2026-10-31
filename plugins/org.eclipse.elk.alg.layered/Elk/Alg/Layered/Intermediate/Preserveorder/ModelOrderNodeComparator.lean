import Std.Data.HashSet
import Elk.Alg.Layered.Intermediate.Preserveorder.ModelOrderPortComparator
/-!
# `org.eclipse.elk.alg.layered.intermediate.preserveorder.ModelOrderNodeComparator`

Port of `ModelOrderNodeComparator.java` (elk-rs `model_order_node_comparator.rs`): compares two nodes of one
layer by the order of the previous-layer nodes they are connected to (for dummy nodes or with
`PREFER_EDGES`), by the long edge feedback structure of helper dummies, and by their (group) model
order. Like the port comparator it is stateful: every decision is recorded in transitive
`biggerThan`/`smallerThan` relations (`ModelOrderRelations`) consulted first by later comparisons, so
the comparison sequence of the sorting algorithm matters (Rust and Java sort with insertion sort,
`SortByInputModelProcessor.insertionSort`).

## API (for `LayerSweepCrossingMinimizer` and `SortByInputModelProcessor`)
* `ModelOrderNodeComparator.new graph previousLayer orderingStrategy longEdgeNodeOrder
  groupOrderStrategy beforePorts` (Rust `new`; `graph` is a `ModelOrderGraphContext`, see
  `CMGroupModelOrderCalculator` — use `ModelOrderGraphContext.ofGraph g` or `.unavailable` to
  reproduce a Rust `try_lock` failure on a locked graph).
* `compare c n1 n2 : LayeredM (Int × ModelOrderNodeComparator)` — the Rust `i32` result (`-1`, `0`,
  `1`) and the updated comparator; `compareM n1 n2 : NodeComparatorM Int` is the same in
  `StateT ModelOrderNodeComparator LayeredM`.
* `clearTransitiveOrdering`, `resetForPreviousLayer`, `resetForPreviousLayerSlice` are pure updates.

## Java semantics (ELK Java is the reference; elk-rs differed)
* Java's fourth transitivity check repeats the second one (`biggerThan.get(n2).contains(n1)`) and so
  never decides (elk-rs tested `smallerThan(n2) ∋ n1`).
* The previous-layer check iterates the previous layer and the first of the two source nodes found
  decides, also when the other one is not in it (elk-rs decided only when both were in it).

## Deviations from Java (kept from elk-rs)
* A `visiting` set of the pairs currently being compared makes a recursive comparison of the same
  pair return `0` (Java can recurse without bound).
* `layer_id` is `Layer.id as usize` (`0` without a layer); the "previous layer" of a node in layer id
  `0` does not exist (Rust `checked_sub`).
* Missing ports, edge ends or owners make `handle_helper_dummy_nodes` return `0` instead of throwing.
-/
namespace Elk.Alg.Layered.Intermediate.Preserveorder

open Elk.Graph Elk.Core.Options Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

/-- Rust `ModelOrderNodeComparator`. -/
structure ModelOrderNodeComparator where
  /-- `previous_layer`. -/
  previousLayer : Array LNodeId := #[]
  /-- `graph` (the options read through it). -/
  graph : ModelOrderGraphContext := {}
  /-- `ordering_strategy` (`CONSIDER_MODEL_ORDER_STRATEGY`). -/
  orderingStrategy : OrderingStrategy := .none
  /-- `_group_order_strategy` (stored, unused, as in Rust/Java). -/
  groupOrderStrategy : GroupOrderStrategy := .onlyWithinGroup
  /-- `relations` (Java `biggerThan`/`smallerThan`). -/
  relations : ModelOrderRelations LNodeId := {}
  /-- `long_edge_node_order` (`CONSIDER_MODEL_ORDER_LONG_EDGE_STRATEGY`). -/
  longEdgeNodeOrder : LongEdgeOrderingStrategy := .equal
  /-- `before_ports`: whether the comparator runs before the ports are sorted. -/
  beforePorts : Bool := false
  /-- `visiting`: the `(n1, n2)` pairs whose comparison is in progress (recursion guard). -/
  visiting : Std.HashSet (LNodeId × LNodeId) := {}
  deriving Inhabited

/-- `ModelOrderNodeComparator` as a state over `LayeredM`. -/
abbrev NodeComparatorM := StateT ModelOrderNodeComparator LayeredM

/-- Rust `has_model_order(node)`. -/
def hasModelOrder (n : LNodeId) : LayeredM Bool := do
  return (← getNode n).internal.modelOrder.isSome

/-- Rust `first_incoming_port(node)`: the first port with incoming edges. -/
def firstIncomingPort (n : LNodeId) : LayeredM (Option LPortId) := do
  for p in (← getNode n).ports do
    if !(← getPort p).incomingEdges.isEmpty then return some p
  return none

/-- Rust `first_incoming_source_port(node)`: source of the first incoming edge of `firstIncomingPort`. -/
def firstIncomingSourcePort (n : LNodeId) : LayeredM (Option LPortId) := do
  let some port ← firstIncomingPort n | return none
  let some e := (← getPort port).incomingEdges[0]? | return none
  return (← getEdge e).source

/-- Rust `first_outgoing_port(node)`: the first port with outgoing edges. -/
def firstOutgoingPort (n : LNodeId) : LayeredM (Option LPortId) := do
  for p in (← getNode n).ports do
    if !(← getPort p).outgoingEdges.isEmpty then return some p
  return none

/-- Rust `first_outgoing_target_port(node)`: target of the first outgoing edge of `firstOutgoingPort`. -/
def firstOutgoingTargetPort (n : LNodeId) : LayeredM (Option LPortId) := do
  let some port ← firstOutgoingPort n | return none
  let some e := (← getPort port).outgoingEdges[0]? | return none
  return (← getEdge e).target

/-- Rust `first_source_port_to_previous_layer(node)`: over the node's ports in order, the source port
of the first incoming edge of the first port whose first incoming edge comes from layer id
`layer_id(node) - 1` (`none` for layer id `0`). -/
def firstSourcePortToPreviousLayer (n : LNodeId) : LayeredM (Option LPortId) := do
  let nodeLayer ← layerIdOf n
  if nodeLayer == 0 then return none
  let prevLayer := nodeLayer - 1
  for port in (← getNode n).ports do
    if let some e := (← getPort port).incomingEdges[0]? then
      if let some sourcePort := (← getEdge e).source then
        if let some sourceNode := (← getPort sourcePort).owner then
          if (← layerIdOf sourceNode) == prevLayer then
            return some sourcePort
  return none

/-- The long edge feedback data of a dummy for `handle_helper_dummy_nodes` (both-long-edge case):
the source port of its first incoming edge, whether its source / target node is in its own layer, and
the reference node (that node, else the dummy itself). `none` when an end is missing. -/
def feedbackReference (n : LNodeId) : LayeredM (Option (LPortId × Bool × Bool × LNodeId)) := do
  let some sourcePort ← firstIncomingSourcePort n | return none
  let some targetPort ← firstOutgoingTargetPort n | return none
  let some sourceNode := (← getPort sourcePort).owner | return none
  let some targetNode := (← getPort targetPort).owner | return none
  let layer ← layerIdOf n
  if (← layerIdOf sourceNode) == layer then return some (sourcePort, true, false, sourceNode)
  if (← layerIdOf targetNode) == layer then return some (sourcePort, false, true, targetNode)
  return some (sourcePort, false, false, n)

/-- The ends of a long edge dummy for `handle_helper_dummy_nodes` (one-dummy cases): the owners of
the first incoming edge's source and the first outgoing edge's target. -/
def dummyEnds (n : LNodeId) : LayeredM (Option (LNodeId × LNodeId)) := do
  let some sourcePort ← firstIncomingSourcePort n | return none
  let some targetPort ← firstOutgoingTargetPort n | return none
  let some sourceNode := (← getPort sourcePort).owner | return none
  let some targetNode := (← getPort targetPort).owner | return none
  return some (sourceNode, targetNode)

namespace ModelOrderNodeComparator

/-- `new ModelOrderNodeComparator(graph, previousLayer, orderingStrategy, longEdgeOrderingStrategy,
groupOrderStrategy, beforePorts)`. -/
def new (graph : ModelOrderGraphContext) (previousLayer : Array LNodeId) (orderingStrategy : OrderingStrategy)
    (longEdgeNodeOrder : LongEdgeOrderingStrategy) (groupOrderStrategy : GroupOrderStrategy) (beforePorts : Bool) :
    ModelOrderNodeComparator :=
  { previousLayer := previousLayer, graph := graph
    orderingStrategy := orderingStrategy, groupOrderStrategy := groupOrderStrategy
    longEdgeNodeOrder := longEdgeNodeOrder, beforePorts := beforePorts }

/-- `clearTransitiveOrdering()` (Rust also clears `visiting`). -/
def clearTransitiveOrdering (c : ModelOrderNodeComparator) : ModelOrderNodeComparator :=
  { c with relations := {}, visiting := {} }

/-- Rust `reset_for_previous_layer(previous_layer)`: new previous layer, no relations. -/
def resetForPreviousLayer (c : ModelOrderNodeComparator) (previousLayer : Array LNodeId) : ModelOrderNodeComparator :=
  { c with previousLayer := previousLayer
           relations := {}, visiting := {} }

/-- Rust `reset_for_previous_layer_slice(previous_layer)` (same as `resetForPreviousLayer`). -/
def resetForPreviousLayerSlice (c : ModelOrderNodeComparator) (previousLayer : Array LNodeId) : ModelOrderNodeComparator :=
  c.resetForPreviousLayer previousLayer

/-- Applies `f` to the relations, keeping them uniquely referenced. -/
@[inline] def withRelations {α : Type} (f : ModelOrderRelations LNodeId → α × ModelOrderRelations LNodeId) :
    NodeComparatorM α :=
  modifyGet fun c =>
    let rel := c.relations
    let c := { c with relations := {} }
    let (a, rel) := f rel
    (a, { c with relations := rel })

/-- Rust `update_bigger_and_smaller(bigger, smaller)` (Java `updateBiggerAndSmallerAssociations`). -/
def updateBiggerAndSmaller (bigger smaller : LNodeId) : NodeComparatorM Unit :=
  withRelations fun rel =>
    let (bi, rel) := rel.index bigger
    let (si, rel) := rel.index smaller
    ((), rel.record bi si)

/-- Records `n1 > n2` and returns `1`, or records `n2 > n1` and returns `-1`. -/
def recordDecision (n1 n2 : LNodeId) (n1Bigger : Bool) : NodeComparatorM Int := do
  if n1Bigger then
    updateBiggerAndSmaller n1 n2
    return 1
  else
    updateBiggerAndSmaller n2 n1
    return -1

/-- Records the result `compared` of a helper dummy comparison (`> 0`: `n1 > n2`, else `n2 > n1`). -/
def recordCompared (n1 n2 : LNodeId) (compared : Int) : NodeComparatorM Unit := do
  if compared > 0 then updateBiggerAndSmaller n1 n2 else updateBiggerAndSmaller n2 n1

/-- The transitivity checks at the start of `compare` (indices are allocated for `n1`, then `n2`); Java's
fourth check (`biggerThan.get(n2).contains(n1)`, a repetition of the second) never decides. -/
def relationVerdict (n1 n2 : LNodeId) : NodeComparatorM (Option Int) := do
  -- one pass over the relations: index `n1`, then `n2`, then the three checks
  withRelations fun rel =>
    let (k1, rel) := rel.index n1
    let (k2, rel) := rel.index n2
    let v : Option Int :=
      if rel.isBigger k1 k2 then some 1
      else if rel.isBigger k2 k1 then some (-1)
      else if rel.isSmaller k1 k2 then some (-1)
      else none
    (v, rel)

/-- `for (LNode previousNode : previousLayer)`: `-1` if `p1Node` is found first, `1` if `p2Node` is,
`0` if neither is in the previous layer. -/
def compareInPreviousLayer (p1Node p2Node : LNodeId) : NodeComparatorM Int := do
  return ModelOrderPortComparator.checkReferenceLayer (← get).previousLayer p1Node p2Node

/-- `getModelOrderFromConnectedEdges(node)`: `MODEL_ORDER` of the first incoming edge of the first port
with incoming edges (Java's unboxing `NullPointerException`, `edgeModelOrderNullError`, when it has
none), else `longEdgeNodeOrder.returnValue()`. -/
def modelOrderFromConnectedEdges (n : LNodeId) : NodeComparatorM Int := do
  if let some port := (← firstIncomingPort n) then
    if let some e := (← getPort port).incomingEdges[0]? then
      -- Java returns `edge.getProperty(MODEL_ORDER)` as `int`: unboxing `null` throws
      let some order := (← getEdge e).internal.modelOrder | throw (IO.userError edgeModelOrderNullError)
      return order
  return (← get).longEdgeNodeOrder.returnValue

/-- `compare` when both nodes have a source port in the previous layer: the same source node orders
by its port order (fallback: edge model order), different nodes by their previous-layer positions.
`none` falls through. -/
def compareSourcePorts (n1 n2 : LNodeId) (p1SourcePort p2SourcePort : LPortId) : NodeComparatorM (Option Int) := do
  let some p1Node := (← getPort p1SourcePort).owner | return none
  let some p2Node := (← getPort p2SourcePort).owner | return none
  if p1Node == p2Node then
    for port in (← getNode p1Node).ports do
      if port == p1SourcePort then
        updateBiggerAndSmaller n2 n1
        return some (-1)
      else if port == p2SourcePort then
        updateBiggerAndSmaller n1 n2
        return some 1
    let n1EdgeOrder ← modelOrderFromConnectedEdges n1
    let n2EdgeOrder ← modelOrderFromConnectedEdges n2
    return some (← recordDecision n1 n2 (n1EdgeOrder > n2EdgeOrder))
  let inPrevious ← compareInPreviousLayer p1Node p2Node
  if inPrevious != 0 then
    return some (← recordDecision n1 n2 (inPrevious > 0))
  return none

/-- The final model order decision of `compare` (both nodes with `MODEL_ORDER`: their (group) model
orders with offset `MAX_MODEL_ORDER_NODES`; otherwise `n1 < n2`). -/
def compareByModelOrder (n1 n2 : LNodeId) (n1HasModelOrder n2HasModelOrder : Bool) : NodeComparatorM Int := do
  if n1HasModelOrder && n2HasModelOrder then
    let graph := (← get).graph
    -- Java unboxes `graph.getProperty(MAX_MODEL_ORDER_NODES)` for the `int offset` argument
    if graph.maxModelOrderNodesNull then throw (IO.userError maxModelOrderNodesNullError)
    let nd1 ← getNode n1
    let nd2 ← getNode n2
    let n1Order := CMGroupModelOrderCalculator.calculateModelOrderOrGroupModelOrderOf graph nd1 nd2 graph.maxModelOrderNodes
    let n2Order := CMGroupModelOrderCalculator.calculateModelOrderOrGroupModelOrderOf graph nd2 nd1 graph.maxModelOrderNodes
    recordDecision n1 n2 (n1Order > n2Order)
  else
    updateBiggerAndSmaller n2 n1
    return -1

/-- The `before_ports` decision of `handle_helper_dummy_nodes` for two long edge dummies with the same
reference node (`none`: no case applies, fall through to comparing the reference nodes). -/
def beforePortsFeedbackDecision (n1 n2 : LNodeId) (n1SourcePort n2SourcePort : LPortId)
    (n1SourceFeedback n1TargetFeedback n2SourceFeedback n2TargetFeedback : Bool) : NodeComparatorM (Option Int) := do
  if n1SourceFeedback && n2SourceFeedback then
    -- a fresh port comparator (Java passes `n2TargetFeedbackNode` as `portModelOrder`)
    let graph := (← get).graph
    let previousLayer := (← get).previousLayer
    let orderingStrategy := (← get).orderingStrategy
    let portComparator := ModelOrderPortComparator.new graph previousLayer orderingStrategy none n2TargetFeedback
    let (returnValue, _) ← (portComparator.compare n1SourcePort n2SourcePort : LayeredM _)
    if returnValue > 0 then
      updateBiggerAndSmaller n2 n1
      return some 1
    updateBiggerAndSmaller n1 n2
    return some (-1)
  else if n1SourceFeedback && n2TargetFeedback then
    updateBiggerAndSmaller n2 n1
    return some 1
  else if n1TargetFeedback && n2SourceFeedback then
    updateBiggerAndSmaller n1 n2
    return some (-1)
  else if n1TargetFeedback && n2TargetFeedback then
    return some 0
  return none

mutual

/-- Rust `compare(n1, n2)` in `NodeComparatorM`: `-1`, `0` or `1`. Recursion (through
`handleHelperDummyNodes`) on a pair that is already being compared returns `0`. -/
partial def compareM (n1 n2 : LNodeId) : NodeComparatorM Int := do
  let key := (n1, n2)
  if (← get).visiting.contains key then return 0
  modify fun c => { c with visiting := c.visiting.insert key }
  let value ← compareBody n1 n2
  modify fun c => { c with visiting := c.visiting.erase key }
  return value

/-- Body of `compare` (every Rust `return` goes through `finish_compare`, done by `compareM`). -/
partial def compareBody (n1 n2 : LNodeId) : NodeComparatorM Int := do
  if let some v := (← relationVerdict n1 n2) then return v
  let n1HasModelOrder ← hasModelOrder n1
  let n2HasModelOrder ← hasModelOrder n2
  if (← get).orderingStrategy == .preferEdges || !n1HasModelOrder || !n2HasModelOrder then
    if let some v := (← compareByEdges n1 n2 n1HasModelOrder n2HasModelOrder) then return v
  compareByModelOrder n1 n2 n1HasModelOrder n2HasModelOrder

/-- The connection-based part of `compare` (`PREFER_EDGES` or a node without model order). -/
partial def compareByEdges (n1 n2 : LNodeId) (n1HasModelOrder n2HasModelOrder : Bool) : NodeComparatorM (Option Int) := do
  let p1SourcePort ← firstSourcePortToPreviousLayer n1
  let p2SourcePort ← firstSourcePortToPreviousLayer n2
  if let (some s1, some s2) := (p1SourcePort, p2SourcePort) then
    if let some v := (← compareSourcePorts n1 n2 s1 s2) then return some v
  if p1SourcePort.isSome != p2SourcePort.isSome then
    let compared ← handleHelperDummyNodes n1 n2
    if compared != 0 then
      recordCompared n1 n2 compared
      return some compared
    if !n1HasModelOrder || !n2HasModelOrder then
      let n1EdgeOrder ← modelOrderFromConnectedEdges n1
      let n2EdgeOrder ← modelOrderFromConnectedEdges n2
      return some (← recordDecision n1 n2 (n1EdgeOrder > n2EdgeOrder))
  if p1SourcePort.isNone && p2SourcePort.isNone then
    let compared ← handleHelperDummyNodes n1 n2
    if compared != 0 then
      recordCompared n1 n2 compared
      return some compared
  return none

/-- Rust `handle_helper_dummy_nodes(n1, n2)`: orders (feedback) long edge dummies by their source or
target node in the same layer; `0` for two normal nodes or when nothing applies. -/
partial def handleHelperDummyNodes (n1 n2 : LNodeId) : NodeComparatorM Int := do
  let n1Type := (← getNode n1).type
  let n2Type := (← getNode n2).type
  if n1Type == .longEdge && n2Type == .normal then
    let some (dummySourceNode, dummyTargetNode) ← dummyEnds n1 | return 0
    let dummyLayerId ← layerIdOf n1
    if (← layerIdOf dummySourceNode) != dummyLayerId && (← layerIdOf dummyTargetNode) != dummyLayerId then
      return 0
    if dummySourceNode == n2 || dummyTargetNode == n2 then
      updateBiggerAndSmaller n1 n2
      return 1
    compareM dummySourceNode n2
  else if n1Type == .normal && n2Type == .longEdge then
    let some (dummySourceNode, dummyTargetNode) ← dummyEnds n2 | return 0
    -- Rust (and Java) take the layer id of `n1` here
    let dummyLayerId ← layerIdOf n1
    if (← layerIdOf dummySourceNode) != dummyLayerId && (← layerIdOf dummyTargetNode) != dummyLayerId then
      return 0
    if dummySourceNode == n1 || dummyTargetNode == n1 then
      updateBiggerAndSmaller n2 n1
      return -1
    compareM n1 dummySourceNode
  else if n1Type == .longEdge && n2Type == .longEdge then
    handleLongEdgePair n1 n2
  else
    return 0

/-- The both-long-edge case of `handle_helper_dummy_nodes`. -/
partial def handleLongEdgePair (n1 n2 : LNodeId) : NodeComparatorM Int := do
  let some (n1SourcePort, n1SourceFeedback, n1TargetFeedback, n1Reference) ← feedbackReference n1 | return 0
  let some (n2SourcePort, n2SourceFeedback, n2TargetFeedback, n2Reference) ← feedbackReference n2 | return 0
  if n1Reference == n2Reference then
    if (← get).beforePorts then
      if let some v := (← beforePortsFeedbackDecision n1 n2 n1SourcePort n2SourcePort
          n1SourceFeedback n1TargetFeedback n2SourceFeedback n2TargetFeedback) then
        return v
    else
      for port in (← getNode n1Reference).ports do
        if port == n1SourcePort then
          updateBiggerAndSmaller n2 n1
          return -1
        else if port == n2SourcePort then
          updateBiggerAndSmaller n1 n2
          return 1
  compareM n1Reference n2Reference

end

/-- Rust `compare(n1, n2)` on a comparator value: the result (`-1`, `0`, `1`) and the comparator with
the updated transitive relations. -/
def compare (c : ModelOrderNodeComparator) (n1 n2 : LNodeId) : LayeredM (Int × ModelOrderNodeComparator) :=
  (compareM n1 n2).run c

end ModelOrderNodeComparator

/-! ## Pure comparison on the arena (Lean only)

`NodeCmpEnv.compare` is `ModelOrderNodeComparator.compareM` as a pure function of the arena (the
comparator never writes it): the read-only fields (`NodeCmpEnv`) and the relations are separate
arguments, and the `visiting` set is the stack of pairs whose comparison is in progress, passed down
the recursion (`compareM` inserts a pair before its body and erases it afterwards, so between two
top-level comparisons the set is empty and inside one it is exactly the pairs of the enclosing calls).
Every relation update (`index` calls and `record`) happens in the same order as in `compareM`, which
is kept as the reference (differential test `layered.intermediate.preserveorder.pureComparators`).
Results are `-1`, `0`, `1`; `failedOffset`/`failedEdgeOrder` stand for Java's exceptions and travel up
like a result (every caller returns them at once), `fallThrough` is an internal "no decision". -/

/-- The read-only part of a `ModelOrderNodeComparator` (for `NodeCmpEnv.compare`). -/
structure NodeCmpEnv where
  /-- `previous_layer`. -/
  previousLayer : Array LNodeId := #[]
  /-- `graph`. -/
  graph : ModelOrderGraphContext := {}
  /-- `ordering_strategy` (for the port comparator of the `before_ports` case). -/
  orderingStrategy : OrderingStrategy := .none
  /-- `ordering_strategy == PREFER_EDGES`. -/
  preferEdges : Bool := false
  /-- `long_edge_node_order.returnValue()`. -/
  longEdgeReturn : Int := 0
  /-- `before_ports`. -/
  beforePorts : Bool := false
  deriving Inhabited

namespace NodeCmpEnv

/-- `new ModelOrderNodeComparator(graph, previousLayer, orderingStrategy, longEdgeOrderingStrategy,
groupOrderStrategy, beforePorts)` without the relations (the group order strategy is unused). -/
def new (graph : ModelOrderGraphContext) (previousLayer : Array LNodeId) (orderingStrategy : OrderingStrategy)
    (longEdgeNodeOrder : LongEdgeOrderingStrategy) (beforePorts : Bool) : NodeCmpEnv :=
  { previousLayer, graph, orderingStrategy, preferEdges := orderingStrategy == .preferEdges
    longEdgeReturn := longEdgeNodeOrder.returnValue, beforePorts }

/-- `resetForPreviousLayer(previousLayer)` (the caller resets the relations). -/
def resetForPreviousLayer (env : NodeCmpEnv) (previousLayer : Array LNodeId) : NodeCmpEnv :=
  { env with previousLayer }

/-- Java's `maxModelOrderNodesNullError`. -/
@[inline] def failedOffset : Int := 2

/-- Java's `edgeModelOrderNullError`. -/
@[inline] def failedEdgeOrder : Int := 3

/-- No decision (fall through). -/
@[inline] def fallThrough : Int := 4

/-- Whether a result is a failure (`failedOffset`, `failedEdgeOrder`). -/
@[inline] def isFailure (r : Int) : Bool := r == failedOffset || r == failedEdgeOrder

/-- `updateBiggerAndSmaller(bigger, smaller)`. -/
@[inline] def upd (rel : ModelOrderRelations LNodeId) (bigger smaller : LNodeId) : ModelOrderRelations LNodeId :=
  let (bi, rel) := rel.index bigger
  let (si, rel) := rel.index smaller
  rel.record bi si

/-- `recordDecision(n1, n2, n1Bigger)`. -/
@[inline] def recordDecision (rel : ModelOrderRelations LNodeId) (n1 n2 : LNodeId) (n1Bigger : Bool) :
    Int × ModelOrderRelations LNodeId :=
  if n1Bigger then (1, upd rel n1 n2) else (-1, upd rel n2 n1)

/-- `recordCompared(n1, n2, compared)`. -/
@[inline] def recordCompared (rel : ModelOrderRelations LNodeId) (n1 n2 : LNodeId) (compared : Int) :
    ModelOrderRelations LNodeId :=
  if compared > 0 then upd rel n1 n2 else upd rel n2 n1

/-- `firstIncomingPort` from `ports[i]` on. -/
partial def firstIncomingPortFrom (a : LGraphArena) (ports : Array LPortId) (i : Nat) : Option LPortId :=
  if h : i < ports.size then
    let p := ports[i]
    if !(a.port p).incomingEdges.isEmpty then some p else firstIncomingPortFrom a ports (i + 1)
  else none

/-- `firstOutgoingPort` from `ports[i]` on. -/
partial def firstOutgoingPortFrom (a : LGraphArena) (ports : Array LPortId) (i : Nat) : Option LPortId :=
  if h : i < ports.size then
    let p := ports[i]
    if !(a.port p).outgoingEdges.isEmpty then some p else firstOutgoingPortFrom a ports (i + 1)
  else none

/-- `firstIncomingSourcePort` on the arena. -/
def firstIncomingSourcePortIn (a : LGraphArena) (n : LNodeId) : Option LPortId :=
  match firstIncomingPortFrom a (a.node n).ports 0 with
  | some port =>
    match (a.port port).incomingEdges[0]? with
    | some e => (a.edge e).source
    | none => none
  | none => none

/-- `firstOutgoingTargetPort` on the arena. -/
def firstOutgoingTargetPortIn (a : LGraphArena) (n : LNodeId) : Option LPortId :=
  match firstOutgoingPortFrom a (a.node n).ports 0 with
  | some port =>
    match (a.port port).outgoingEdges[0]? with
    | some e => (a.edge e).target
    | none => none
  | none => none

/-- The port loop of `firstSourcePortToPreviousLayer` from `ports[i]` on. -/
partial def sourcePortInLayerFrom (a : LGraphArena) (ports : Array LPortId) (prevLayer : Nat) (i : Nat) : Option LPortId :=
  if h : i < ports.size then
    match (a.port ports[i]).incomingEdges[0]? with
    | some e =>
      match (a.edge e).source with
      | some sourcePort =>
        match (a.port sourcePort).owner with
        | some sourceNode =>
          if PortCmpEnv.layerIdIn a sourceNode == prevLayer then some sourcePort
          else sourcePortInLayerFrom a ports prevLayer (i + 1)
        | none => sourcePortInLayerFrom a ports prevLayer (i + 1)
      | none => sourcePortInLayerFrom a ports prevLayer (i + 1)
    | none => sourcePortInLayerFrom a ports prevLayer (i + 1)
  else none

/-- `firstSourcePortToPreviousLayer` on the arena. -/
def firstSourcePortToPreviousLayerIn (a : LGraphArena) (n : LNodeId) : Option LPortId :=
  let nodeLayer := PortCmpEnv.layerIdIn a n
  if nodeLayer == 0 then none else sourcePortInLayerFrom a (a.node n).ports (nodeLayer - 1) 0

/-- `feedbackReference` on the arena. -/
def feedbackReferenceIn (a : LGraphArena) (n : LNodeId) : Option (LPortId × Bool × Bool × LNodeId) :=
  match firstIncomingSourcePortIn a n, firstOutgoingTargetPortIn a n with
  | some sourcePort, some targetPort =>
    match (a.port sourcePort).owner, (a.port targetPort).owner with
    | some sourceNode, some targetNode =>
      let layer := PortCmpEnv.layerIdIn a n
      if PortCmpEnv.layerIdIn a sourceNode == layer then some (sourcePort, true, false, sourceNode)
      else if PortCmpEnv.layerIdIn a targetNode == layer then some (sourcePort, false, true, targetNode)
      else some (sourcePort, false, false, n)
    | _, _ => none
  | _, _ => none

/-- `dummyEnds` on the arena. -/
def dummyEndsIn (a : LGraphArena) (n : LNodeId) : Option (LNodeId × LNodeId) :=
  match firstIncomingSourcePortIn a n, firstOutgoingTargetPortIn a n with
  | some sourcePort, some targetPort =>
    match (a.port sourcePort).owner, (a.port targetPort).owner with
    | some sourceNode, some targetNode => some (sourceNode, targetNode)
    | _, _ => none
  | _, _ => none

/-- `modelOrderFromConnectedEdges` on the arena (`none`: Java's `edgeModelOrderNullError`). -/
def modelOrderFromConnectedEdgesIn (a : LGraphArena) (env : NodeCmpEnv) (n : LNodeId) : Option Int :=
  match firstIncomingPortFrom a (a.node n).ports 0 with
  | some port =>
    match (a.port port).incomingEdges[0]? with
    | some e => (a.edge e).internal.modelOrder
    | none => some env.longEdgeReturn
  | none => some env.longEdgeReturn

/-- Which of two ports comes first in `ports[i:]`: `1` for `x`, `2` for `y`, `0` if neither occurs. -/
partial def firstOfTwo (ports : Array LPortId) (x y : LPortId) (i : Nat) : UInt8 :=
  if h : i < ports.size then
    let p := ports[i]
    if p.idx == x.idx then 1 else if p.idx == y.idx then 2 else firstOfTwo ports x y (i + 1)
  else 0

/-- The edge model order decision (`n1EdgeOrder > n2EdgeOrder`) of `compareSourcePorts`/`compareByEdges`. -/
@[inline] def edgeOrderDecision (a : LGraphArena) (env : NodeCmpEnv) (rel : ModelOrderRelations LNodeId)
    (n1 n2 : LNodeId) : Int × ModelOrderRelations LNodeId :=
  match modelOrderFromConnectedEdgesIn a env n1 with
  | none => (failedEdgeOrder, rel)
  | some o1 =>
    match modelOrderFromConnectedEdgesIn a env n2 with
    | none => (failedEdgeOrder, rel)
    | some o2 => recordDecision rel n1 n2 (o1 > o2)

/-- `compareSourcePorts` on the arena (`fallThrough`: `none`). -/
def sourcePorts (a : LGraphArena) (env : NodeCmpEnv) (rel : ModelOrderRelations LNodeId) (n1 n2 : LNodeId)
    (s1 s2 : LPortId) : Int × ModelOrderRelations LNodeId :=
  match (a.port s1).owner, (a.port s2).owner with
  | some p1Node, some p2Node =>
    if p1Node.idx == p2Node.idx then
      match firstOfTwo (a.node p1Node).ports s1 s2 0 with
      | 1 => (-1, upd rel n2 n1)
      | 2 => (1, upd rel n1 n2)
      | _ => edgeOrderDecision a env rel n1 n2
    else
      let inPrevious := PortCmpEnv.referenceIn env.previousLayer p1Node p2Node 0
      if inPrevious != 0 then recordDecision rel n1 n2 (inPrevious > 0) else (fallThrough, rel)
  | _, _ => (fallThrough, rel)

/-- `compareByModelOrder` on the arena. -/
def byModelOrder (a : LGraphArena) (env : NodeCmpEnv) (rel : ModelOrderRelations LNodeId) (n1 n2 : LNodeId)
    (has1 has2 : Bool) : Int × ModelOrderRelations LNodeId :=
  if has1 && has2 then
    let graph := env.graph
    if graph.maxModelOrderNodesNull then (failedOffset, rel)
    else
      let nd1 := a.node n1
      let nd2 := a.node n2
      let o1 := CMGroupModelOrderCalculator.calculateModelOrderOrGroupModelOrderOf graph nd1 nd2 graph.maxModelOrderNodes
      let o2 := CMGroupModelOrderCalculator.calculateModelOrderOrGroupModelOrderOf graph nd2 nd1 graph.maxModelOrderNodes
      recordDecision rel n1 n2 (o1 > o2)
  else (-1, upd rel n2 n1)

/-- `beforePortsFeedbackDecision` on the arena (`fallThrough`: `none`). -/
def beforePortsDecision (a : LGraphArena) (env : NodeCmpEnv) (rel : ModelOrderRelations LNodeId) (n1 n2 : LNodeId)
    (sp1 sp2 : LPortId) (sf1 tf1 sf2 tf2 : Bool) : Int × ModelOrderRelations LNodeId :=
  if sf1 && sf2 then
    -- a fresh port comparator (Java passes `n2TargetFeedbackNode` as `portModelOrder`)
    let penv := PortCmpEnv.new env.graph env.previousLayer env.orderingStrategy none tf2
    let (rv, _) := PortCmpEnv.compareCore a penv {} sp1 sp2
    if rv == PortCmpEnv.failed then (failedOffset, rel)
    else if rv > 0 then (1, upd rel n2 n1)
    else (-1, upd rel n1 n2)
  else if sf1 && tf2 then (1, upd rel n2 n1)
  else if tf1 && sf2 then (-1, upd rel n1 n2)
  else if tf1 && tf2 then (0, rel)
  else (fallThrough, rel)

mutual

/-- `compareM n1 n2` on the arena; `visiting` holds the pairs of the enclosing comparisons. -/
partial def cmp (a : LGraphArena) (env : NodeCmpEnv) (visiting : Array (LNodeId × LNodeId))
    (rel : ModelOrderRelations LNodeId) (n1 n2 : LNodeId) : Int × ModelOrderRelations LNodeId :=
  if visiting.any (fun kv => kv.1.idx == n1.idx && kv.2.idx == n2.idx) then (0, rel)
  else body a env (visiting.push (n1, n2)) rel n1 n2

/-- `compareBody` on the arena. -/
partial def body (a : LGraphArena) (env : NodeCmpEnv) (visiting : Array (LNodeId × LNodeId))
    (rel : ModelOrderRelations LNodeId) (n1 n2 : LNodeId) : Int × ModelOrderRelations LNodeId :=
  let (k1, rel) := rel.index n1
  let (k2, rel) := rel.index n2
  if rel.isBigger k1 k2 then (1, rel)
  else if rel.isBigger k2 k1 then (-1, rel)
  else if rel.isSmaller k1 k2 then (-1, rel)
  else
    let has1 := (a.node n1).internal.modelOrder.isSome
    let has2 := (a.node n2).internal.modelOrder.isSome
    if env.preferEdges || !has1 || !has2 then
      let (r, rel) := byEdges a env visiting rel n1 n2 has1 has2
      if r != fallThrough then (r, rel) else byModelOrder a env rel n1 n2 has1 has2
    else byModelOrder a env rel n1 n2 has1 has2

/-- `compareByEdges` on the arena (`fallThrough`: `none`). -/
partial def byEdges (a : LGraphArena) (env : NodeCmpEnv) (visiting : Array (LNodeId × LNodeId))
    (rel : ModelOrderRelations LNodeId) (n1 n2 : LNodeId) (has1 has2 : Bool) : Int × ModelOrderRelations LNodeId :=
  let s1 := firstSourcePortToPreviousLayerIn a n1
  let s2 := firstSourcePortToPreviousLayerIn a n2
  let (r, rel) := match s1, s2 with
    | some x, some y => sourcePorts a env rel n1 n2 x y
    | _, _ => (fallThrough, rel)
  if r != fallThrough then (r, rel)
  else if s1.isSome != s2.isSome then
    let (compared, rel) := helperDummies a env visiting rel n1 n2
    if isFailure compared then (compared, rel)
    else if compared != 0 then (compared, recordCompared rel n1 n2 compared)
    else if !has1 || !has2 then edgeOrderDecision a env rel n1 n2
    else (fallThrough, rel)
  else if s1.isNone && s2.isNone then
    let (compared, rel) := helperDummies a env visiting rel n1 n2
    if isFailure compared then (compared, rel)
    else if compared != 0 then (compared, recordCompared rel n1 n2 compared)
    else (fallThrough, rel)
  else (fallThrough, rel)

/-- `handleHelperDummyNodes` on the arena. -/
partial def helperDummies (a : LGraphArena) (env : NodeCmpEnv) (visiting : Array (LNodeId × LNodeId))
    (rel : ModelOrderRelations LNodeId) (n1 n2 : LNodeId) : Int × ModelOrderRelations LNodeId :=
  match (a.node n1).type, (a.node n2).type with
  | .longEdge, .normal =>
    match dummyEndsIn a n1 with
    | some (src, tgt) =>
      let l := PortCmpEnv.layerIdIn a n1
      if PortCmpEnv.layerIdIn a src != l && PortCmpEnv.layerIdIn a tgt != l then (0, rel)
      else if src.idx == n2.idx || tgt.idx == n2.idx then (1, upd rel n1 n2)
      else cmp a env visiting rel src n2
    | none => (0, rel)
  | .normal, .longEdge =>
    match dummyEndsIn a n2 with
    | some (src, tgt) =>
      -- Rust (and Java) take the layer id of `n1` here
      let l := PortCmpEnv.layerIdIn a n1
      if PortCmpEnv.layerIdIn a src != l && PortCmpEnv.layerIdIn a tgt != l then (0, rel)
      else if src.idx == n1.idx || tgt.idx == n1.idx then (-1, upd rel n2 n1)
      else cmp a env visiting rel n1 src
    | none => (0, rel)
  | .longEdge, .longEdge => longEdgePair a env visiting rel n1 n2
  | _, _ => (0, rel)

/-- `handleLongEdgePair` on the arena. -/
partial def longEdgePair (a : LGraphArena) (env : NodeCmpEnv) (visiting : Array (LNodeId × LNodeId))
    (rel : ModelOrderRelations LNodeId) (n1 n2 : LNodeId) : Int × ModelOrderRelations LNodeId :=
  match feedbackReferenceIn a n1, feedbackReferenceIn a n2 with
  | some (sp1, sf1, tf1, r1), some (sp2, sf2, tf2, r2) =>
    if r1.idx == r2.idx then
      if env.beforePorts then
        let (v, rel) := beforePortsDecision a env rel n1 n2 sp1 sp2 sf1 tf1 sf2 tf2
        if v != fallThrough then (v, rel) else cmp a env visiting rel r1 r2
      else
        match firstOfTwo (a.node r1).ports sp1 sp2 0 with
        | 1 => (-1, upd rel n2 n1)
        | 2 => (1, upd rel n1 n2)
        | _ => cmp a env visiting rel r1 r2
    else cmp a env visiting rel r1 r2
  | _, _ => (0, rel)

end

/-- `compare(n1, n2)` on the arena with the relations `rel`: the result (`-1`, `0`, `1`, or
`failedOffset`/`failedEdgeOrder` for Java's exceptions) and the updated relations. -/
@[inline] def compareCore (a : LGraphArena) (env : NodeCmpEnv) (rel : ModelOrderRelations LNodeId) (n1 n2 : LNodeId) :
    Int × ModelOrderRelations LNodeId :=
  cmp a env #[] rel n1 n2

/-- The exception text of a failed result. -/
def failureText (r : Int) : String :=
  if r == failedOffset then maxModelOrderNodesNullError else edgeModelOrderNullError

/-- `compare(n1, n2)` on the arena: the result (`-1`, `0`, `1`) and the updated relations, or Java's
exception text. -/
def compare (a : LGraphArena) (env : NodeCmpEnv) (rel : ModelOrderRelations LNodeId) (n1 n2 : LNodeId) :
    Except String (Int × ModelOrderRelations LNodeId) :=
  let (r, rel) := compareCore a env rel n1 n2
  if isFailure r then .error (failureText r) else .ok (r, rel)

end NodeCmpEnv

end Elk.Alg.Layered.Intermediate.Preserveorder
