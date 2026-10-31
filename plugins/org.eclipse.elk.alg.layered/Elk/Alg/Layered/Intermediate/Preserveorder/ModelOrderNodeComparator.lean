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
  let k1 ← withRelations (·.index n1)
  let k2 ← withRelations (·.index n2)
  let rel := (← get).relations
  if rel.isBigger k1 k2 then return some 1
  if rel.isBigger k2 k1 then return some (-1)
  if rel.isSmaller k1 k2 then return some (-1)
  return none

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

end Elk.Alg.Layered.Intermediate.Preserveorder
