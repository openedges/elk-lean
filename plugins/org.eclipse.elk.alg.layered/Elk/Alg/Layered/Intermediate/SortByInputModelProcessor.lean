import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Intermediate.Preserveorder.ModelOrderNodeComparator
/-!
# `org.eclipse.elk.alg.layered.intermediate.SortByInputModelProcessor`

Port of elk-rs `intermediate/sort_by_input_model_processor.rs`. Sorts the nodes of every layer and the
ports of every node (unless its port constraints are `FIXED_ORDER`/`FIXED_POS`) by the input model
order, using the stateful `ModelOrderNodeComparator` / `ModelOrderPortComparator`.

Per layer (in layer order): the layer's `id` is set to its index; the nodes are sorted with a
`beforePorts = true` node comparator; then the ports of each node (in the new node order) are sorted
after computing the node's long edge target model orders (`longEdgeTargetNodePreprocessing`); then the
nodes are sorted again with a `beforePorts = false` comparator (starting from the first sort's
result). The previous layer of layer `0` is its own node list as it was before sorting; for later
layers it is the final order of the previous layer.

Slots: before phase 3 (`SORT_BY_INPUT_ORDER_OF_MODEL`), after `LongEdgeSplitter` and before
`NorthSouthPortPreprocessor`.

## Deviations from Java (Rust is followed)
* Ports are sorted with the same insertion sort as nodes (`insertion_sort_port`) and one comparator
  that is reset per node (Java: `Collections.sort` with a new comparator per node).
* The comparators read the graph options from a private context graph built once per run
  (`build_ordering_context_graph`, here `ModelOrderGraphContext.ofGraph`).
* The monitor task name is `"Sort By Input Model"` (Java appends the ordering strategy) and nothing
  is logged.
* `longEdgeTargetNodePreprocessing` sets `LONG_EDGE_TARGET_NODE` only when a target node exists (Java
  also stores `null`).
* The previous layer of layer `0` is a copy of its unsorted node list (Java uses the layer itself).

## `TARGET_NODE_MODEL_ORDER` storage

The map is the typed field `LNodeInternals.targetNodeModelOrder` (Java/Rust keep it on the node).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Options Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate.Preserveorder LayeredM

namespace SortByInputModelProcessor

/-- `node.getProperty(InternalProperties.TARGET_NODE_MODEL_ORDER)`. -/
def getTargetNodeModelOrder (node : LNodeId) : LayeredM (Option (Array (LNodeId × Int))) := do
  return (← getNode node).internal.targetNodeModelOrder

/-- `node.setProperty(InternalProperties.TARGET_NODE_MODEL_ORDER, map)`. -/
def setTargetNodeModelOrder (node : LNodeId) (m : Array (LNodeId × Int)) : LayeredM Unit :=
  modifyNode node fun n => { n with internal := { n.internal with targetNodeModelOrder := some m } }

/-- Rust `insertion_sort(layer, comparator)`: insertion sort with the stateful node comparator (an
element moves left while `compare(left, element) > 0`), then `clearTransitiveOrdering`. -/
def insertionSortM (layer : Array LNodeId) : NodeComparatorM (Array LNodeId) := do
  let mut layer := layer
  for i in [1:layer.size] do
    let temp := layer[i]!
    let mut j := i
    while j > 0 do
      let r ← ModelOrderNodeComparator.compareM layer[j - 1]! temp
      if r > 0 then
        layer := layer.set! j layer[j - 1]!
        j := j - 1
      else
        break
    layer := layer.set! j temp
  modify ModelOrderNodeComparator.clearTransitiveOrdering
  return layer

/-- `insertionSort(layer, comparator)` on a comparator value: the sorted nodes and the comparator. -/
def insertionSort (layer : Array LNodeId) (comparator : ModelOrderNodeComparator) :
    LayeredM (Array LNodeId × ModelOrderNodeComparator) :=
  (insertionSortM layer).run comparator

/-- Rust `insertion_sort_port(ports, comparator)`: like `insertionSortM` for ports. -/
def insertionSortPortM (ports : Array LPortId) : PortComparatorM (Array LPortId) := do
  let mut ports := ports
  for i in [1:ports.size] do
    let temp := ports[i]!
    let mut j := i
    while j > 0 do
      let r ← ModelOrderPortComparator.compareM ports[j - 1]! temp
      if r > 0 then
        ports := ports.set! j ports[j - 1]!
        j := j - 1
      else
        break
    ports := ports.set! j temp
  modify ModelOrderPortComparator.clearTransitiveOrdering
  return ports

/-- `insertionSortPort(ports, comparator)` on a comparator value: the sorted ports and the comparator. -/
def insertionSortPort (ports : Array LPortId) (comparator : ModelOrderPortComparator) :
    LayeredM (Array LPortId × ModelOrderPortComparator) :=
  (insertionSortPortM ports).run comparator

/-- Rust `get_target_node_from_edge(edge)`: follows the edge through non-normal nodes (their first
outgoing edge) to the long edge target node; a dummy with `LONG_EDGE_TARGET` returns that port's
node. `none` when an end is missing or a non-normal node has no outgoing edge. -/
def getTargetNodeFromEdge (edge : LEdgeId) : LayeredM (Option LNodeId) := do
  let mut edge := edge
  while true do
    let some targetPort := (← getEdge edge).target | return none
    let some targetNode := (← getPort targetPort).owner | return none
    let nd ← getNode targetNode
    if let some longEdgeTarget := nd.internal.longEdgeTarget then
      if let some target := (← getPort longEdgeTarget).owner then
        return some target
    if nd.type != .normal then
      -- `node.outgoing_edges().first()`: the first outgoing edge of the first port that has one
      let some port ← firstOutgoingPort targetNode | return none
      let some next := (← getPort port).outgoingEdges[0]? | return none
      edge := next
      continue
    return some targetNode
  return none

/-- `getTargetNode(port)` (Rust `get_target_node`): the long edge target of the port's first outgoing edge. -/
def getTargetNode (port : LPortId) : LayeredM (Option LNodeId) := do
  match (← getPort port).outgoingEdges[0]? with
  | some edge => getTargetNodeFromEdge edge
  | none => return none

/-- `longEdgeTargetNodePreprocessing(node)` (Rust `long_edge_target_node_preprocessing`): unless the
node already has a `TARGET_NODE_MODEL_ORDER` map (then that is returned), sets `LONG_EDGE_TARGET_NODE`
on every port whose first outgoing edge leads to a target node and maps each target node to the
minimal `MODEL_ORDER` (`Integer.MAX_VALUE` if unset) of those first edges that are not `REVERSED`; the
map is stored on the node. Pairs are in order of first insertion (only lookups are observable). -/
def longEdgeTargetNodePreprocessing (node : LNodeId) : LayeredM (Array (LNodeId × Int)) := do
  if let some existing ← getTargetNodeModelOrder node then return existing
  let mut orders : Std.HashMap LNodeId Int := {}
  let mut keys : Array LNodeId := #[]
  for port in (← getNode node).ports do
    let some firstEdge := (← getPort port).outgoingEdges[0]? | continue
    let some targetNode ← getTargetNodeFromEdge firstEdge | continue
    modifyPort port fun p => { p with internal := { p.internal with longEdgeTargetNode := some targetNode } }
    let prevOrder := orders.getD targetNode 2147483647
    let ed ← getEdge firstEdge
    let modelOrder := ed.internal.modelOrder.getD 2147483647
    if !ed.internal.reversed then
      if !orders.contains targetNode then
        keys := keys.push targetNode
      orders := orders.insert targetNode (min prevOrder modelOrder)
  let result := keys.map fun k => (k, orders.getD k 0)
  setTargetNodeModelOrder node result
  return result

/-- Sorts the ports of the nodes of one layer (nodes with `FIXED_ORDER`/`FIXED_POS` port constraints
are skipped), then caches the port sides. -/
def sortPortsOfLayer (nodes : Array LNodeId) (comparator : ModelOrderPortComparator) :
    LayeredM ModelOrderPortComparator := do
  let mut comparator := comparator
  for node in nodes do
    let constraints := (← getNode node).props.getD LayeredOptions.PORT_CONSTRAINTS .undefined
    if constraints == .fixedOrder || constraints == .fixedPos then continue
    let longEdgeTargets ← longEdgeTargetNodePreprocessing node
    comparator := comparator.resetForNodeTargetModelOrder (some longEdgeTargets)
    let (ports, c) ← insertionSortPort (← getNode node).ports comparator
    comparator := c
    modifyNode node fun n => { n with ports := ports }
    cachePortSides node
  return comparator

/-- `process(graph, progressMonitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let layers := gr.layers
  if layers.isEmpty then return
  let orderingStrategy := gr.props.getD LayeredOptions.CONSIDER_MODEL_ORDER_STRATEGY .none
  let longEdgeStrategy := gr.props.getD LayeredOptions.CONSIDER_MODEL_ORDER_LONG_EDGE_STRATEGY .equal
  let groupStrategy := gr.props.getD LayeredOptions.GROUP_MODEL_ORDER_CM_GROUP_ORDER_STRATEGY .onlyWithinGroup
  let portModelOrder := gr.props.getD LayeredOptions.CONSIDER_MODEL_ORDER_PORT_MODEL_ORDER false
  let context ← ModelOrderGraphContext.ofGraph graph
  let mut prePortsNodeComparator :=
    ModelOrderNodeComparator.new context #[] orderingStrategy longEdgeStrategy groupStrategy true
  let mut postPortsNodeComparator :=
    ModelOrderNodeComparator.new context #[] orderingStrategy longEdgeStrategy groupStrategy false
  let mut portComparator := ModelOrderPortComparator.new context #[] orderingStrategy none portModelOrder
  let mut previousLayerNodes : Array LNodeId := #[]
  let mut layerIndex := 0
  for layer in layers do
    modifyLayer layer fun l => { l with id := (layerIndex : Int) }
    let mut nodes := (← getLayer layer).nodes
    -- Java semantics: for the first layer, previousLayer is the layer itself
    if layerIndex == 0 then
      previousLayerNodes := nodes
    prePortsNodeComparator := prePortsNodeComparator.resetForPreviousLayerSlice previousLayerNodes
    let (sorted, c) ← insertionSort nodes prePortsNodeComparator
    nodes := sorted
    prePortsNodeComparator := c
    modifyLayer layer fun l => { l with nodes := nodes }
    portComparator := portComparator.resetForPreviousLayerSlice previousLayerNodes
    portComparator ← sortPortsOfLayer nodes portComparator
    postPortsNodeComparator := postPortsNodeComparator.resetForPreviousLayerSlice previousLayerNodes
    let (sorted, c) ← insertionSort nodes postPortsNodeComparator
    nodes := sorted
    postPortsNodeComparator := c
    modifyLayer layer fun l => { l with nodes := nodes }
    previousLayerNodes := nodes
    layerIndex := layerIndex + 1

/-- The `SortByInputModelProcessor`. -/
def processor : LayeredProcessor :=
  { name := "SortByInputModelProcessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Sort By Input Model" 1.0
      run graph
      monitor.done }

end SortByInputModelProcessor

builtin_initialize registerSortByInputModelProcessor : Unit ←
  IntermediateProcessorStrategy.register .sortByInputOrderOfModel SortByInputModelProcessor.processor

end Elk.Alg.Layered.Intermediate
