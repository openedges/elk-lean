import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Alg.Layered.Graph.Tarjan
import Elk.Alg.Layered.P1Cycles.GroupModelOrderCalculator
/-!
# `org.eclipse.elk.alg.layered.p1cycles.SCCModelOrderCycleBreaker`

Port of the shared part of elk-rs `p1cycles/scc_model_order_cycle_breaker.rs` (the Java abstract
base class of `SCConnectivity` and `SCCNodeTypeCycleBreaker`; there is no strategy constant for it).

`processSccModelOrderCycleBreaking` repeats until Tarjan finds no strongly connected component with
more than one node: compute the components over the layerless nodes, let the subclass's
`findNodes` pick the edges to reverse, reverse them *without* port adaptation, increment the
`LAYERING_LAYER_ID` of each reversed edge's (new) source node and mark the graph `CYCLIC`.

Rust runs Tarjan on a fresh `LGraph` whose layerless nodes are the graph's layerless nodes; the
Lean `Tarjan` reads the layerless nodes of the graph id it is given, so the layered graph itself
is passed (same node list, same order).
-/
namespace Elk.Alg.Layered.P1Cycles

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace SCCModelOrderCycleBreaker

/-- `INTERMEDIATE_PROCESSING_CONFIGURATION`: `REVERSED_EDGE_RESTORER` after P5
(Rust `layout_processor_configuration`). -/
def layoutProcessorConfiguration : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration).addAfter .p5EdgeRouting .reversedEdgeRestorer

/-- `findNodes(stronglyConnectedComponents, offset, bigOffset)` of a subclass: the edges to reverse
(Rust appends to the empty `rev_edges`). -/
abbrev FindNodes := LGraphId → Array (Array LNodeId) → Int → Int → LayeredM (Array LEdgeId)

/-- Rust `constraint_model_order`: the constraint group model order when the graph's
`GROUP_MODEL_ORDER_CB_GROUP_ORDER_STRATEGY` is `ENFORCED`, else the constraint model order. -/
def constraintModelOrder (graph : LGraphId) (node : LNodeId) (calculator : GroupModelOrderCalculator)
    (offset bigOffset : Int) : LayeredM (Int × GroupModelOrderCalculator) := do
  let enforce := (← getGraph graph).props.getD LayeredOptions.GROUP_MODEL_ORDER_CB_GROUP_ORDER_STRATEGY
    .onlyWithinGroup == .enforced
  let nd ← getNode node
  if enforce then return calculator.computeConstraintGroupModelOrder nd bigOffset offset
  else return calculator.computeConstraintModelOrder nd offset

/-- Rust `node_group_model_order_id`: `GROUP_MODEL_ORDER_CYCLE_BREAKING_ID` (default `0`). -/
def nodeGroupModelOrderId (node : LNodeId) : LayeredM Int :=
  getNodePropD node LayeredOptions.GROUP_MODEL_ORDER_CYCLE_BREAKING_ID 0

/-- Rust `contains_node`. -/
@[inline] def containsNode (component : Array LNodeId) (node : LNodeId) : Bool := component.contains node

/-- The minimum and maximum constraint model order nodes of a component (first one wins ties;
one calculator for the whole component). Shared by the `find_nodes` of `SCConnectivity` and
`SCCNodeTypeCycleBreaker`, which duplicate this loop in Rust. -/
def minMaxNodes (graph : LGraphId) (component : Array LNodeId) (offset bigOffset : Int) :
    LayeredM (Option (LNodeId × LNodeId)) := do
  let mut minNode : Option LNodeId := none
  let mut maxNode : Option LNodeId := none
  let mut minModelOrder : Int := 2147483647
  let mut maxModelOrder : Int := -2147483648
  let mut calculator := GroupModelOrderCalculator.new
  for node in component do
    let (current, c) ← constraintModelOrder graph node calculator offset bigOffset
    calculator := c
    if minNode.isNone || current < minModelOrder then
      minNode := some node
      minModelOrder := current
    if maxNode.isNone || current > maxModelOrder then
      maxNode := some node
      maxModelOrder := current
  match minNode, maxNode with
  | some mn, some mx => return some (mn, mx)
  | _, _ => return none

/-- The incoming edges (node-level) of `node` whose source node is in `component`. -/
def incomingFromComponent (component : Array LNodeId) (node : LNodeId) : LayeredM (Array LEdgeId) := do
  let mut result := #[]
  for edge in (← withArena (·.nodeIncomingEdges node)) do
    let some sourcePort := (← getEdge edge).source | continue
    let some sourceNode := (← getPort sourcePort).owner | continue
    if containsNode component sourceNode then result := result.push edge
  return result

/-- The outgoing edges (node-level) of `node` whose target node is in `component`. -/
def outgoingToComponent (component : Array LNodeId) (node : LNodeId) : LayeredM (Array LEdgeId) := do
  let mut result := #[]
  for edge in (← withArena (·.nodeOutgoingEdges node)) do
    let some targetPort := (← getEdge edge).target | continue
    let some targetNode := (← getPort targetPort).owner | continue
    if containsNode component targetNode then result := result.push edge
  return result

/-- Rust `increment_source_layer_id`: `LAYERING_LAYER_ID` of the edge's source node plus one
(`-1` when unset). -/
def incrementSourceLayerId (edge : LEdgeId) : LayeredM Unit := do
  let some sourcePort := (← getEdge edge).source | return
  let some sourceNode := (← getPort sourcePort).owner | return
  let current ← getNodePropD sourceNode LayeredOptions.LAYERING_LAYER_ID (-1)
  setNodeProp sourceNode LayeredOptions.LAYERING_LAYER_ID (current + 1)

/-- Rust `process_scc_model_order_cycle_breaking` (Java `SCCModelOrderCycleBreaker.process`). -/
def processSccModelOrderCycleBreaking (graph : LGraphId) (findNodes : FindNodes) : LayeredM Unit := do
  let gr ← getGraph graph
  let offset : Int := max (gr.layerlessNodes.size : Int) gr.internal.maxModelOrderNodes
  let bigOffset := offset * gr.internal.cbNumModelOrderGroups
  let mut revEdges : Array LEdgeId := #[]
  while true do
    let (_, tarjan) ← Tarjan.run (do Tarjan.resetTarjan graph; Tarjan.tarjan graph) (Tarjan.new revEdges)
    let components := tarjan.stronglyConnectedComponents
    if components.isEmpty then break
    revEdges := revEdges ++ (← findNodes graph components offset bigOffset)
    for edge in revEdges do
      LGraphUtil.reverseEdge edge graph false
      incrementSourceLayerId edge
      modifyGraph graph fun g => { g with internal := { g.internal with cyclic := true } }
    revEdges := #[]

end SCCModelOrderCycleBreaker

end Elk.Alg.Layered.P1Cycles
