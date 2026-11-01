import Elk.Alg.Layered.P1Cycles.SCCModelOrderCycleBreaker
import Elk.Alg.Layered.Options.CycleBreakingStrategy
/-!
# `org.eclipse.elk.alg.layered.p1cycles.SCCNodeTypeCycleBreaker`

Port of elk-rs `p1cycles/scc_node_type_cycle_breaker.rs` (`SccNodeTypeCycleBreaker`). Like
`SCConnectivity`, but a minimum node whose `GROUP_MODEL_ORDER_CYCLE_BREAKING_ID` equals the graph's
`GROUP_MODEL_ORDER_CB_PREFERRED_SOURCE_ID` gets its incoming component edges reversed, and else a
maximum node whose id equals `GROUP_MODEL_ORDER_CB_PREFERRED_TARGET_ID` gets its outgoing edges
reversed; only then connectivity decides.

Java semantics (agent HMO; elk-rs differs):
- Java compares the boxed `Integer`s with `==` (`javaBoxedIdEq`): the preferred ids have no default,
  so an unset preference never matches (elk-rs `unwrap_or(0)` made every component with default
  options take the preferred-source branch), and equal set values are the same object only inside
  the `Integer` cache `[-128, 127]` (node and graph values come from separate `Integer.valueOf`
  calls of the JSON import);
- in the preferred-target branch the filter tests the edge's *source* node (always the maximum
  node itself), so all its outgoing edges are reversed (same as elk-rs).

The phase name is the Java class name `SCCNodeTypeCycleBreaker` (the elk-rs `type_name` is
`SccNodeTypeCycleBreaker`).
-/
namespace Elk.Alg.Layered.P1Cycles

open Elk.Graph Elk.Core Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM
  SCCModelOrderCycleBreaker

namespace SCCNodeTypeCycleBreaker

/-- The outgoing edges (node-level) of `node` whose *source* node is in `component` (Rust filter). -/
private def outgoingFromComponentSource (component : Array LNodeId) (node : LNodeId) : LayeredM (Array LEdgeId) := do
  let mut result := #[]
  for edge in (← withArena (·.nodeOutgoingEdges node)) do
    let some sourcePort := (← getEdge edge).source | continue
    let some sourceNode := (← getPort sourcePort).owner | continue
    if containsNode component sourceNode then result := result.push edge
  return result

/-- Java's `nodeId == graphPreferredId` on boxed `Integer`s: false for an unset preference (`null`),
and for equal values only inside the `Integer` cache `[-128, 127]` (distinct boxes otherwise). -/
def javaBoxedIdEq (nodeId : Int) (preferred : Option Int) : Bool :=
  match preferred with
  | some p => nodeId == p && -128 <= p && p <= 127
  | none => false

/-- `findNodes(...)` (Java `SCCNodeTypeCycleBreaker.findNodes`, Rust
`SccNodeTypeCycleBreaker::find_nodes` with Java's preferred id comparison). -/
def findNodes : FindNodes := fun graph components offset bigOffset => do
  let gr ← getGraph graph
  let preferredSource := gr.props.get LayeredOptions.GROUP_MODEL_ORDER_CB_PREFERRED_SOURCE_ID
  let preferredTarget := gr.props.get LayeredOptions.GROUP_MODEL_ORDER_CB_PREFERRED_TARGET_ID
  let mut revEdges : Array LEdgeId := #[]
  for component in components do
    if component.size <= 1 then continue
    let some (minNode, maxNode) ← minMaxNodes graph component offset bigOffset | continue
    if javaBoxedIdEq (← nodeGroupModelOrderId minNode) preferredSource then
      revEdges := revEdges ++ (← incomingFromComponent component minNode)
      continue
    if javaBoxedIdEq (← nodeGroupModelOrderId maxNode) preferredTarget then
      revEdges := revEdges ++ (← outgoingFromComponentSource component maxNode)
      continue
    let minInDegree := (← withArena (·.nodeIncomingEdges minNode)).size
    let maxOutDegree := (← withArena (·.nodeOutgoingEdges maxNode)).size
    if minInDegree > maxOutDegree then
      revEdges := revEdges ++ (← incomingFromComponent component minNode)
    else
      revEdges := revEdges ++ (← outgoingToComponent component maxNode)
  return revEdges

/-- The `SCCNodeTypeCycleBreaker` phase (`CycleBreakingStrategy.SCC_NODE_TYPE`). -/
def phase : LayeredPhase :=
  { name := "SCCNodeTypeCycleBreaker"
    process := fun graph monitor => do
      let _ ← monitor.begin "Model order cycle breaking" 1.0
      processSccModelOrderCycleBreaking graph findNodes
      monitor.done
    getLayoutProcessorConfiguration := fun _ => pure (some layoutProcessorConfiguration) }

end SCCNodeTypeCycleBreaker

builtin_initialize registerSCCNodeTypeCycleBreaker : Unit ←
  LayeredPhases.registerPhase .p1CycleBreaking (ElkEnum.ordinal CycleBreakingStrategy.sccNodeType)
    (pure SCCNodeTypeCycleBreaker.phase)

end Elk.Alg.Layered.P1Cycles
