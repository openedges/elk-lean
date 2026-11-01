import Std.Data.HashMap
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.HyperedgeDummyMerger`

Port of elk-rs `intermediate/hyperedge_dummy_merger.rs`. Merges adjacent `LONG_EDGE` dummy nodes
(in the order the crossing minimizer left them) that belong to the same hyperedge: without label
dummies they must be in the same hyperedge component (`identify_hyperedges`); with label dummies
they must share the long edge source (both before their label dummies) or target (both after).

Representation differences from Java, unobservable (agent COV re-audit):
* the hyperedge components are kept in a port → component map instead of being written to the
  ports' `id` fields (the port ids are left unchanged); the components are found with an explicit
  stack (same partition and component numbering as the Java recursion). No later processor reads a
  port id without assigning it first (`EndLabelSorter` and the self-loop routers number the ports
  themselves), so the stale ids Java leaves behind never matter;
* the merged node is removed with `set_layer(None)` (Java only removes it from the layer list and
  leaves its `layer` field): the merged node has no edges and is in no layer list, so nothing reaches
  it afterwards.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace HyperedgeDummyMerger

/-- Rust `MergeState` (Java `MergeState`). -/
structure MergeState where
  allowMerge : Bool
  sameSource : Bool
  sameTarget : Bool

/-- `is_long_edge_dummy(node)`. -/
def isLongEdgeDummy (node : LNodeId) : LayeredM Bool := do
  return (← getNode node).type == .longEdge

/-- `mark_hyperedge_component(start, component_id, component_ids)`: assigns `componentId` to every
port reachable from `start` through edges and through the ports of long edge dummies (explicit
stack; pushes connected ports, then sibling ports of a long edge dummy). -/
def markHyperedgeComponent (start : LPortId) (componentId : Int) (componentIds : Std.HashMap LPortId Int) :
    LayeredM (Std.HashMap LPortId Int) := do
  let mut ids := componentIds
  let mut stack : Array LPortId := #[start]
  while true do
    let some port := stack.back? | break
    stack := stack.pop
    if ids.contains port then continue
    ids := ids.insert port componentId
    let connectedPorts ← withArena (·.portConnectedPorts port)
    for connected in connectedPorts do
      if !ids.contains connected then stack := stack.push connected
    let (isLongEdge, nodePorts) ← match (← getPort port).owner with
      | some node =>
        let nd ← getNode node
        pure (nd.type == .longEdge, nd.ports)
      | none => pure (false, #[])
    if isLongEdge then
      for sibling in nodePorts do
        if sibling != port && !ids.contains sibling then stack := stack.push sibling
  return ids

/-- `identify_hyperedges(layered_graph)` (Java `identifyHyperedges`): numbers the hyperedge
components of the ports of all layered nodes (layer → node → port order). -/
def identifyHyperedges (graph : LGraphId) : LayeredM (Std.HashMap LPortId Int) := do
  let mut ports : Array LPortId := #[]
  for layer in (← getGraph graph).layers do
    for node in (← getLayer layer).nodes do
      ports := ports ++ (← getNode node).ports
  let mut componentIds : Std.HashMap LPortId Int := {}
  let mut nextId : Int := 0
  for port in ports do
    if componentIds.contains port then continue
    componentIds ← markHyperedgeComponent port nextId componentIds
    nextId := nextId + 1
  return componentIds

/-- `check_merge_allowed(curr_node, last_node, hyperedge_ids)` (Java `checkMergeAllowed`). -/
def checkMergeAllowed (currNode lastNode : LNodeId) (hyperedgeIds : Std.HashMap LPortId Int) : LayeredM MergeState := do
  let curr ← getNode currNode
  let last ← getNode lastNode
  let currHasLabelDummies := curr.internal.longEdgeHasLabelDummies
  let lastHasLabelDummies := last.internal.longEdgeHasLabelDummies
  let sameSource := match curr.internal.longEdgeSource, last.internal.longEdgeSource with
    | some c, some l => c == l
    | _, _ => false
  let sameTarget := match curr.internal.longEdgeTarget, last.internal.longEdgeTarget with
    | some c, some l => c == l
    | _, _ => false
  if !currHasLabelDummies && !lastHasLabelDummies then
    let allowMerge := match curr.ports[0]?, last.ports[0]? with
      | some currPort, some lastPort =>
        let currId := hyperedgeIds.get? currPort
        let lastId := hyperedgeIds.get? lastPort
        currId.isSome && currId == lastId
      | _, _ => false
    return { allowMerge, sameSource, sameTarget }
  let currBeforeLabelDummy := curr.internal.longEdgeBeforeLabelDummy
  let lastBeforeLabelDummy := last.internal.longEdgeBeforeLabelDummy
  let eligibleForSourceMerging := (!currHasLabelDummies || currBeforeLabelDummy)
    && (!lastHasLabelDummies || lastBeforeLabelDummy)
  let eligibleForTargetMerging := (!currHasLabelDummies || !currBeforeLabelDummy)
    && (!lastHasLabelDummies || !lastBeforeLabelDummy)
  return { allowMerge := (sameSource && eligibleForSourceMerging) || (sameTarget && eligibleForTargetMerging),
           sameSource, sameTarget }

/-- `merge_nodes(merge_source, merge_target, keep_source_port, keep_target_port)` (Java
`mergeNodes`): moves all edges of `mergeSource` to the first western/eastern port of `mergeTarget`
and clears the target's `LONG_EDGE_SOURCE`/`LONG_EDGE_TARGET` unless they are shared. -/
def mergeNodes (mergeSource mergeTarget : LNodeId) (keepSourcePort keepTargetPort : Bool) : LayeredM Unit := do
  let targetInput := (← withArena (·.nodePortsBySide mergeTarget .west))[0]?
  let targetOutput := (← withArena (·.nodePortsBySide mergeTarget .east))[0]?
  let (some targetInput, some targetOutput) := (targetInput, targetOutput) | return
  for port in (← getNode mergeSource).ports do
    while true do
      let some edge := (← getPort port).incomingEdges[0]? | break
      setEdgeTarget edge (some targetInput)
    while true do
      let some edge := (← getPort port).outgoingEdges[0]? | break
      setEdgeSource edge (some targetOutput)
  if !keepSourcePort then
    modifyNode mergeTarget fun n => { n with internal := { n.internal with longEdgeSource := none } }
  if !keepTargetPort then
    modifyNode mergeTarget fun n => { n with internal := { n.internal with longEdgeTarget := none } }

/-- `process(layered_graph, monitor)`: per layer compares each node with its predecessor; after a
merge the current node is removed and the same index is checked again. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Hyperedge merging" 1.0
  let hyperedgeIds ← identifyHyperedges graph
  for layer in (← getGraph graph).layers do
    let mut nodeIndex := 1
    while true do
      let nodes := (← getLayer layer).nodes
      if nodeIndex >= nodes.size then break
      let currNode := nodes[nodeIndex]!
      let lastNode := nodes[nodeIndex - 1]!
      if (← isLongEdgeDummy currNode) && (← isLongEdgeDummy lastNode) then
        let state ← checkMergeAllowed currNode lastNode hyperedgeIds
        if state.allowMerge then
          mergeNodes currNode lastNode state.sameSource state.sameTarget
          setNodeLayer currNode none
          -- re-check at this index because the current node was removed
          continue
      nodeIndex := nodeIndex + 1
  monitor.done

/-- The `HyperedgeDummyMerger` processor. -/
def processor : LayeredProcessor := { name := "HyperedgeDummyMerger", process := process }

end HyperedgeDummyMerger

builtin_initialize registerHyperedgeDummyMerger : Unit ←
  IntermediateProcessorStrategy.register .hyperedgeDummyMerger HyperedgeDummyMerger.processor

end Elk.Alg.Layered.Intermediate
