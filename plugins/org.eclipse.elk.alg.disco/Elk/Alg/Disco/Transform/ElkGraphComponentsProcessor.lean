import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Graph.Monad
import Elk.Core.Exceptions
/-!
# `org.eclipse.elk.alg.disco.transform.ElkGraphComponentsProcessor`

Splits the children of an `ElkNode` into connected components by a depth-first search (elk-rs
`transform/elk_graph_components_processor.rs`).

Two nodes are adjacent if an edge connects them on the same hierarchy level, or if both are
connected to the inside of the same port of the parent (edges that lead from a child to a port of
the parent or back). The search follows the adjacency in insertion order: Rust keeps a `Vec` with
a visited-set per node (`add_adjacent`), where Java uses a `HashSet`; the DFS order, and with it
the order of the nodes in a component, is the Rust one.

This file also holds the helpers for 'simple' edges (`ElkGraphUtil.getSourceNode` and friends:
exactly one source and one target) which the Rust port duplicates in the transformer and the
processor; `ElkGraphTransformer` uses the public ones.
-/
namespace Elk.Alg.Disco.Transform

open Elk.Graph Elk.Core

namespace ElkGraphComponentsProcessor

/-- `edge_endpoints`: source and target of a simple edge; throws
`java.lang.IllegalArgumentException: Passed edge is not 'simple'.` otherwise. -/
def edgeEndpoints (e : EdgeId) : ElkM (ConnectableId × ConnectableId) := do
  let edge ← ElkM.getEdge e
  if edge.sources.size != 1 || edge.targets.size != 1 then
    throwIllegalArgument "Passed edge is not 'simple'."
  return (edge.sources[0]!, edge.targets[0]!)

/-- `ElkGraphUtil.connectableShapeToNode(shape).expect(...)`. -/
private def shapeNode (shape : ConnectableId) : ElkM NodeId := do
  match ElkGraphUtil.connectableShapeToNode (← get) shape with
  | some n => return n
  | none => throwIllegalArgument "Passed edge is not 'simple'."

/-- `get_source_node(edge)`. -/
def sourceNode (e : EdgeId) : ElkM NodeId := do
  shapeNode (← edgeEndpoints e).1

/-- `get_target_node(edge)`. -/
def targetNode (e : EdgeId) : ElkM NodeId := do
  shapeNode (← edgeEndpoints e).2

/-- `get_source_port(edge)`. -/
def sourcePort (e : EdgeId) : ElkM (Option PortId) := do
  return ElkGraphUtil.connectableShapeToPort (← edgeEndpoints e).1

/-- `get_target_port(edge)`. -/
def targetPort (e : EdgeId) : ElkM (Option PortId) := do
  return ElkGraphUtil.connectableShapeToPort (← edgeEndpoints e).2

/-- `same_hierarchy_level(edge)`: source and target node have the same parent (or both none). -/
def sameHierarchyLevel (e : EdgeId) : ElkM Bool := do
  let s ← sourceNode e
  let t ← targetNode e
  return (← ElkM.getNode s).parent == (← ElkM.getNode t).parent

/-- `add_adjacent`: appends the node unless it is already in the set. -/
private def addAdjacent (nodes : Array NodeId) (ids : Std.HashSet NodeId) (n : NodeId) :
    Array NodeId × Std.HashSet NodeId :=
  if ids.contains n then (nodes, ids) else (nodes.push n, ids.insert n)

/-- `get_inner_neighbors_of_port(port)`: the nodes that are connected to the port from inside its
parent (incoming edges first, then outgoing ones; duplicates removed). -/
private def innerNeighborsOfPort (port : PortId) : ElkM (Array NodeId) := do
  let p ← ElkM.getPort port
  let some portParent := p.parent | return #[]
  let edges := p.incomingEdges ++ p.outgoingEdges
  let mut result : Array NodeId := #[]
  let mut seen : Std.HashSet NodeId := {}
  for edge in edges do
    let source ← sourceNode edge
    let target ← targetNode edge
    let sourceParent := (← ElkM.getNode source).parent
    let targetParent := (← ElkM.getNode target).parent
    let inwards := sourceParent == some portParent || targetParent == some portParent
    if !inwards then continue
    let neighbor := if source == portParent then target else source
    (result, seen) := addAdjacent result seen neighbor
  return result

/-- `adjacent_and_inside_parent.entry(port).or_insert_with(get_inner_neighbors_of_port)`. -/
private def cachedInnerNeighbors (cache : Std.HashMap PortId (Array NodeId)) (port : PortId) :
    ElkM (Array NodeId × Std.HashMap PortId (Array NodeId)) := do
  match cache.get? port with
  | some ns => return (ns, cache)
  | none =>
    let ns ← innerNeighborsOfPort port
    return (ns, cache.insert port ns)

/-- `compute_incidences(nodes)`: for every node the adjacent nodes in discovery order: sources of
incoming same-level edges, inner neighbors of parent ports that incoming edges come from, targets
of outgoing same-level edges, inner neighbors of parent ports that outgoing edges lead to. -/
private def computeIncidences (nodes : Array NodeId) : ElkM (Std.HashMap NodeId (Array NodeId)) := do
  let mut incidenceMap : Std.HashMap NodeId (Array NodeId) := {}
  let mut adjacentAndInsideParent : Std.HashMap PortId (Array NodeId) := {}
  for node in nodes do
    let mut adjacentIds : Std.HashSet NodeId := {}
    let mut adjacentNodes : Array NodeId := #[]
    let incoming ← (fun g => ElkGraphUtil.allIncomingEdges g node) <$> get
    for edge in incoming do
      if ← sameHierarchyLevel edge then
        (adjacentNodes, adjacentIds) := addAdjacent adjacentNodes adjacentIds (← sourceNode edge)
    for edge in incoming do
      if ← sameHierarchyLevel edge then continue
      let sourceN ← sourceNode edge
      let targetN ← targetNode edge
      if (← ElkM.getNode targetN).parent == some sourceN then
        if let some port ← sourcePort edge then
          let (nodesAtPort, cache) ← cachedInnerNeighbors adjacentAndInsideParent port
          adjacentAndInsideParent := cache
          for adj in nodesAtPort do
            (adjacentNodes, adjacentIds) := addAdjacent adjacentNodes adjacentIds adj
    let outgoing ← (fun g => ElkGraphUtil.allOutgoingEdges g node) <$> get
    for edge in outgoing do
      if ← sameHierarchyLevel edge then
        (adjacentNodes, adjacentIds) := addAdjacent adjacentNodes adjacentIds (← targetNode edge)
    for edge in outgoing do
      if ← sameHierarchyLevel edge then continue
      let sourceN ← sourceNode edge
      let targetN ← targetNode edge
      if (← ElkM.getNode sourceN).parent == some targetN then
        if let some port ← targetPort edge then
          let (nodesAtPort, cache) ← cachedInnerNeighbors adjacentAndInsideParent port
          adjacentAndInsideParent := cache
          for adj in nodesAtPort do
            (adjacentNodes, adjacentIds) := addAdjacent adjacentNodes adjacentIds adj
    incidenceMap := incidenceMap.insert node adjacentNodes
  return incidenceMap

/-- `dfs(start, ...)`: naive recursive depth-first search; marks the node visited, appends it to
the component and descends into the unvisited adjacent nodes in order. -/
private partial def dfs (start : NodeId) (incidenceMap : Std.HashMap NodeId (Array NodeId))
    (visited : Std.HashSet NodeId) (component : Array NodeId) :
    Std.HashSet NodeId × Array NodeId := Id.run do
  let mut visited := visited.insert start
  let mut component := component.push start
  for node in incidenceMap.getD start #[] do
    if !visited.contains node then
      (visited, component) := dfs node incidenceMap visited component
  return (visited, component)

/-- `ElkGraphComponentsProcessor.split(graph)`: the connected components of the children of the
graph, each in DFS order, in the order of their first node. -/
def split (graph : NodeId) : ElkM (Array (Array NodeId)) := do
  let children := (← ElkM.getNode graph).children
  let incidenceMap ← computeIncidences children
  let mut visited : Std.HashSet NodeId := {}
  let mut components : Array (Array NodeId) := #[]
  for node in children do
    if !visited.contains node then
      let (v, component) := dfs node incidenceMap visited #[]
      visited := v
      components := components.push component
  return components

end ElkGraphComponentsProcessor

end Elk.Alg.Disco.Transform
