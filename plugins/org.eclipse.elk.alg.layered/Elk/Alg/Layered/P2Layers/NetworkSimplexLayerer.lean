import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Common.NetworkSimplex
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.layered.p2layers.NetworkSimplexLayerer` (elk-rs `network_simplex_layerer.rs`)

The network simplex layerer: every connected component of the layerless nodes is turned into an
`NGraph LNodeId` (one `NNode` per `LNode` in component order, one `NEdge` per non-self-loop
outgoing edge with weight `max(1, PRIORITY_SHORTNESS)` and delta `1`) and layered with
`NetworkSimplex` (balancing on, previous layering of the earlier components, iteration limit
`4 * THOROUGHNESS * floor(sqrt(|component|))`). The layers are read back from `NGraph.nodeList`
in its post-`execute` order, like the Rust loop over `graph.nodes`.

Orders reproduced from the Rust port:

* `connectedComponents` sets `LNode.id` to the index in the layerless node list, builds the
  adjacency per node as (per port) the source nodes of the incoming edges followed by the target
  nodes of the outgoing edges, and visits components with a depth-first search in that order
  (iterative, same visiting order as the recursive `dfs_flat`). A component larger than the
  current first one is inserted at the front, otherwise appended.
* `initializeGraph` iterates the component's nodes and their `getOutgoingEdges()` (per port).

Deviations: the `NEdge` origin (the `LEdge` in Rust/Java) is not stored because the
`NGraph LNodeId` payload type is the node id; nothing reads it. The sub monitor gets
`1 / |components|` work like Rust (Java: `1`).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl1p0 : Float := 1.0

namespace Elk.Alg.Layered.P2Layers

open Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Alg Elk.Alg.Common.NetworkSimplex
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace NetworkSimplexLayerer

/-- `BASELINE_PROCESSING_CONFIGURATION`. -/
def BASELINE_PROCESSING_CONFIGURATION : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p1CycleBreaking .edgeAndLayerConstraintEdgeReverser
    |>.addBefore .p2Layering .layerConstraintPreprocessor
    |>.addBefore .p3NodeOrdering .layerConstraintPostprocessor

/-- `ITER_LIMIT_FACTOR`: factor for the iteration limit of the network simplex. -/
def ITER_LIMIT_FACTOR : Int := 4

/-- The node owning the source port of `e`. -/
private def edgeSourceNode (a : LGraphArena) (e : LEdgeId) : Option LNodeId :=
  (a.edge e).source.bind fun p => (a.port p).owner

/-- The node owning the target port of `e`. -/
private def edgeTargetNode (a : LGraphArena) (e : LEdgeId) : Option LNodeId :=
  (a.edge e).target.bind fun p => (a.port p).owner

/-- Rust `dfs_flat`: the depth-first search over the prebuilt adjacency, run iteratively with an
explicit stack (same visiting order as the recursion). Returns the updated visit flags and the
nodes of the component in visiting order. -/
def dfsFlat (start : Nat) (adjacency : Array (Array Nat)) (nodes : Array LNodeId)
    (visited : Array Bool) : Array Bool × Array LNodeId := Id.run do
  let mut visited := visited
  let mut component : Array LNodeId := #[]
  if visited.getD start true then
    return (visited, component)
  visited := visited.set! start true
  component := component.push nodes[start]!
  -- frames: (node index, index of the next neighbour to visit)
  let mut stack : Array (Nat × Nat) := #[(start, 0)]
  while !stack.isEmpty do
    let (idx, k) := stack.back!
    let adj := adjacency[idx]!
    if h : k < adj.size then
      stack := stack.set! (stack.size - 1) (idx, k + 1)
      let neighbor := adj[k]
      if !visited.getD neighbor true then
        visited := visited.set! neighbor true
        component := component.push nodes[neighbor]!
        stack := stack.push (neighbor, 0)
    else
      stack := stack.pop
  return (visited, component)

/-- `connectedComponents(nodes)`: the connected components of `nodes`, the largest one first.
Sets `LNode.id` to the index of each node in `nodes`. -/
def connectedComponents (nodes : Array LNodeId) : LayeredM (Array (Array LNodeId)) := do
  let numNodes := nodes.size
  -- build ptr → idx map and set node ids in a single pass
  let mut ptrToIdx : Std.HashMap LNodeId Nat := {}
  for h : index in [0:nodes.size] do
    ptrToIdx := ptrToIdx.insert nodes[index] index
    modifyNode nodes[index] fun x => { x with id := index }
  -- adjacency: per port the sources of the incoming edges, then the targets of the outgoing edges
  let adjacency ← withArena fun a => nodes.map fun node => Id.run do
    let mut adj : Array Nat := #[]
    for p in (a.node node).ports do
      let pt := a.port p
      for e in pt.incomingEdges do
        if let some src := edgeSourceNode a e then
          if let some j := ptrToIdx.get? src then adj := adj.push j
      for e in pt.outgoingEdges do
        if let some tgt := edgeTargetNode a e then
          if let some j := ptrToIdx.get? tgt then adj := adj.push j
    return adj
  let mut visited := Array.replicate numNodes false
  let mut components : Array (Array LNodeId) := #[]
  for start in [0:numNodes] do
    if visited.getD start true then continue
    let (visited', component) := dfsFlat start adjacency nodes visited
    visited := visited'
    if components.isEmpty || components[0]!.size < component.size then
      components := #[component] ++ components
    else
      components := components.push component
  return components

/-- `initialize(nodes)` (Rust `initialize_graph`): the network simplex graph of one component.
Node origins are the `LNode` ids; self-loops and edges leaving the component are skipped. -/
def initializeGraph (nodes : Array LNodeId) : LayeredM (NGraph LNodeId) := do
  let mut graph : NGraph LNodeId := NGraph.new
  let mut nodeMap : Std.HashMap LNodeId NNodeId := {}
  for node in nodes do
    let (graph', nnode) := (NNode.of.origin node).create graph
    graph := graph'
    nodeMap := nodeMap.insert node nnode
  for node in nodes do
    let outgoing ← withArena (·.nodeOutgoingEdges node)
    for edge in outgoing do
      if ← withArena (·.edgeIsSelfLoop edge) then continue
      let some sourceNode ← withArena (edgeSourceNode · edge) | continue
      let some targetNode ← withArena (edgeTargetNode · edge) | continue
      let some sourceNNode := nodeMap.get? sourceNode | continue
      let some targetNNode := nodeMap.get? targetNode | continue
      let priority ← getEdgePropD edge LayeredOptions.PRIORITY_SHORTNESS 1
      let weight := Float.ofInt (max priority 1)
      let builder : NEdgeBuilder LNodeId := NEdge.of
      let (graph', _) ← (builder.weight weight |>.delta 1 |>.source sourceNNode |>.target targetNNode).create graph
      graph := graph'
  return graph

/-- `process(layeredGraph, monitor)`. -/
def process (layeredGraph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Network simplex layering" fl1p0
  let thoroughness := (← getGraphPropD layeredGraph LayeredOptions.THOROUGHNESS 7) * ITER_LIMIT_FACTOR
  let nodes := (← getGraph layeredGraph).layerlessNodes
  if nodes.isEmpty then
    monitor.done
    return
  let connectedComponents ← connectedComponents nodes
  let mut previousLayeringNodeCounts : Option (Array Int) := none
  for h : idx in [0:connectedComponents.size] do
    let component := connectedComponents[idx]
    -- Java parity: (int) Math.sqrt(connComp.size()) -> floor(sqrt(n)) for n >= 1
    let iterLimit := thoroughness * Float.toIntTrunc (Float.sqrt component.size.toFloat)
    let graph ← initializeGraph component
    let simplex := NetworkSimplex.forGraph graph
      |>.withIterationLimit iterLimit
      |>.withPreviousLayering previousLayeringNodeCounts
      |>.withBalancing true
    let subMonitor ← monitor.subTask (fl1p0 / connectedComponents.size.toFloat)
    let graph ← simplex.execute subMonitor
    for nnode in graph.nodeList do
      let nd := graph.node nnode
      let some lNode := nd.origin | continue
      -- the network simplex normalizes the layers to start at 0
      let layer := nd.layer.toNat
      while (← getGraph layeredGraph).layers.size <= layer do
        let graphRef := (← nodeGraph lNode).getD layeredGraph
        let newLayer ← createLayer graphRef
        modifyGraph layeredGraph fun g => { g with layers := g.layers.push newLayer }
      if let some layerRef := (← getGraph layeredGraph).layers[layer]? then
        setNodeLayer lNode (some layerRef)
    if connectedComponents.size > 1 then
      let layers := (← getGraph layeredGraph).layers
      let mut counts : Array Int := Array.mkEmpty layers.size
      for l in layers do
        counts := counts.push (← getLayer l).nodes.size
      previousLayeringNodeCounts := some counts
    if idx + 1 == connectedComponents.size then
      previousLayeringNodeCounts := none
  modifyGraph layeredGraph fun g => { g with layerlessNodes := #[] }
  monitor.done

/-- The `NetworkSimplexLayerer` phase. -/
def phase : LayeredPhase :=
  { name := "NetworkSimplexLayerer"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure (some BASELINE_PROCESSING_CONFIGURATION) }

end NetworkSimplexLayerer

end Elk.Alg.Layered.P2Layers
