import Std.Data.HashMap
import Elk.Alg.Layered.Components.SimpleRowGraphPlacer
import Elk.Alg.Layered.Components.ComponentGroupGraphPlacer
import Elk.Alg.Layered.Components.ComponentGroupModelOrderGraphPlacer
import Elk.Alg.Layered.Components.ModelOrderRowGraphPlacer
/-!
# `org.eclipse.elk.alg.layered.components.ComponentsProcessor`

Port of `components/components_processor.rs` (elk-rs) and `ComponentsProcessor.java`: splits a
graph into its connected components before layout and combines the laid out components
afterwards.

## `split`
Only the layerless nodes are considered. The Rust port builds an adjacency list first (per
node: for each port in port order the source nodes of the incoming edges, then the target
nodes of the outgoing edges; neighbours outside the layerless list are skipped) and runs a
pre-order DFS from every unvisited node in layerless order; the component lists the nodes in DFS
discovery order. The DFS here is iterative with an explicit stack of `(node, next neighbour)`
frames, which visits the nodes in exactly the order of the recursive Rust `dfs_flat`. External
port dummies contribute their `EXT_PORT_SIDE` to the component's `EXT_PORT_CONNECTIONS`.

Every component graph is created in the same arena with a copy of the graph's public options
and typed internals (Rust clones the whole property map), its padding, the collected
`EXT_PORT_CONNECTIONS` and without `NODE_SIZE_MINIMUM`. The nodes get the component as their
graph. With `CONSIDER_MODEL_ORDER_COMPONENTS` the components are stably sorted by their minimal
node model order.

Splitting is skipped (the graph itself is the only component) unless
`SEPARATE_CONNECTED_COMPONENTS` is not `false` and the graph has no external ports or its port
constraints are not order-fixed.

## `combine`
Dispatches like Rust `combine`: single component fast path, then (with external ports)
`ModelOrderRowGraphPlacer` / `ComponentGroupModelOrderGraphPlacer` / `ComponentGroupGraphPlacer`
by `CONSIDER_MODEL_ORDER_COMPONENTS`, else `SimpleRowGraphPlacer`.

The Java `node.id` visit marks are not used (Rust keeps a separate `visited` array).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.Layered.Components

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open LayeredM AbstractGraphPlacer

namespace ComponentsProcessor

/-- Rust `dfs_flat(idx, adjacency, ext_port_side, visited, component, ext_port_sides)`:
pre-order DFS from `start` (iterative, same visiting order as the recursive original). Returns
the discovered node indices, the external port sides met and the updated `visited` flags. -/
def dfsFlat (start : Nat) (adjacency : Array (Array Nat)) (extPortSide : Array (Option PortSide))
    (visited : Array Bool) : Array Nat × EnumSet PortSide × Array Bool := Id.run do
  let mut visited := visited
  let mut component : Array Nat := #[]
  let mut sides : EnumSet PortSide := EnumSet.noneOf
  if visited[start]?.getD true then return (component, sides, visited)
  visited := visited.set! start true
  component := component.push start
  if let some side := (extPortSide[start]?).bind id then sides := sides.insert side
  let mut stack : Array (Nat × Nat) := #[(start, 0)]
  while !stack.isEmpty do
    let (v, k) := stack.back!
    let neighbours := adjacency[v]?.getD #[]
    if h : k < neighbours.size then
      stack := stack.set! (stack.size - 1) (v, k + 1)
      let w := neighbours[k]
      if !(visited[w]?.getD true) then
        visited := visited.set! w true
        component := component.push w
        if let some side := (extPortSide[w]?).bind id then sides := sides.insert side
        stack := stack.push (w, 0)
    else
      stack := stack.pop
  return (component, sides, visited)

/-- `split(graph)`: the connected components of the graph's layerless nodes (see the module
doc); returns `#[graph]` when splitting is disabled or not possible. -/
def split (graph : LGraphId) : LayeredM (Array LGraphId) := do
  let gr ← getGraph graph
  let separate := gr.props.getD LayeredOptions.SEPARATE_CONNECTED_COMPONENTS true
  let extPorts := gr.internal.graphProperties.contains .externalPorts
  let extPortConstraints := gr.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  let considerModelOrder := gr.props.getD LayeredOptions.CONSIDER_MODEL_ORDER_COMPONENTS
    ComponentOrderingStrategy.none
  let nodes := gr.layerlessNodes
  let compatiblePortConstraints := !extPortConstraints.isOrderFixed
  if !(separate && (compatiblePortConstraints || !extPorts)) then
    return #[graph]
  -- Rust `ptr_to_idx` (a later duplicate overwrites an earlier one, like `collect()`)
  let mut ptrToIdx : Std.HashMap LNodeId Nat := {}
  for i in [0:nodes.size] do
    ptrToIdx := ptrToIdx.insert nodes[i]! i
  let mut adjacency : Array (Array Nat) := Array.replicate nodes.size #[]
  let mut extPortSide : Array (Option PortSide) := Array.replicate nodes.size none
  for i in [0:nodes.size] do
    let nd ← getNode nodes[i]!
    if nd.type == .externalPort then
      extPortSide := extPortSide.set! i (some nd.internal.extPortSide)
    let mut adj : Array Nat := #[]
    for port in nd.ports do
      let pt ← getPort port
      for edge in pt.incomingEdges do
        if let some src := (← getEdge edge).source then
          if let some srcNode := (← getPort src).owner then
            if let some j := ptrToIdx[srcNode]? then adj := adj.push j
      for edge in pt.outgoingEdges do
        if let some tgt := (← getEdge edge).target then
          if let some tgtNode := (← getPort tgt).owner then
            if let some j := ptrToIdx[tgtNode]? then adj := adj.push j
    adjacency := adjacency.set! i adj
  let mut result : Array LGraphId := #[]
  let randomHolder ← LayeredM.randomHolder graph
  let mut visited : Array Bool := Array.replicate nodes.size false
  for start in [0:nodes.size] do
    if visited[start]! then continue
    let (componentIndices, extPortSides, visited') := dfsFlat start adjacency extPortSide visited
    visited := visited'
    if componentIndices.isEmpty then continue
    -- `copy_properties` clones `RANDOM`, whose state elk-rs shares between clones: the
    -- component draws from the generator of the graph it was split from
    let componentGraph ← createGraph {
      props := gr.props.remove LayeredOptions.NODE_SIZE_MINIMUM,
      internal := { gr.internal with extPortConnections := extPortSides, random := none,
                                     randomOwner := some randomHolder },
      padding := gr.padding }
    for idx in componentIndices do
      let n := nodes[idx]!
      modifyGraph componentGraph fun g => { g with layerlessNodes := g.layerlessNodes.push n }
      modifyNode n fun nd => { nd with graph := some componentGraph }
    result := result.push componentGraph
  if considerModelOrder != .none then
    let mut keyed : Array (Int × LGraphId) := #[]
    for c in result do
      keyed := keyed.push (← LGraphUtil.getMinimalModelOrder c, c)
    result := (stableSort keyed fun a b => compare a.1 b.1).map (·.2)
  return result

/-- `combine(components, target)`: places the laid out components and moves their nodes into
`target` (see the module doc). -/
def combine (components : Array LGraphId) (target : LGraphId) : LayeredM Unit := do
  let tg ← getGraph target
  let considerModelOrder := tg.props.getD LayeredOptions.CONSIDER_MODEL_ORDER_COMPONENTS
    ComponentOrderingStrategy.none
  let hasExternalPorts := tg.internal.graphProperties.contains .externalPorts
  -- Only SimpleRowGraphPlacer has a single-component fast path. External port groups still
  -- need placement, even when the split produced one graph.
  if components.size == 1 && (!hasExternalPorts || components[0]! == target) then
    let source := components[0]!
    if source == target then return
    adoptSingleComponent target source
    return
  if components.isEmpty then
    modifyGraph target fun g => { g with layerlessNodes := #[], size := ⟨fl0p0, fl0p0⟩ }
    return
  if hasExternalPorts then
    match considerModelOrder with
    | .modelOrder => ModelOrderRowGraphPlacer.combine components target
    | .groupModelOrder => ComponentGroupModelOrderGraphPlacer.combine components target
    | .none | .insidePortSideGroups => ComponentGroupGraphPlacer.combine components target
    return
  SimpleRowGraphPlacer.combine components target

end ComponentsProcessor

end Elk.Alg.Layered.Components
