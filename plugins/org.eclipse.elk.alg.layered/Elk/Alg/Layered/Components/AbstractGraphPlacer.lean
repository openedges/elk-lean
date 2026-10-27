import Std.Data.HashSet
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.components.AbstractGraphPlacer`

The shared helpers of the graph placers (Java `AbstractGraphPlacer.moveGraph(s)` /
`offsetGraph(s)`). elk-rs folds the placers into free functions of
`components/components_processor.rs`; these are its `move_graph(s)`, `offset_graph(s)`,
`collect_component_nodes` and `shift_node_and_outgoing_edges`.

Unlike Java (which only looks at `getLayerlessNodes()`), the Rust helpers move the layerless
nodes **and** the nodes still assigned to layers (`collect_component_nodes`: layerless nodes
first, then the layers' nodes, each node once in first-seen order).

The Java `LGraph.copyProperties(source)` of the placers is `copyProperties` here: the public
option map is merged (`PropertyMap.copyFrom`) and the typed internals are taken from the
source. Rust copies every key of the source map, so this is exact as long as the source holds
every internal key of the target, which is the case for components created by
`ComponentsProcessor.split` (they start from a clone of the target's properties).
-/
namespace Elk.Alg.Layered.Components

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace AbstractGraphPlacer

/-- Rust `collect_component_nodes(graph)`: layerless nodes, then the nodes of the layers, each
node once (first occurrence wins). -/
def collectComponentNodes (graph : LGraphId) : LayeredM (Array LNodeId) := do
  let gr ← getGraph graph
  let mut seen : Std.HashSet LNodeId := {}
  let mut nodes : Array LNodeId := #[]
  for n in gr.layerlessNodes do
    if !seen.contains n then
      seen := seen.insert n
      nodes := nodes.push n
  for l in gr.layers do
    for n in (← getLayer l).nodes do
      if !seen.contains n then
        seen := seen.insert n
        nodes := nodes.push n
  return nodes

/-- Rust `shift_node_and_outgoing_edges(node, offset_x, offset_y)`: moves the node, the bend
points and junction points of its outgoing edges and their labels. -/
def shiftNodeAndOutgoingEdges (node : LNodeId) (offsetX offsetY : Float) : LayeredM Unit := do
  modifyNode node fun nd => { nd with position := ⟨nd.position.x + offsetX, nd.position.y + offsetY⟩ }
  for p in (← getNode node).ports do
    for e in (← getPort p).outgoingEdges do
      modifyEdge e fun ed =>
        let ed := { ed with bendPoints := ed.bendPoints.offsetValues offsetX offsetY }
        -- `JUNCTION_POINTS` has a default (empty chain), so Rust always stores the result
        match ed.props.get LayeredOptions.JUNCTION_POINTS with
        | some jps => { ed with props := ed.props.set LayeredOptions.JUNCTION_POINTS (jps.offsetValues offsetX offsetY) }
        | none => ed
      for l in (← getEdge e).labels do
        modifyLabel l fun lb => { lb with position := ⟨lb.position.x + offsetX, lb.position.y + offsetY⟩ }

/-- `offsetGraph(graph, offsetx, offsety)` (Rust `offset_graph`): offsets all nodes of the
graph without moving them to another graph and without applying the graph's offset. -/
def offsetGraph (graph : LGraphId) (offsetX offsetY : Float) : LayeredM Unit := do
  for n in ← collectComponentNodes graph do
    shiftNodeAndOutgoingEdges n offsetX offsetY

/-- `offsetGraphs(graphs, offsetx, offsety)`. -/
def offsetGraphs (graphs : Array LGraphId) (offsetX offsetY : Float) : LayeredM Unit := do
  for g in graphs do offsetGraph g offsetX offsetY

/-- `moveGraph(destGraph, sourceGraph, offsetx, offsety)` (Rust `move_graph`): applies the
source graph's offset plus the given offset, removes the nodes from their layers and appends
them to the destination's layerless nodes. -/
def moveGraph (destination source : LGraphId) (offsetX offsetY : Float) : LayeredM Unit := do
  let src ← getGraph source
  let graphOffsetX := src.offset.x + offsetX
  let graphOffsetY := src.offset.y + offsetY
  for n in ← collectComponentNodes source do
    shiftNodeAndOutgoingEdges n graphOffsetX graphOffsetY
    setNodeLayer n none
    modifyGraph destination fun g => { g with layerlessNodes := g.layerlessNodes.push n }
    modifyNode n fun nd => { nd with graph := some destination }

/-- `moveGraphs(destGraph, sourceGraphs, offsetx, offsety)`. -/
def moveGraphs (destination : LGraphId) (sources : Array LGraphId) (offsetX offsetY : Float) : LayeredM Unit := do
  for s in sources do moveGraph destination s offsetX offsetY

/-- `LGraph.copyProperties(source)` as used by the placers (see the module doc). -/
def copyProperties (target source : LGraphId) : LayeredM Unit := do
  let src ← getGraph source
  modifyGraph target fun g => { g with props := g.props.copyFrom src.props, internal := src.internal }

/-- `target.getLayerlessNodes().clear()`. -/
def clearLayerlessNodes (target : LGraphId) : LayeredM Unit :=
  modifyGraph target fun g => { g with layerlessNodes := #[] }

/-- The single-component path of Rust `combine` / `combine_simple_row`: moves the nodes of
`source` into `target` and copies the properties, padding and size. -/
def adoptSingleComponent (target source : LGraphId) : LayeredM Unit := do
  clearLayerlessNodes target
  moveGraph target source 0.0 0.0
  copyProperties target source
  let src ← getGraph source
  modifyGraph target fun g => { g with padding := src.padding, size := ⟨src.size.x, src.size.y⟩ }

/-- Rust `max_of(values)`: `f64::max` fold starting at `0.0`. -/
def maxOf (values : Array Float) : Float :=
  values.foldl (fun acc v => Elk.Core.Util.fmax acc v) 0.0

end AbstractGraphPlacer

end Elk.Alg.Layered.Components
