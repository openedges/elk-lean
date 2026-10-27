import Std.Data.HashMap
import Elk.Graph
import Elk.Core.Math.KVector
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
import Elk.Alg.Force.Graph.FGraph
import Elk.Alg.Force.Options.ForceOptions
/-!
# `org.eclipse.elk.alg.force.ComponentsProcessor`

Port of `components_processor.rs` (elk-rs): splits a force graph into its connected components and
packs the laid out components again.

`split` (when `SEPARATE_CONNECTED_COMPONENTS`, default true) runs a depth first search from every
unvisited node (in node list order), with the edge-skipping rule of Rust: an edge is skipped when the
node it was reached from (`last`) is its source or target. Rust quirks reproduced on purpose:
* components copy their nodes in DFS order, so with a single component the arena `nodeId`s (which keep
  the original node index) are a permutation of the node order; only with several components the ids
  are renumbered by the node order of each component;
* an edge can be pushed to the edge list of a component twice (e.g. the closing edge of a cycle is
  visited from both of its end nodes) and is then copied twice.

`recombine` assigns every component the sum of its node priorities (graph option `PRIORITY`) and its
bounding box, sorts the components by priority (descending) and bounding box area (ascending, stable),
and places them row by row left to right in a square-ish layout (`ASPECT_RATIO`, default 1.0, spacing
`SPACING_NODE_NODE`).
-/
namespace Elk.Alg.Force

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.Force.Graph Elk.Alg.Force.Options

namespace ComponentsProcessor

/-- State of the depth first search: the component's nodes and edges and the visited flags. -/
private structure DfsState where
  compNodes : Array FNodeId := #[]
  compEdges : Array FEdgeId := #[]
  visited : Array Bool := #[]
  deriving Inhabited

/-- `build_incidence_lists`: for every node id the incident edges (edge order; an edge appears under
its source and under its target). -/
private def buildIncidenceLists (g : FGraph) : Array (Array FEdgeId) := Id.run do
  let n := g.nodes.size
  let mut incidence : Array (Array FEdgeId) := Array.replicate n #[]
  for eid in g.edges do
    let sourceId := (g.arena.edgeSource[eid.idx]!).map fun nid => g.arena.nodeId[nid.idx]!
    let targetId := (g.arena.edgeTarget[eid.idx]!).map fun nid => g.arena.nodeId[nid.idx]!
    if let some sid := sourceId then
      if sid < n then incidence := incidence.modify sid (·.push eid)
    if let some tid := targetId then
      if tid < n then incidence := incidence.modify tid (·.push eid)
  return incidence

/-- `dfs`: collects the nodes and edges of the component of `nid`. -/
private partial def dfs (g : FGraph) (incidence : Array (Array FEdgeId)) (nid : FNodeId)
    (last : Option FNodeId) (st : DfsState) : DfsState := Id.run do
  let nodeId := g.arena.nodeId[nid.idx]!
  if st.visited[nodeId]! then return st
  let mut st := { st with visited := st.visited.set! nodeId true, compNodes := st.compNodes.push nid }
  for eid in incidence[nodeId]! do
    let sourceNid := g.arena.edgeSource[eid.idx]!
    let targetNid := g.arena.edgeTarget[eid.idx]!
    if let some lastNid := last then
      if sourceNid == some lastNid || targetNid == some lastNid then continue
    if let some src := sourceNid then
      if src != nid then st := dfs g incidence src (some nid) st
    if let some tgt := targetNid then
      if tgt != nid then st := dfs g incidence tgt (some nid) st
    st := { st with compEdges := st.compEdges.push eid }
  return st

/-- Copies a node of `src` into `dest` (geometry, displacement, options, origin, id, label); the
position is moved by `offset` when given. -/
private def copyNode (src : FArena) (dest : FArena) (old : FNodeId) (offset : Option KVector) :
    FArena × FNodeId :=
  let (a, nid) := dest.addNode
  let pos := src.nodePosition[old.idx]!
  let pos := match offset with
    | some o => pos + o
    | none => pos
  let i := nid.idx
  ({ a with
      nodePosition := a.nodePosition.set! i pos
      nodeSize := a.nodeSize.set! i (src.nodeSize[old.idx]!)
      nodeDisplacement := a.nodeDisplacement.set! i (src.nodeDisplacement[old.idx]!)
      nodeProperties := a.nodeProperties.set! i (src.nodeProperties[old.idx]!)
      nodeOrigin := a.nodeOrigin.set! i (src.nodeOrigin[old.idx]!)
      nodeId := a.nodeId.set! i (src.nodeId[old.idx]!)
      nodeLabel := a.nodeLabel.set! i (src.nodeLabel[old.idx]!) }, nid)

/-- Copies the options, origin and (remapped) end nodes of an edge into a new edge of `dest`. -/
private def copyEdge (src : FArena) (dest : FArena) (old : FEdgeId) (remap : Std.HashMap Nat FNodeId) :
    FArena × FEdgeId :=
  let (a, eid) := dest.addEdge
  let i := eid.idx
  let a := { a with
    edgeProperties := a.edgeProperties.set! i (src.edgeProperties[old.idx]!)
    edgeOrigin := a.edgeOrigin.set! i (src.edgeOrigin[old.idx]!) }
  let a := match src.edgeSource[old.idx]! with
    | some s => match remap[s.idx]? with
      | some ns => { a with edgeSource := a.edgeSource.set! i (some ns) }
      | none => a
    | none => a
  let a := match src.edgeTarget[old.idx]! with
    | some t => match remap[t.idx]? with
      | some nt => { a with edgeTarget := a.edgeTarget.set! i (some nt) }
      | none => a
    | none => a
  (a, eid)

/-- Copies a bend point of `src` as a new bend point of the edge `eid` of `dest` (moved by `offset`
when given); returns the new id. -/
private def copyBendpoint (src : FArena) (dest : FArena) (old : FBendpointId) (eid : FEdgeId)
    (offset : Option KVector) : FArena × FBendpointId :=
  let (a, bid) := dest.addBendpoint eid
  let pos := src.bendPosition[old.idx]!
  let pos := match offset with
    | some o => pos + o
    | none => pos
  let i := bid.idx
  ({ a with
      bendPosition := a.bendPosition.set! i pos
      bendSize := a.bendSize.set! i (src.bendSize[old.idx]!)
      bendDisplacement := a.bendDisplacement.set! i (src.bendDisplacement[old.idx]!)
      bendProperties := a.bendProperties.set! i (src.bendProperties[old.idx]!) }, bid)

/-- Copies a label of `src` as a new label of the edge `eid` of `dest` (moved by `offset` when given);
returns the new id. -/
private def copyLabel (src : FArena) (dest : FArena) (old : FLabelId) (eid : FEdgeId)
    (offset : Option KVector) : FArena × FLabelId :=
  let (a, lid) := dest.addLabel eid
  let pos := src.labelPosition[old.idx]!
  let pos := match offset with
    | some o => pos + o
    | none => pos
  let i := lid.idx
  ({ a with
      labelPosition := a.labelPosition.set! i pos
      labelSize := a.labelSize.set! i (src.labelSize[old.idx]!)
      labelDisplacement := a.labelDisplacement.set! i (src.labelDisplacement[old.idx]!)
      labelProperties := a.labelProperties.set! i (src.labelProperties[old.idx]!)
      labelOrigin := a.labelOrigin.set! i (src.labelOrigin[old.idx]!)
      labelText := a.labelText.set! i (src.labelText[old.idx]!) }, lid)

/-- Builds the component graph of the given nodes and edges: copies of the nodes (in the given order),
of the edges with their bend points and labels. -/
private def buildComponent (graph : FGraph) (compNodes : Array FNodeId) (compEdges : Array FEdgeId) : FGraph :=
  Id.run do
    let mut component : FGraph := ({} : FGraph).copyProperties graph
    let mut remap : Std.HashMap Nat FNodeId := {}
    for old in compNodes do
      let (a, nid) := copyNode graph.arena component.arena old none
      component := { component with arena := a, nodes := component.nodes.push nid }
      remap := remap.insert old.idx nid
    for oldEid in compEdges do
      let (a, newEid) := copyEdge graph.arena component.arena oldEid remap
      component := { component with arena := a }
      for oldBid in graph.arena.edgeBendpoints[oldEid.idx]! do
        let (a, bid) := copyBendpoint graph.arena component.arena oldBid newEid none
        component := { component with arena := a, bendpoints := component.bendpoints.push bid }
      for oldLid in graph.arena.edgeLabels[oldEid.idx]! do
        let (a, lid) := copyLabel graph.arena component.arena oldLid newEid none
        component := { component with arena := a, labels := component.labels.push lid }
      component := { component with edges := component.edges.push newEid }
    return component

/-- `ComponentsProcessor::split(graph)`. -/
def split (graph : FGraph) : Array FGraph := Id.run do
  let separate := graph.props.getD ForceOptions.SEPARATE_CONNECTED_COMPONENTS true
  if !separate then return #[graph]
  let nodeCount := graph.nodes.size
  let incidence := buildIncidenceLists graph
  let mut st : DfsState := { visited := Array.replicate nodeCount false }
  let mut components : Array FGraph := #[]
  for i in [0:nodeCount] do
    let nid := graph.nodes[i]!
    let nodeId := graph.arena.nodeId[nid.idx]!
    if st.visited[nodeId]! then continue
    st := { st with compNodes := #[], compEdges := #[] }
    st := dfs graph incidence nid none st
    components := components.push (buildComponent graph st.compNodes st.compEdges)
  if components.size > 1 then
    components := components.map fun comp => Id.run do
      let mut nodeIds := comp.arena.nodeId
      for id in [0:comp.nodes.size] do
        nodeIds := nodeIds.set! (comp.nodes[id]!).idx id
      return { comp with arena := { comp.arena with nodeId := nodeIds } }
  return components

/-- `bounding_size`: size of the bounding box stored by `recombine`. -/
private def boundingSize (g : FGraph) : KVector :=
  (g.bbLowright.getD {}) - (g.bbUpleft.getD {})

/-- `move_graph(dest, source, offset_x, offset_y)`: appends a copy of the nodes, edges, bend points and
labels of `source` to `dest`, translated so that the upper left corner of the source's bounding box
ends up at `(offsetX, offsetY)`. -/
private def moveGraph (dest source : FGraph) (offsetX offsetY : Float) : FGraph := Id.run do
  let offset := KVector.mk offsetX offsetY - (source.bbUpleft.getD {})
  let mut dest := dest
  let mut remap : Std.HashMap Nat FNodeId := {}
  for old in source.nodes do
    let (a, nid) := copyNode source.arena dest.arena old (some offset)
    dest := { dest with arena := a, nodes := dest.nodes.push nid }
    remap := remap.insert old.idx nid
  for oldEid in source.edges do
    let (a, newEid) := copyEdge source.arena dest.arena oldEid remap
    dest := { dest with arena := a }
    for oldBid in source.arena.edgeBendpoints[oldEid.idx]! do
      let (a, bid) := copyBendpoint source.arena dest.arena oldBid newEid (some offset)
      dest := { dest with arena := a, bendpoints := dest.bendpoints.push bid }
    dest := { dest with edges := dest.edges.push newEid }
  for oldLid in source.labels do
    -- the new edge: the copy of the label's edge among the edges just appended to `dest`
    let newEid : Option FEdgeId := do
      let oldE ← source.arena.labelEdge[oldLid.idx]!
      let idx ← source.edges.findIdx? (· == oldE)
      dest.edges[dest.edges.size - source.edges.size + idx]?
    if let some newEid := newEid then
      let (a, lid) := copyLabel source.arena dest.arena oldLid newEid (some offset)
      dest := { dest with arena := a, labels := dest.labels.push lid }
  return dest

/-- Priority, bounding box and the sort order of `recombine`: higher priority first, then smaller
bounding box area first. -/
private def compareComponents (graph1 graph2 : FGraph) : Ordering :=
  let prio1 := graph1.props.getD ForceOptions.PRIORITY 0
  let prio2 := graph2.props.getD ForceOptions.PRIORITY 0
  let prio := compare prio2 prio1
  if prio != Ordering.eq then prio
  else
    let size1 := boundingSize graph1
    let size2 := boundingSize graph2
    Float.comparePartial (size1.x * size1.y) (size2.x * size2.y)

/-- Stores the summed node priority and the bounding box of a component. -/
private def annotateComponent (graph : FGraph) : FGraph := Id.run do
  let mut priority : Int := 0
  let mut minX := Float.maxValue
  let mut minY := Float.maxValue
  let mut maxX := Float.minValue
  let mut maxY := Float.minValue
  for nid in graph.nodes do
    priority := priority + (graph.arena.nodeProperties[nid.idx]!).getD ForceOptions.PRIORITY 1
    let pos := graph.arena.nodePosition[nid.idx]!
    let size := graph.arena.nodeSize[nid.idx]!
    minX := fmin minX (pos.x - size.x / 2.0)
    minY := fmin minY (pos.y - size.y / 2.0)
    maxX := fmax maxX (pos.x + size.x / 2.0)
    maxY := fmax maxY (pos.y + size.y / 2.0)
  return { graph with
    props := graph.props.set ForceOptions.PRIORITY priority
    bbUpleft := some ⟨minX, minY⟩
    bbLowright := some ⟨maxX, maxY⟩ }

/-- `ComponentsProcessor::recombine(components)`. -/
def recombine (components : Array FGraph) : FGraph := Id.run do
  if components.size == 1 then return components[0]!
  if components.isEmpty then return {}
  let comps := stableSort (components.map annotateComponent) compareComponents
  let mut result : FGraph := ({} : FGraph).copyProperties comps[0]!
  let mut maxRowWidth : Float := 0.0
  let mut totalArea : Float := 0.0
  for graph in comps do
    let size := boundingSize graph
    maxRowWidth := fmax maxRowWidth size.x
    totalArea := totalArea + size.x * size.y
  let aspectRatio := result.props.getD ForceOptions.ASPECT_RATIO 1.0
  maxRowWidth := fmax maxRowWidth (Float.sqrt totalArea * aspectRatio)
  let spacing := result.props.getD ForceOptions.SPACING_NODE_NODE 0.0
  let mut xpos : Float := 0.0
  let mut ypos : Float := 0.0
  let mut highestBox : Float := 0.0
  for graph in comps do
    let size := boundingSize graph
    if xpos + size.x > maxRowWidth then
      xpos := 0.0
      ypos := ypos + (highestBox + spacing)
      highestBox := 0.0
    result := moveGraph result graph xpos ypos
    highestBox := fmax highestBox size.y
    xpos := xpos + (size.x + spacing)
  return result

end ComponentsProcessor

end Elk.Alg.Force
