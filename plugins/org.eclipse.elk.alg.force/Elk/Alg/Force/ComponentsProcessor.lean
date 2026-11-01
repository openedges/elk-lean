import Std.Data.HashMap
import Elk.Graph
import Elk.Core.Math.KVector
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
import Elk.Alg.Force.Graph.FGraph
import Elk.Alg.Force.Options.ForceOptions
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
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
  visited from both of its end nodes). Java then lists the same `FEdge` twice and its `FLabel`s twice
  (elk-rs made two independent copies): the component keeps one copy and repeats its ids, and the force
  models and `recombine` treat repeated entries with Java's object semantics.

`recombine` assigns every component the sum of its node priorities (node option `PRIORITY`) and its
bounding box, sorts the components by priority (descending) and bounding box area (ascending, stable),
and places them row by row left to right in a square-ish layout (`ASPECT_RATIO`, force default `1.6f`,
spacing `SPACING_NODE_NODE`, force default 80).
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

/-- Builds the component graph of the given nodes and edges (Java `dfs`: `component.getNodes().add`,
`component.getEdges().add(edge)`, `component.getLabels().addAll(edge.getLabels())`): copies of the nodes
(in the given order) and of the edges with their labels. Java keeps the *objects*: an edge the search
lists twice (the closing edge of a cycle, reached from both end nodes) is the same `FEdge` twice in
the edge list and its labels are the same `FLabel`s twice in the label list. The copy keeps that
identity: the second occurrence pushes the ids of the first copy again (the label then acts twice as a
particle, accumulates its displacement twice and is moved twice by `recombine`, all like Java). Java's
search adds no bend points to the component (the force models create them later). -/
private def buildComponent (graph : FGraph) (compNodes : Array FNodeId) (compEdges : Array FEdgeId) : FGraph :=
  Id.run do
    let mut component : FGraph := ({} : FGraph).copyProperties graph
    let mut remap : Std.HashMap Nat FNodeId := {}
    for old in compNodes do
      let (a, nid) := copyNode graph.arena component.arena old none
      component := { component with arena := a, nodes := component.nodes.push nid }
      remap := remap.insert old.idx nid
    let mut edgeMap : Std.HashMap Nat FEdgeId := {}
    for oldEid in compEdges do
      match edgeMap[oldEid.idx]? with
      | some newEid =>
        component := { component with
          edges := component.edges.push newEid
          labels := component.labels ++ component.arena.edgeLabels[newEid.idx]! }
      | none =>
        let (a, newEid) := copyEdge graph.arena component.arena oldEid remap
        component := { component with arena := a }
        for oldBid in graph.arena.edgeBendpoints[oldEid.idx]! do
          let (a, _) := copyBendpoint graph.arena component.arena oldBid newEid none
          component := { component with arena := a }
        for oldLid in graph.arena.edgeLabels[oldEid.idx]! do
          let (a, lid) := copyLabel graph.arena component.arena oldLid newEid none
          component := { component with arena := a, labels := component.labels.push lid }
        component := { component with edges := component.edges.push newEid }
        edgeMap := edgeMap.insert oldEid.idx newEid
    return component

/-- Renumbers the node ids of a component `0, 1, …` in node order (the component loop of `split`).
Out of line with the id column taken out of the component, so that `Array.map` updates the
exclusive component and its column in place (PLAN 7.1 items 59, 27). -/
@[noinline] private def renumberComponent (comp : FGraph) : FGraph := Id.run do
  let arena := comp.arena
  let comp := { comp with arena := {} }
  let mut nodeIds := arena.nodeId
  let arena := { arena with nodeId := #[] }
  for id in [0:comp.nodes.size] do
    nodeIds := nodeIds.set! (comp.nodes[id]!).idx id
  return { comp with arena := { arena with nodeId := nodeIds } }

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
    components := components.map renumberComponent
  return components

/-- `bounding_size`: size of the bounding box stored by `recombine`. -/
private def boundingSize (g : FGraph) : KVector :=
  (g.bbLowright.getD {}) - (g.bbUpleft.getD {})

/-- `moveGraph(destGraph, sourceGraph, offsetx, offsety)`: appends the nodes, edges and labels of
`source` to `dest`, translated by `(offsetX, offsetY) - BB_UPLEFT`. Java semantics (object lists):
* every node is moved once and added;
* for every entry of the edge list the bend points of the edge are moved and the edge is added, so the
  bend points of an edge listed twice (see `buildComponent`) are moved twice; the bend points are
  **not** added to the bend point list of `dest` (the packed graph's bounding box in `applyLayout`
  then ignores them);
* every entry of the label list is moved and added (a label listed twice is moved twice).
The arena copies keep that identity: an edge or label already copied is moved again instead of
copied again. -/
private def moveGraph (dest source : FGraph) (offsetX offsetY : Float) : FGraph := Id.run do
  let offset := KVector.mk offsetX offsetY - (source.bbUpleft.getD {})
  let mut dest := dest
  let mut remap : Std.HashMap Nat FNodeId := {}
  for old in source.nodes do
    let (a, nid) := copyNode source.arena dest.arena old (some offset)
    dest := { dest with arena := a, nodes := dest.nodes.push nid }
    remap := remap.insert old.idx nid
  let mut edgeMap : Std.HashMap Nat FEdgeId := {}
  for oldEid in source.edges do
    if !edgeMap.contains oldEid.idx then
      let (a, newEid) := copyEdge source.arena dest.arena oldEid remap
      dest := { dest with arena := a }
      for oldBid in source.arena.edgeBendpoints[oldEid.idx]! do
        let (a, _) := copyBendpoint source.arena dest.arena oldBid newEid none
        dest := { dest with arena := a }
      edgeMap := edgeMap.insert oldEid.idx newEid
    let some newEid := edgeMap[oldEid.idx]? | continue
    let mut bendPosition := dest.arena.bendPosition
    for bid in dest.arena.edgeBendpoints[newEid.idx]! do
      bendPosition := bendPosition.modifyIn bid.idx (· + offset)
    dest := { dest with arena := { dest.arena with bendPosition }, edges := dest.edges.push newEid }
  let mut labelMap : Std.HashMap Nat FLabelId := {}
  for oldLid in source.labels do
    match labelMap[oldLid.idx]? with
    | some lid =>
      dest := { dest with
        arena := { dest.arena with labelPosition := dest.arena.labelPosition.modifyIn lid.idx (· + offset) }
        labels := dest.labels.push lid }
    | none =>
      let some oldE := source.arena.labelEdge[oldLid.idx]! | continue
      let some newEid := edgeMap[oldE.idx]? | continue
      let (a, lid) := copyLabel source.arena dest.arena oldLid newEid (some offset)
      dest := { dest with arena := a, labels := dest.labels.push lid }
      labelMap := labelMap.insert oldLid.idx lid
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
  -- Java `double minx = Integer.MAX_VALUE, ..., maxx = Integer.MIN_VALUE` and `Math.min`/`Math.max`
  -- (a NaN position, e.g. after `iterations = 0`, propagates to the whole component)
  let mut minX := flIntMax
  let mut minY := flIntMax
  let mut maxX := flIntMin
  let mut maxY := flIntMin
  for nid in graph.nodes do
    priority := priority + (graph.arena.nodeProperties[nid.idx]!).getD ForceOptions.PRIORITY 1
    let pos := graph.arena.nodePosition[nid.idx]!
    let size := graph.arena.nodeSize[nid.idx]!
    minX := javaMin minX (pos.x - size.x / fl2p0)
    minY := javaMin minY (pos.y - size.y / fl2p0)
    maxX := javaMax maxX (pos.x + size.x / fl2p0)
    maxY := javaMax maxY (pos.y + size.y / fl2p0)
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
  let mut maxRowWidth : Float := fl0p0
  let mut totalArea : Float := fl0p0
  for graph in comps do
    let size := boundingSize graph
    maxRowWidth := javaMax maxRowWidth size.x
    totalArea := totalArea + size.x * size.y
  -- Java `(float) Math.sqrt(totalArea) * result.getProperty(ForceOptions.ASPECT_RATIO)` (force
  -- default 1.6f) and `ForceOptions.SPACING_NODE_NODE` (force default 80)
  let aspectRatio := result.props.getD ForceOptions.ASPECT_RATIO fl1p0
  maxRowWidth := javaMax maxRowWidth (Float.toF32 (Float.sqrt totalArea) * aspectRatio)
  let spacing := result.props.getD ForceOptions.SPACING_NODE_NODE fl0p0
  let mut xpos : Float := fl0p0
  let mut ypos : Float := fl0p0
  let mut highestBox : Float := fl0p0
  for graph in comps do
    let size := boundingSize graph
    if xpos + size.x > maxRowWidth then
      xpos := fl0p0
      ypos := ypos + (highestBox + spacing)
      highestBox := fl0p0
    result := moveGraph result graph xpos ypos
    highestBox := javaMax highestBox size.y
    xpos := xpos + (size.x + spacing)
  return result

end ComponentsProcessor

end Elk.Alg.Force
