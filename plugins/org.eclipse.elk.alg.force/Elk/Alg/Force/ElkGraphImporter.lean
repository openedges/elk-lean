import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Graph
import Elk.Graph.Impl.EMapPropertyHolderImpl
import Elk.Core.Exceptions
import Elk.Core.Math.KVector
import Elk.Core.Options
import Elk.Core.Util.ElkUtil
import Elk.Core.Util.Java
import Elk.Alg.Force.Graph.FGraph
import Elk.Alg.Force.Options.ForceOptions
/-!
# `org.eclipse.elk.alg.force.ElkGraphImporter`

Port of `elk_graph_importer.rs` (elk-rs), the only implementation of Java's `IGraphImporter<ElkNode>`
(the interface is folded into this module: `importGraph` and `applyLayout`).

`importGraph` converts the children of a layout node into an `FGraph`: one node per child (centre
position, size at least 1x1, label text of the first label), one edge per non-hierarchical,
non-self-loop edge between two children, with one label per edge label. Hyperedges raise an
`UnsupportedGraphException`. As a side effect, children without port constraints get
`PORT_CONSTRAINTS = FREE` (like Rust).

`applyLayout` writes the positions back: nodes are shifted so that the padded bounding box starts at the
origin, every edge gets a single section (start point, bend points, end point), labels are moved and
the layout node is resized (unless `NODE_SIZE_FIXED_GRAPH_SIZE`); the child area size is stored.

Rust keeps hash maps from pointer-derived origin ids to `ElkGraph` elements; here the origin of an
`FGraph` element is the typed `ElkGraph` id (see `Options.InternalProperties`), so no maps are needed.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Force

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Alg.Force.Graph Elk.Alg.Force.Options

namespace ElkGraphImporter

/-- The `PORT_CONSTRAINTS = FREE` default of the force algorithms: stored on the node unless the node
already has constraints other than `UNDEFINED`. -/
private def ensurePortConstraints (node : NodeId) : ElkM Unit := do
  let current := ((← ElkM.getNode node).props.get ForceOptions.PORT_CONSTRAINTS).getD PortConstraints.undefined
  if current == PortConstraints.undefined then
    ElkM.setNodeProp node ForceOptions.PORT_CONSTRAINTS PortConstraints.free

/-- Imports one `ElkNode` child as an `FNode` (index `index` becomes its node id). -/
private def importNode (fgraph : FGraph) (child : NodeId) (index : Nat) : ElkM (FGraph × FNodeId) := do
  let g ← get
  let elknode := g.node child
  let label := match elknode.labels[0]? with
    | some l => (g.label l).text
    | none => ""
  let (a, nid) := fgraph.arena.addNode
  let i := nid.idx
  let w := elknode.width
  let h := elknode.height
  let a := { a with
    nodeId := a.nodeId.set! i index
    nodeLabel := a.nodeLabel.set! i (some label)
    nodeProperties := a.nodeProperties.set! i elknode.props
    nodePosition := a.nodePosition.set! i ⟨elknode.x + w / 2.0, elknode.y + h / 2.0⟩
    nodeSize := a.nodeSize.set! i ⟨fmax w 1.0, fmax h 1.0⟩
    nodeOrigin := a.nodeOrigin.set! i (some (Origin.elkNode child)) }
  return ({ fgraph with arena := a, nodes := fgraph.nodes.push nid }, nid)

/-- Imports an edge and its labels. -/
private def importEdge (fgraph : FGraph) (g : ElkGraph) (e : EdgeId) (source target : FNodeId) : FGraph :=
  Id.run do
    let elkedge := g.edge e
    let (a, eid) := fgraph.arena.addEdge
    let i := eid.idx
    let a := { a with
      edgeProperties := a.edgeProperties.set! i elkedge.props
      edgeOrigin := a.edgeOrigin.set! i (some (Origin.elkEdge e)) }
    let a := (a.setEdgeSource eid source).setEdgeTarget eid target
    let mut fgraph := { fgraph with arena := a, edges := fgraph.edges.push eid }
    for l in elkedge.labels do
      let elklabel := g.label l
      let (a, lid) := fgraph.arena.addLabel eid
      let j := lid.idx
      let a := { a with
        labelText := a.labelText.set! j (some elklabel.text)
        labelProperties := a.labelProperties.set! j elklabel.props
        labelOrigin := a.labelOrigin.set! j (some (Origin.elkLabel l))
        labelSize := a.labelSize.set! j ⟨fmax elklabel.width fl1p0, fmax elklabel.height fl1p0⟩ }
      fgraph := { fgraph with arena := a }
      fgraph := fgraph.refreshLabelPosition lid
      fgraph := { fgraph with labels := fgraph.labels.push lid }
    return fgraph

/-- `IGraphImporter::import_graph(elkgraph)`. -/
def importGraph (elkgraph : NodeId) : ElkM FGraph := do
  let root ← ElkM.getNode elkgraph
  let mut fgraph : FGraph := { props := root.props, origin := some (Origin.elkNode elkgraph) }
  let children := root.children
  let mut elemMap : Std.HashMap NodeId FNodeId := {}
  for index in [0:children.size] do
    let child := children[index]!
    let (fg, nid) ← importNode fgraph child index
    fgraph := fg
    elemMap := elemMap.insert child nid
    ensurePortConstraints child
  let g ← get
  let mut seen : Std.HashSet EdgeId := {}
  for child in children do
    for e in ElkGraphUtil.allOutgoingEdges g child do
      let elkedge := g.edge e
      if elkedge.isHyperedge then
        throwUnsupportedGraph "Graph must not contain hyperedges."
      if ElkGraphUtil.isHierarchicalEdge g e || ElkGraphUtil.isSelfloop g e then continue
      if seen.contains e then continue
      let some targetShape := elkedge.targets[0]? | continue
      let some targetNode := ElkGraphUtil.connectableShapeToNode g targetShape | continue
      if let (some source, some target) := (elemMap[child]?, elemMap[targetNode]?) then
        fgraph := importEdge fgraph g e source target
        seen := seen.insert e
  return fgraph

/-- `ensure_single_section`: the first section of the edge (creating one if needed, keeping only the
last of several), reset to an empty section. -/
private def ensureSingleSection (e : EdgeId) : ElkM SectionId := do
  let sections := (← ElkM.getEdge e).sections
  if sections.isEmpty then
    ElkM.createSection (some e)
  else
    if sections.size > 1 then modify (·.retainLastEdgeSection e)
    return (← ElkM.getEdge e).sections[0]!

/-- Minimum and maximum corner of the node and bend point boxes of a force graph. -/
private def boundingBox (fgraph : FGraph) : Float × Float × Float × Float := Id.run do
  let mut minX := Float.maxValue
  let mut minY := Float.maxValue
  let mut maxX := Float.minValue
  let mut maxY := Float.minValue
  for nid in fgraph.nodes do
    let pos := fgraph.arena.nodePosition[nid.idx]!
    let size := fgraph.arena.nodeSize[nid.idx]!
    minX := fmin minX (pos.x - size.x / fl2p0)
    minY := fmin minY (pos.y - size.y / fl2p0)
    maxX := fmax maxX (pos.x + size.x / fl2p0)
    maxY := fmax maxY (pos.y + size.y / fl2p0)
  for bid in fgraph.bendpoints do
    let pos := fgraph.arena.bendPosition[bid.idx]!
    let size := fgraph.arena.bendSize[bid.idx]!
    minX := fmin minX (pos.x - size.x / fl2p0)
    minY := fmin minY (pos.y - size.y / fl2p0)
    maxX := fmax maxX (pos.x + size.x / fl2p0)
    maxY := fmax maxY (pos.y + size.y / fl2p0)
  return (minX, minY, maxX, maxY)

/-- `IGraphImporter::apply_layout(graph)`. -/
def applyLayout (fgraph : FGraph) : ElkM Unit := do
  let some (Origin.elkNode root) := fgraph.origin | return
  let (minX, minY, maxX, maxY) := boundingBox fgraph
  -- Java `kgraph.getProperty(ForceOptions.PADDING)`: the force default (50) is stored when unset
  let padding := (← ElkM.getNodePropSticky root ForceOptions.PADDING).getD (ElkPadding.ofAny fl0p0)
  let offset : KVector := ⟨padding.left - minX, padding.top - minY⟩
  for nid in fgraph.nodes do
    let some (Origin.elkNode node) := fgraph.arena.nodeOrigin[nid.idx]! | continue
    let nodePos := fgraph.arena.nodePosition[nid.idx]! + offset
    ElkM.modifyNode node fun n =>
      { n with x := nodePos.x - n.width / fl2p0, y := nodePos.y - n.height / fl2p0 }
  for eid in fgraph.edges do
    let some (Origin.elkEdge edge) := fgraph.arena.edgeOrigin[eid.idx]! | continue
    let sec ← ensureSingleSection edge
    let start := (fgraph.edgeSourcePoint eid).map (· + offset)
    let bends := (fgraph.arena.edgeBendpoints[eid.idx]!).map fun bid =>
      fgraph.arena.bendPosition[bid.idx]! + offset
    let «end» := (fgraph.edgeTargetPoint eid).map (· + offset)
    ElkM.modifySection sec fun s =>
      { s with
        bendPoints := bends
        startX := (start.map (·.x)).getD fl0p0
        startY := (start.map (·.y)).getD fl0p0
        endX := («end».map (·.x)).getD fl0p0
        endY := («end».map (·.y)).getD fl0p0 }
  for lid in fgraph.labels do
    let some (Origin.elkLabel label) := fgraph.arena.labelOrigin[lid.idx]! | continue
    let labelPos := fgraph.arena.labelPosition[lid.idx]! + offset
    ElkM.modifyLabel label fun l => { l with x := labelPos.x, y := labelPos.y }
  let horizontal := padding.left + padding.right
  let vertical := padding.top + padding.bottom
  let width := (maxX - minX) + horizontal
  let height := (maxY - minY) + vertical
  let fixedGraphSize := ((← ElkM.getNode root).props.get ForceOptions.NODE_SIZE_FIXED_GRAPH_SIZE).getD false
  if !fixedGraphSize then
    let _ ← ElkUtil.resizeNodeWith root width height false true
  ElkM.setNodeProp root CoreOptions.CHILD_AREA_WIDTH (width - horizontal)
  ElkM.setNodeProp root CoreOptions.CHILD_AREA_HEIGHT (height - vertical)

end ElkGraphImporter

end Elk.Alg.Force
