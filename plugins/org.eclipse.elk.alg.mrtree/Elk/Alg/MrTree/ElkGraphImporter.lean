import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Graph
import Elk.Core.Math.KVector
import Elk.Core.Options
import Elk.Core.Util.ElkUtil
import Elk.Core.Util.Java
import Elk.Alg.MrTree.Graph.TArena
import Elk.Alg.MrTree.Options.MrTreeOptions
/-!
# `org.eclipse.elk.alg.mrtree.ElkGraphImporter`

Port of `elk_graph_importer.rs` (elk-rs), the only implementation of `IGraphImporter<ElkNode>`
(`i_graph_importer.rs`; the interface is folded into this module: `importGraph` and `applyLayout`).

`importGraph` runs in `ElkM` (it only reads the `ElkGraph`) and returns a new `TArena` holding the
imported `TGraph` (the arena is a value, see `Elk.Alg.MrTree.Graph.TArena`). The graph copies the
properties of the layout node; every child becomes a `TNode` (id = child index, label = text of the
first label or `""`, properties copied, position = centre of the child, size = child size but at least
1x1); then, for the children in order and their `allOutgoingEdges`, every edge that is neither
hierarchical, a self loop nor a hyperedge (Rust skips hyperedges, Java does not) and was not seen yet
becomes a `TEdge` between the two tree nodes (properties copied), appended to the graph's edge list.
No `TLabel`s are created.

`applyLayout` writes the result of the (packed) graph back: the bounding box of the node boxes (centre
± half size, `f64::min`/`f64::max`), every node's top-left position and its *public* properties (Rust
copies the whole property map, which contains the internal properties too; those are typed fields in
Lean and are not written back), every edge's bend points into its first section (Java `firstEdgeSection(edge, true, true)`: created
if missing, reset, further sections removed; Rust neither resets it nor removes further sections),
where an edge with fewer than two bend points gets the chain `source centre -> target centre`
(`position + size / 2` of the tree nodes). The layout node is resized to the box plus padding (unless
`NODE_SIZE_FIXED_GRAPH_SIZE`, without moving ports or labels) and `CHILD_AREA_WIDTH`/`HEIGHT` are set.
A graph without `ORIGIN` (the empty graph returned by `ComponentsProcessor.pack` for no components) is
ignored.

Rust keeps hash maps from pointer-derived origin ids to `ElkGraph` elements; here the origin is the
typed `ElkGraph` id, so the maps are not needed.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl1p0 : Float := 1.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.MrTree

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Util Elk.Core.Options
open Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options

namespace ElkGraphImporter

/-- Pure part of `import_graph`: the arena with the imported graph. -/
def importGraphPure (g : ElkGraph) (elkgraph : NodeId) : TArena × TGraphId := Id.run do
  let root := g.node elkgraph
  let (a, tg) := ({} : TArena).createGraph
  let mut a := a.modifyGraph tg fun x =>
    { x with props := x.props.copyFrom root.props, internal.origin := some (.elkNode elkgraph) }
  let children := root.children
  let mut elemMap : Std.HashMap NodeId TNodeId := {}
  for index in [0:children.size] do
    let child := children[index]!
    let elknode := g.node child
    let label := match elknode.labels[0]? with
      | some l => (g.label l).text
      | none => ""
    let (a', tn) := a.createNode (index : Int) (some tg) (some label)
    a := a'.modifyNode tn fun n =>
      { n with
        props := n.props.copyFrom elknode.props
        position := ⟨elknode.x + elknode.width / fl2p0, elknode.y + elknode.height / fl2p0⟩
        size := ⟨fmax elknode.width fl1p0, fmax elknode.height fl1p0⟩
        internal.origin := some (.elkNode child) }
    elemMap := elemMap.insert child tn
  let mut seen : Std.HashSet EdgeId := {}
  for child in children do
    for e in ElkGraphUtil.allOutgoingEdges g child do
      let elkedge := g.edge e
      if ElkGraphUtil.isHierarchicalEdge g e || ElkGraphUtil.isSelfloop g e || elkedge.isHyperedge then
        continue
      if seen.contains e then continue
      let some targetShape := elkedge.targets[0]? | continue
      let some targetNode := ElkGraphUtil.connectableShapeToNode g targetShape | continue
      if let (some source, some target) := (elemMap[child]?, elemMap[targetNode]?) then
        let (a', te) := a.createEdge source target
        a := a'.modifyEdge te fun x =>
          { x with props := x.props.copyFrom elkedge.props, internal.origin := some (.elkEdge e) }
        a := a.modifyGraph tg fun x => { x with edges := x.edges.push te }
        seen := seen.insert e
  return (a, tg)

/-- `IGraphImporter::import_graph(elkgraph)`: a new arena with the imported graph. -/
def importGraph (elkgraph : NodeId) : ElkM (TArena × TGraphId) := do
  return importGraphPure (← get) elkgraph

/-- `IGraphImporter::apply_layout(tgraph)`. -/
def applyLayout (a : TArena) (tgraph : TGraphId) : ElkM Unit := do
  let graph := a.graph tgraph
  let some (.elkNode root) := graph.internal.origin | return
  let mut minX := Float.maxValue
  let mut minY := Float.maxValue
  let mut maxX := Float.minValue
  let mut maxY := Float.minValue
  for node in graph.nodes do
    let n := a.node node
    minX := fmin minX (n.position.x - n.size.x / fl2p0)
    minY := fmin minY (n.position.y - n.size.y / fl2p0)
    maxX := fmax maxX (n.position.x + n.size.x / fl2p0)
    maxY := fmax maxY (n.position.y + n.size.y / fl2p0)
  let padding := ((← ElkM.getNode root).props.get MrTreeOptions.PADDING).getD {}
  for node in graph.nodes do
    let n := a.node node
    let some (.elkNode elkNode) := n.internal.origin | continue
    ElkM.modifyNode elkNode fun x =>
      { x with x := n.position.x, y := n.position.y, props := x.props.copyFrom n.props }
  for edge in graph.edges do
    let te := a.edge edge
    let some (.elkEdge elkEdge) := te.internal.origin | continue
    let mut bendPoints := te.bendPoints
    if bendPoints.size < 2 then
      let (some s, some t) := (te.source, te.target) | continue
      let sn := a.node s
      let tn := a.node t
      bendPoints := #[⟨sn.position.x + sn.size.x / fl2p0, sn.position.y + sn.size.y / fl2p0⟩,
        ⟨tn.position.x + tn.size.x / fl2p0, tn.position.y + tn.size.y / fl2p0⟩]
    -- Java `ElkGraphUtil.firstEdgeSection(elkedge, true, true)` (elk-rs keeps the other sections)
    let edgeSection ← modifyGet fun g =>
      let (g, s) := ElkGraphUtil.firstEdgeSection g elkEdge true true; (s, g)
    ElkUtil.applyVectorChain bendPoints edgeSection
  let paddingHorizontal := padding.left + padding.right
  let paddingVertical := padding.top + padding.bottom
  let width := maxX - minX + paddingHorizontal
  let height := maxY - minY + paddingVertical
  let fixedSize := ((← ElkM.getNode root).props.get CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE).getD false
  if !fixedSize then
    discard <| ElkUtil.resizeNodeWith root width height false false
  ElkM.setNodeProp root CoreOptions.CHILD_AREA_WIDTH (width - paddingHorizontal)
  ElkM.setNodeProp root CoreOptions.CHILD_AREA_HEIGHT (height - paddingVertical)

end ElkGraphImporter

end Elk.Alg.MrTree
