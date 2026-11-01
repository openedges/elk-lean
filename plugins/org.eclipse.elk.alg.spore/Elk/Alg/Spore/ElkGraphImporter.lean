import Std.Data.HashMap
import Elk.Core.Util.ElkUtil
import Elk.Core.Util.Random
import Elk.Core.Util.Adapters
import Elk.Alg.Common.NodeSpacing.NodeDimensionCalculation
import Elk.Alg.Spore.IGraphImporter
import Elk.Alg.Spore.Options.SporeCompactionOptions
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.spore.ElkGraphImporter`

Port of `elk_graph_importer.rs` (elk-rs) and `ElkGraphImporter.java`: transforms the children of an
`ElkNode` into a SPOrE `Graph` and writes the result back.

`importGraph` computes the node margins (`NodeDimensionCalculation.calculateNodeMargins`), reads
the options of the root node, and creates one vertex per child: the vertex is the center of the
node; vertices that coincide with an earlier one are wiggled with a `Random` seeded with `0`
(amount `0.001`) until they are unique; the vertex' rectangle is the node's bounds enlarged by the
margins and `spacing.nodeNode` (half on each side). The preferred root is the first vertex (`FIXED`
without a preferred root id), the vertex whose node has the preferred root id (`FIXED`), or the
vertex closest to the center of the root node (`CENTER_NODE`).

`applyPositions` sets the node locations, resizes the root to the bounding box plus padding,
translates the children, and re-routes every contained edge as a straight line between the
clipped node centers.

Rust differences from Java kept: `first_edge_section(edge, reset = true, removeOthers = true)`
keeps the **last** section (`retain_last`) of an edge with several sections and returns the former
first section (which then is detached); the vertex wiggle adds `(r * amount - amount / 2)` as one
term (the `KVector.wiggle` of the core adds in a different order, which rounds differently).
-/

namespace Elk.Alg.Spore

open Elk Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.Common.Spore Elk.Alg.Common.NodeSpacing Elk.Alg.Spore.Graph Elk.Alg.Spore.Options

/-- Mutable state of an `ElkGraphImporter`. -/
structure ElkGraphImporterState where
  /-- `node_map`: vertex ↦ the `ElkNode` it was created for. -/
  nodeMap : Std.HashMap KVector NodeId := {}
  /-- The imported graph (`elk_graph`). -/
  elkGraph : Option NodeId := none
  /-- The `spacing.nodeNode` value of the imported graph. -/
  spacingNodeNode : Float := fl0p0

/-- `org.eclipse.elk.alg.spore.ElkGraphImporter`: an `IO.Ref` handle (the Java/Rust object is
mutable and lives across the iterations of the overlap removal). -/
structure ElkGraphImporter where
  ref : IO.Ref ElkGraphImporterState

namespace ElkGraphImporter

/-- `ElkGraphImporter::new()`. -/
def new : IO ElkGraphImporter := return ⟨← IO.mkRef {}⟩

/-- Rust `KVector::wiggle(random, amount)` (`Elk.Core.Math.KVector.wiggle`). -/
@[inline] private def wiggle (v : KVector) (random : Random) (amount : Float) : KVector × Random :=
  KVector.wiggle v random amount

/-- Creates the vertex of a node (unique center, wiggled with `random`) and its rectangle. -/
private def createNode (nodeMap : Std.HashMap KVector NodeId) (random : Random)
    (spacingNodeNode : Float) (n : ElkNode) : Node × Random := Id.run do
  let halfWidth := n.width / fl2p0
  let halfHeight := n.height / fl2p0
  let mut vertex : KVector := ⟨n.x + halfWidth, n.y + halfHeight⟩
  let mut random := random
  while nodeMap.contains vertex do
    let (v, r) := wiggle vertex random fl0p001
    vertex := v
    random := r
  let margin : ElkMargin := (n.props.get CoreOptions.MARGINS).getD default
  let rect := ElkRectangle.ofValues
    (vertex.x - halfWidth - spacingNodeNode / fl2p0 - margin.left)
    (vertex.y - halfHeight - spacingNodeNode / fl2p0 - margin.top)
    (n.width + spacingNodeNode + margin.left + margin.right)
    (n.height + spacingNodeNode + margin.top + margin.bottom)
  return (Node.new vertex rect, random)

/-- The index of the vertex closest to `center` (the first one on ties). -/
private def closestVertex (vertices : Array Node) (center : KVector) : Option Nat := Id.run do
  let mut closest := Float.posInf
  let mut best : Option Nat := none
  let mut idx := 0
  for node in vertices do
    let distance := node.originalVertex.distance center
    if distance < closest then
      closest := distance
      best := some idx
    idx := idx + 1
  return best

/-- `import_graph(input_graph)`. -/
def importGraph (imp : ElkGraphImporter) (inputGraph : NodeId) : ElkM Graph := do
  imp.ref.modify fun s => { s with elkGraph := some inputGraph, nodeMap := {} }
  let adapter ← ElkGraphAdapters.adapt inputGraph
  NodeDimensionCalculation.calculateNodeMargins adapter inputGraph
  let root ← ElkM.getNode inputGraph
  let props := root.props
  let preferredRootId : Option String := props.get SporeCompactionOptions.PROCESSING_ORDER_PREFERRED_ROOT
  let costFunction := (props.get SporeCompactionOptions.PROCESSING_ORDER_SPANNING_TREE_COST_FUNCTION).getD default
  let treeConstruction := (props.get SporeCompactionOptions.PROCESSING_ORDER_TREE_CONSTRUCTION).getD default
  let compactionStrategy := (props.get SporeCompactionOptions.COMPACTION_COMPACTION_STRATEGY).getD default
  let rootSelection := (props.get SporeCompactionOptions.PROCESSING_ORDER_ROOT_SELECTION).getD default
  let spacingNodeNode := (props.get SporeCompactionOptions.SPACING_NODE_NODE).getD 0.0
  imp.ref.modify fun s => { s with spacingNodeNode }
  let mut graph := Graph.new costFunction treeConstruction compactionStrategy
  let debugMode := (props.get SporeCompactionOptions.DEBUG_MODE).getD false
  graph := graph.setProperty InternalProperties.DEBUG_SVG debugMode
  graph := { graph with
    orthogonalCompaction := (props.get SporeCompactionOptions.COMPACTION_ORTHOGONAL).getD false }
  if root.children.isEmpty then return graph
  let mut random := Random.ofUInt64 0
  let mut nodeMap : Std.HashMap KVector NodeId := {}
  let mut vertices : Array Node := #[]
  for elkNode in root.children do
    let n ← ElkM.getNode elkNode
    let (node, r) := createNode nodeMap random spacingNodeNode n
    random := r
    vertices := vertices.push node
    nodeMap := nodeMap.insert node.vertex elkNode
  imp.ref.modify fun s => { s with nodeMap }
  graph := Graph.rebuildIndexMap { graph with vertices }
  match rootSelection with
  | .fixed =>
    match preferredRootId with
    | none => graph := { graph with preferredRootIndex := some 0 }
    | some preferredId =>
      let mut idx := 0
      for node in vertices do
        if let some elkNode := nodeMap.get? node.originalVertex then
          if (← ElkM.getNode elkNode).identifier == some preferredId then
            graph := { graph with preferredRootIndex := some idx }
            break
        idx := idx + 1
  | .centerNode =>
    let center : KVector := (KVector.scale ⟨root.width, root.height⟩ 0.5).addValues root.x root.y
    graph := { graph with preferredRootIndex := closestVertex vertices center }
  return graph

/-- `update_graph(graph)`: clears the edges and the tree and moves every vertex' `originalVertex` to
the center of its rectangle (vertices whose original vertex is unknown are left alone). -/
def updateGraph (imp : ElkGraphImporter) (graph : Graph) : IO Graph := do
  let s ← imp.ref.get
  let mut updatedMap : Std.HashMap KVector NodeId := {}
  let mut vertices : Array Node := #[]
  for node in graph.vertices do
    match s.nodeMap.get? node.originalVertex with
    | none => vertices := vertices.push node
    | some elkNode =>
      let node := { node with originalVertex := node.rect.center }
      vertices := vertices.push node
      updatedMap := updatedMap.insert node.originalVertex elkNode
  imp.ref.modify fun s => { s with nodeMap := updatedMap }
  return Graph.rebuildIndexMap { graph with tEdges := none, tree := none, vertices }

/-- Java `ElkGraphUtil.firstEdgeSection(e, true, true)`: the first section of the edge, reset (no
bend points, zero start and end), the other sections removed; creates a section if there is none.
(Rust `first_edge_section` resets the first section and then keeps the *last* one, so with several
sections it routed a detached section.) -/
private def firstEdgeSection (edge : EdgeId) : ElkM SectionId :=
  modifyGet fun g => let (g, s) := ElkGraphUtil.firstEdgeSection g edge true true; (s, g)

/-- Bounds `(x, y, width, height)` of a node. -/
private def nodeBounds (n : NodeId) : ElkM (Float × Float × Float × Float) := do
  let node ← ElkM.getNode n
  return (node.x, node.y, node.width, node.height)

/-- Re-routes an edge as a straight line between the clipped centers of its first source and first
target node. -/
private def routeEdge (edge : EdgeId) : ElkM Unit := do
  let section_ ← firstEdgeSection edge
  let g ← get
  let e := g.edge edge
  let source := e.sources[0]?.bind (ElkGraphUtil.connectableShapeToNode g)
  let target := e.targets[0]?.bind (ElkGraphUtil.connectableShapeToNode g)
  let (some source, some target) := (source, target) | return
  let (sx, sy, sw, sh) ← nodeBounds source
  let (tx, ty, tw, th) ← nodeBounds target
  let startLocation : KVector := ⟨sx + sw / 2.0, sy + sh / 2.0⟩
  let endLocation : KVector := ⟨tx + tw / 2.0, ty + th / 2.0⟩
  let uv := ElkMath.clipVector (endLocation - startLocation) sw sh
  let startLocation := startLocation + uv
  let vu := ElkMath.clipVector (startLocation - endLocation) tw th
  let endLocation := endLocation + vu
  ElkM.modifySection section_ fun s =>
    { s with startX := startLocation.x, startY := startLocation.y,
             endX := endLocation.x, endY := endLocation.y }

/-- `apply_positions(graph)`. -/
def applyPositions (imp : ElkGraphImporter) (graph : Graph) : ElkM Unit := do
  let s ← imp.ref.get
  let some elkGraph := s.elkGraph | return
  let mut minX := Float.posInf
  let mut minY := Float.posInf
  let mut maxX := Float.negInf
  let mut maxY := Float.negInf
  for node in graph.vertices do
    let some elkNode := s.nodeMap.get? node.originalVertex | continue
    ElkM.modifyNode elkNode fun n => { n with x := node.rect.x, y := node.rect.y }
    let (x, y, width, height) ← nodeBounds elkNode
    minX := fmin minX x
    minY := fmin minY y
    maxX := fmax maxX (x + width)
    maxY := fmax maxY (y + height)
  if minX == Float.posInf || minY == Float.posInf then return
  let padding : ElkPadding :=
    ((← ElkM.getNode elkGraph).props.get SporeCompactionOptions.PADDING).getD default
  let _ ← ElkUtil.resizeNodeWith elkGraph (maxX - minX + padding.left + padding.right)
    (maxY - minY + padding.top + padding.bottom) true true
  ElkUtil.translateNode elkGraph (-minX + padding.left) (-minY + padding.top)
  for edge in (← ElkM.getNode elkGraph).containedEdges do
    routeEdge edge

instance : IGraphImporter ElkGraphImporter NodeId ElkM where
  importGraph := importGraph
  updateGraph imp g := updateGraph imp g
  applyPositions := applyPositions

end ElkGraphImporter

end Elk.Alg.Spore
