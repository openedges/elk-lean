import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Core.Util.ElkUtil
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Alg.Layered.Intermediate.LabelDummySwitcher
/-!
# `org.eclipse.elk.alg.layered.graph.transform.ElkGraphLayoutTransferrer`

Port of elk-rs `graph/transform/elk_graph_layout_transferrer.rs` (Java
`ElkGraphLayoutTransferrer`): "Implements the graph layout application aspect of
`ElkGraphTransformer`." It applies the layout stored in the layered arena (positions, sizes,
bend points, junction points, label positions, computed padding, graph size) to the ElkGraph
elements the layered elements were created from.

The layered arena is read-only input and the ElkGraph is the `ElkM` state. The Rust
`OriginStore` lookups (`get_node`/`get_port`/`get_edge`/`get_label`) are replaced by the ids in
`Origin.elkNode`/`elkPort`/`elkEdge`/`elkLabel` (an id outside the ElkGraph arena behaves like a
missing store entry).

All documented elk-rs corrections of the Java original are ported (they decide the final
coordinates compared with the oracle):
* nodes of the layers *and* the layerless nodes are processed (`collect_nodes_from_graph`);
* content alignment offset when a minimum size enlarges the graph (`apply_content_alignment_offset`);
* node sizes are also written for nested graphs and network-simplex flexible-size nodes;
* port sizes are written, node labels only when a node *or label* has `NODE_LABELS_PLACEMENT`
  (`has_property`), port labels only when the port label placement is not fixed;
* the hierarchical offset adds `representingNode.position + parentGraph.offset +
  parentGraph.padding` per level (`calculate_hierarchical_offset`, at most 512 levels);
* `INSIDE_SELF_LOOPS_YO` edges that already have a geometry are left untouched;
* the first edge section is reused (identifier/properties kept), its geometry reset and the
  other sections dropped;
* edges of the container that did not get a section receive a straight fallback section
  (`apply_fallback_sections`, also recursively for all descendants);
* the parent node is resized only for root graphs (no representing `LNode`).

Deviations from the Rust code:
* The Rust `ElkTrace::global()` debug prints (`debug_edges`, `edge_apply`, `compound_width`,
  `trace`, `edge_offsets`) are omitted; they do not change any state.
* `LGraph` has no `ORIGIN` field in the Lean arena (`LGraphInternals`), so the ElkNode of a
  graph is resolved by `graphOrigin`: a nested graph's origin is the origin of its
  representing `LNode` (the importer stores the same ElkNode on both), the root graph's origin
  is the explicit `elkGraph` argument of `applyLayout`.
* `LGraphUtil.getExternalPortPosition` moves the external port dummies (as in Java/Rust, and
  the moved positions are seen by the edges processed afterwards); the arena is therefore
  threaded through the recursion locally and the final arena is discarded.
-/
namespace Elk.Alg.Layered.Graph.Transform

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate

namespace ElkGraphLayoutTransferrer

/-! ## Origin lookups -/

/-- `OriginStore::get_node(id)`: `none` when the id is outside the ElkGraph arena. -/
private def elkNodeOf? (n : NodeId) : ElkM (Option NodeId) := do
  return if n.idx < (← get).nodes.size then some n else none

/-- `OriginStore::get_port(id)`. -/
private def elkPortOf? (p : PortId) : ElkM (Option PortId) := do
  return if p.idx < (← get).ports.size then some p else none

/-- `OriginStore::get_edge(id)`. -/
private def elkEdgeOf? (e : EdgeId) : ElkM (Option EdgeId) := do
  return if e.idx < (← get).edges.size then some e else none

/-- `OriginStore::get_label(id)`. -/
private def elkLabelOf? (l : LabelId) : ElkM (Option LabelId) := do
  return if l.idx < (← get).labels.size then some l else none

/-- `lgraph.get_property(InternalProperties::ORIGIN)` as `Origin::ElkNode`: the representing
node's ElkNode origin for a nested graph, `elkGraph` for the root graph (see module doc). -/
private def graphOrigin (a : LGraphArena) (elkGraph : NodeId) (lgraph : LGraphId) : Option NodeId :=
  match (a.graph lgraph).parentNode with
  | none => some elkGraph
  | some parentNode =>
    match (a.node parentNode).internal.origin with
    | some (.elkNode id) => some id
    | _ => none

/-- `LGraphUtil::is_descendant(child, parent)` on a read-only arena. -/
private def isDescendant (a : LGraphArena) (child parent : LNodeId) : IO Bool := do
  let (r, _) ← LayeredM.run (LGraphUtil.isDescendant child parent) a
  return r

/-! ## Helpers -/

/-- Rust `uses_network_simplex_flexible_size(lnode)` (Java inline condition
`NETWORK_SIMPLEX && NodeFlexibility.getNodeFlexibility(lnode).isFlexibleSizeWhereSpacePermits()`):
the node's own `NODE_FLEXIBILITY` if set, else the graph's `NODE_FLEXIBILITY_DEFAULT`, else that
option's default. -/
private def usesNetworkSimplexFlexibleSize (a : LGraphArena) (lnode : LNodeId) : Bool :=
  match a.nodeGraph lnode with
  | none => false
  | some graph =>
    let graphProps := (a.graph graph).props
    let strategy := graphProps.getD LayeredOptions.NODE_PLACEMENT_STRATEGY .brandesKoepf
    if strategy != .networkSimplex then false
    else
      let nodeProps := (a.node lnode).props
      let fromNode : Option NodeFlexibility :=
        if nodeProps.has LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY then
          nodeProps.get LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY
        else none
      let flexibility : NodeFlexibility :=
        (fromNode <|> graphProps.get LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT
          <|> LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT.default).getD .none
      flexibility.isFlexibleSizeWhereSpacePermits

/-- Rust `collect_nodes_from_graph(graph)`: the layerless nodes followed by the nodes of each
layer (in layer order), each node once (first occurrence wins). -/
private def collectNodesFromGraph (a : LGraphArena) (lgraph : LGraphId) : Array LNodeId := Id.run do
  let gr := a.graph lgraph
  let mut seen : Std.HashSet LNodeId := {}
  let mut nodes : Array LNodeId := #[]
  for n in gr.layerlessNodes do
    if !seen.contains n then
      seen := seen.insert n
      nodes := nodes.push n
  for l in gr.layers do
    for n in (a.layer l).nodes do
      if !seen.contains n then
        seen := seen.insert n
        nodes := nodes.push n
  return nodes

/-- Rust `first_shape(list)`: the first source or target of an ElkEdge. -/
private def firstShape (shapes : Array ConnectableId) : Option ConnectableId := shapes[0]?

/-- Rust `apply_content_alignment_offset(lgraph, offset)`: "Applies content alignment
adjustments to the offset when the actual graph size (with minimum size constraints) is larger
than the calculated size. This is analogous to
`HierarchicalNodeResizingProcessor::resizeGraphNoReallyIMeanIt`." Returns the new offset. -/
private def applyContentAlignmentOffset (a : LGraphArena) (lgraph : LGraphId) (offset : KVector) : KVector := Id.run do
  let gr := a.graph lgraph
  let sizeConstraint := gr.props.getD LayeredOptions.NODE_SIZE_CONSTRAINTS EnumSet.noneOf
  let contentAlignment := gr.props.getD CoreOptions.CONTENT_ALIGNMENT EnumSet.noneOf
  let calculatedSize := gr.actualSize
  -- only applied with a minimum size constraint
  if !sizeConstraint.contains .minimumSize then return offset
  let mut minSize := gr.props.getD LayeredOptions.NODE_SIZE_MINIMUM KVector.zero
  let sizeOptions := gr.props.getD CoreOptions.NODE_SIZE_OPTIONS EnumSet.noneOf
  if sizeOptions.contains .defaultMinimumSize then
    if minSize.x <= 0.0 then minSize := { minSize with x := ElkUtil.DEFAULT_MIN_WIDTH }
    if minSize.y <= 0.0 then minSize := { minSize with y := ElkUtil.DEFAULT_MIN_HEIGHT }
  let actualSize : KVector := ⟨fmax calculatedSize.x minSize.x, fmax calculatedSize.y minSize.y⟩
  let mut offset := offset
  if actualSize.x > calculatedSize.x then
    if contentAlignment.contains .hCenter then
      offset := { offset with x := offset.x + (actualSize.x - calculatedSize.x) / 2.0 }
    else if contentAlignment.contains .hRight then
      offset := { offset with x := offset.x + (actualSize.x - calculatedSize.x) }
  if actualSize.y > calculatedSize.y then
    if contentAlignment.contains .vCenter then
      offset := { offset with y := offset.y + (actualSize.y - calculatedSize.y) / 2.0 }
    else if contentAlignment.contains .vBottom then
      offset := { offset with y := offset.y + (actualSize.y - calculatedSize.y) }
  return offset

/-- Rust `calculate_hierarchical_offset(ledge)` (Java `calculateHierarchicalOffset`): "If the
coordinates of an edge must be relative to a different node than they are in the algorithm,
this method returns the correct offset to translate from the algorithm's coordinate system to
the necessary target coordinate system." Starting at the source node's graph, each level up adds
`representingNode.position + parentGraph.offset + parentGraph.padding.(left, top)` until the
edge's `COORDINATE_SYSTEM_ORIGIN` graph is reached (at most 512 levels; missing links stop). -/
private def calculateHierarchicalOffset (a : LGraphArena) (ledge : LEdgeId) : KVector := Id.run do
  let ed := a.edge ledge
  let some targetGraph := ed.internal.coordinateSystemOrigin | return KVector.zero
  let mut result := KVector.zero
  let some startGraph := (ed.source.bind fun p => (a.port p).owner).bind a.nodeGraph | return result
  let mut currentGraph := startGraph
  let mut guard := 0
  while currentGraph != targetGraph do
    guard := guard + 1
    if guard > 512 then break
    let some parentNode := (a.graph currentGraph).parentNode | break
    let parentPos := (a.node parentNode).position
    let some parentGraph := a.nodeGraph parentNode | break
    let pg := a.graph parentGraph
    result := ⟨result.x + (parentPos.x + pg.offset.x + pg.padding.left),
      result.y + (parentPos.y + pg.offset.y + pg.padding.top)⟩
    currentGraph := parentGraph
  return result

/-! ## Labels, ports, nodes -/

/-- Rust `apply_label_layout_with_size(llabel)`: copies size and position of a label whose
origin is an ElkLabel. -/
private def applyLabelLayoutWithSize (a : LGraphArena) (llabel : LLabelId) : ElkM Unit := do
  let lb := a.label llabel
  let some (.elkLabel labelId) := lb.internal.origin | return
  let some elkLabel ← elkLabelOf? labelId | return
  ElkM.modifyLabel elkLabel fun l =>
    { l with width := lb.size.x, height := lb.size.y, x := lb.position.x, y := lb.position.y }

/-- Rust `apply_port_layout(lport, apply_labels)`: position, size and `PORT_SIDE` of the
ElkPort, and the port labels when `applyLabels`. -/
private def applyPortLayout (a : LGraphArena) (lport : LPortId) (applyLabels : Bool) : ElkM Unit := do
  let pt := a.port lport
  let some (.elkPort portId) := pt.internal.origin | return
  let some elkPort ← elkPortOf? portId | return
  ElkM.modifyPort elkPort fun p =>
    { p with x := pt.position.x, y := pt.position.y, width := pt.size.x, height := pt.size.y,
             props := p.props.set CoreOptions.PORT_SIDE pt.side }
  if applyLabels then
    for l in pt.labels do
      applyLabelLayoutWithSize a l

/-- Rust `apply_node_layout(lnode, offset)` (Java `applyNodeLayout`): copies layer/position ids,
the offset position, the size (when the ElkNode has size constraints, a nested graph or a
flexible network-simplex size), the ports (with their labels unless the port label placement is
fixed) and the node labels (when the node or the label has a node label placement). -/
private def applyNodeLayout (a : LGraphArena) (lnode : LNodeId) (offset : KVector) : ElkM Unit := do
  let nd := a.node lnode
  let hasNestedGraph := nd.nestedGraph.isSome
  let nodeHasLabelPlacement := !(nd.props.getD LayeredOptions.NODE_LABELS_PLACEMENT EnumSet.noneOf).isEmpty
  let portLabelsAreFixed :=
    PortLabelPlacement.isFixed (nd.props.getD CoreOptions.PORT_LABELS_PLACEMENT PortLabelPlacement.outsideSet)
  let some (.elkNode nodeId) := nd.internal.origin | return
  let some elkNode ← elkNodeOf? nodeId | return
  let layerId := nd.props.getD LayeredOptions.LAYERING_LAYER_ID (-1)
  let positionId := nd.props.getD LayeredOptions.CROSSING_MINIMIZATION_POSITION_ID (-1)
  ElkM.modifyNode elkNode fun n =>
    let props := n.props.set LayeredOptions.CROSSING_MINIMIZATION_POSITION_ID positionId
    { n with props := props.set LayeredOptions.LAYERING_LAYER_ID layerId }
  let elkSizeConstraints := (← ElkM.getNode elkNode).props.getD LayeredOptions.NODE_SIZE_CONSTRAINTS EnumSet.noneOf
  ElkM.modifyNode elkNode fun n => { n with x := nd.position.x + offset.x, y := nd.position.y + offset.y }
  -- Java parity: node size when size constraints are non-empty, for nested graphs, or when the
  -- network-simplex node flexibility allows size adaptation
  let shouldSetSize := !elkSizeConstraints.isEmpty || hasNestedGraph || usesNetworkSimplexFlexibleSize a lnode
  if shouldSetSize then
    ElkM.modifyNode elkNode fun n => { n with width := nd.size.x, height := nd.size.y }
  for p in nd.ports do
    applyPortLayout a p !portLabelsAreFixed
  -- node label positions only when the node or the label has a label placement
  for l in nd.labels do
    let labelHasLabelPlacement := (a.label l).props.has LayeredOptions.NODE_LABELS_PLACEMENT
    if nodeHasLabelPlacement || labelHasLabelPlacement then
      applyLabelLayoutWithSize a l

/-! ## Edges -/

/-- The inline section handling of Rust `apply_edge_layout`, mirroring Java
`ElkGraphUtil.firstEdgeSection(elkedge, true, true)`: reuses the *first* section (keeping its
identifier and properties), clears its bend points and start/end points and drops (detaches)
all other sections; creates a section when the edge has none. -/
private def firstEdgeSection (e : EdgeId) : ElkM SectionId := do
  let sections := (← ElkM.getEdge e).sections
  match sections[0]? with
  | some first =>
    ElkM.modifySection first fun s =>
      { s with bendPoints := #[], startX := 0.0, startY := 0.0, endX := 0.0, endY := 0.0 }
    for s in sections.extract 1 sections.size do
      ElkM.modifySection s fun x => { x with parent := none }
    ElkM.modifyEdge e fun x => { x with sections := #[first] }
    return first
  | none => ElkM.createSection (some e)

/-- Rust `apply_edge_layout(ledge, origin_id, offset, edge_routing)` (Java `applyEdgeLayout`):
writes the bend point chain (source anchor, bend points, target anchor + `TARGET_OFFSET`, all
translated by the offset plus the hierarchical offset) into the first edge section, the edge
label geometry and `INCLUDE_LABEL`, the translated `JUNCTION_POINTS`, and `EDGE_ROUTING`
(`SPLINES` or removed). Edges with `INSIDE_SELF_LOOPS_YO` that already have a non-zero section
are left untouched. -/
private def applyEdgeLayout (a : LGraphArena) (ledge : LEdgeId) (originId : EdgeId) (offset : KVector)
    (edgeRouting : EdgeRouting) : ElkM Unit := do
  let ed := a.edge ledge
  let some elkEdge ← elkEdgeOf? originId | return
  if (← ElkM.getEdge elkEdge).props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false then
    let alreadyHasGeometry ← (do
      match (← ElkM.getEdge elkEdge).sections[0]? with
      | some s =>
        let sec ← ElkM.getSection s
        pure (sec.startX != 0.0 || sec.startY != 0.0 || sec.endX != 0.0 || sec.endY != 0.0)
      | none => pure false)
    if alreadyHasGeometry then return
  let hierarchicalOffset := calculateHierarchicalOffset a ledge
  let edgeOffset : KVector := ⟨offset.x + hierarchicalOffset.x, offset.y + hierarchicalOffset.y⟩
  let sourceNode := ed.source.bind fun p => (a.port p).owner
  let targetNode := ed.target.bind fun p => (a.port p).owner
  let sourceIsDescendantParent ← match targetNode, sourceNode with
    | some tn, some sn => isDescendant a tn sn
    | _, _ => pure false
  -- source point: for edges into the source's own nested graph, the port position + anchor
  -- relative to the node minus the offset (Java: `sourcePoint.sub(offset)`), else the absolute anchor
  let start : KVector :=
    if sourceIsDescendantParent then
      match ed.source with
      | some p =>
        let pt := a.port p
        ⟨pt.position.x + pt.anchor.x - offset.x, pt.position.y + pt.anchor.y - offset.y⟩
      | none => KVector.zero
    else (ed.source.bind a.portAbsoluteAnchor).getD KVector.zero
  let mut endPoint := (ed.target.bind a.portAbsoluteAnchor).getD KVector.zero
  if let some targetOffset := ed.internal.targetOffset then
    endPoint := ⟨endPoint.x + targetOffset.x, endPoint.y + targetOffset.y⟩
  let chain := ((ed.bendPoints.addFirst start).addLast endPoint).offsetValues edgeOffset.x edgeOffset.y
  let edge ← ElkM.getEdge elkEdge
  let incomingShape := firstShape edge.sources
  let outgoingShape := firstShape edge.targets
  let sec ← firstEdgeSection elkEdge
  ElkM.modifySection sec fun s => { s with incomingShape := incomingShape, outgoingShape := outgoingShape }
  ElkUtil.applyVectorChain chain sec
  -- edge labels: size, position + edge offset, `INCLUDE_LABEL`
  for l in ed.labels do
    let lb := a.label l
    let some (.elkLabel labelId) := lb.internal.origin | continue
    let some elkLabel ← elkLabelOf? labelId | continue
    let includeLabel := lb.props.get LabelDummySwitcher.INCLUDE_LABEL
    ElkM.modifyLabel elkLabel fun x =>
      { x with width := lb.size.x, height := lb.size.y,
               x := lb.position.x + edgeOffset.x, y := lb.position.y + edgeOffset.y,
               props := x.props.setOpt LabelDummySwitcher.INCLUDE_LABEL includeLabel }
  -- junction points (translated) or removed
  let junctionPoints := (ed.props.get LayeredOptions.JUNCTION_POINTS).map
    fun jp => jp.offsetValues edgeOffset.x edgeOffset.y
  ElkM.modifyEdge elkEdge fun x => { x with props := x.props.setOpt LayeredOptions.JUNCTION_POINTS junctionPoints }
  -- SPLINES means bend points are spline control points; otherwise the routing is removed
  ElkM.modifyEdge elkEdge fun x =>
    { x with props := if edgeRouting == .splines then x.props.set CoreOptions.EDGE_ROUTING .splines
                      else x.props.remove CoreOptions.EDGE_ROUTING }

/-! ## Fallback sections -/

/-- Rust `find_port_by_identifier(graph, identifier)`: breadth-first search from `graph`
(ports of a node before its children, children in order) for the first port with that
identifier. -/
private def findPortByIdentifier (g : ElkGraph) (graph : NodeId) (identifier : String) : Option PortId := Id.run do
  let mut queue : Array NodeId := #[graph]
  let mut head := 0
  while head < queue.size do
    let some n := queue[head]? | break
    head := head + 1
    let node := g.node n
    for p in node.ports do
      if (g.port p).identifier == some identifier then return some p
    queue := queue ++ node.children
  return none

/-- Rust `resolve_port_for_fallback(container, port)`: the first port below `container` with the
port's identifier, else the port itself. -/
private def resolvePortForFallback (g : ElkGraph) (container : NodeId) (port : PortId) : PortId :=
  match (g.port port).identifier with
  | some identifier => (findPortByIdentifier g container identifier).getD port
  | none => port

/-- Rust `fallback_anchor_for_port(port, container, container_abs)`: the middle of the port's
outer border (inner border for ports of the container itself) relative to the container; an
undefined `PORT_SIDE` is derived from the port position. `none` for ports without parent. -/
private def fallbackAnchorForPort (g : ElkGraph) (port : PortId) (container : NodeId) (containerAbs : KVector) :
    Option KVector :=
  let pt := g.port port
  match pt.parent with
  | none => none
  | some parent =>
    let side := pt.props.getD LayeredOptions.PORT_SIDE PortSide.undefined
    let nodeWidth := (g.node parent).width
    let side : PortSide :=
      if side == .undefined then
        if pt.x <= 0.0 then .west
        else if pt.x + pt.width >= nodeWidth then .east
        else if pt.y <= 0.0 then .north
        else .south
      else side
    let onContainer := parent == container
    let (anchorX, anchorY) : Float × Float := match side with
      | .west => (if onContainer then pt.x + pt.width else pt.x, pt.y + pt.height / 2.0)
      | .east => (if onContainer then pt.x else pt.x + pt.width, pt.y + pt.height / 2.0)
      | .north => (pt.x + pt.width / 2.0, if onContainer then pt.y + pt.height else pt.y)
      | .south => (pt.x + pt.width / 2.0, if onContainer then pt.y else pt.y + pt.height)
      | .undefined => (pt.x + pt.width / 2.0, pt.y + pt.height / 2.0)
    (ElkUtil.absolutePosition g (.node parent)).map fun parentAbs =>
      ⟨parentAbs.x + anchorX - containerAbs.x, parentAbs.y + anchorY - containerAbs.y⟩

/-- Rust `fallback_anchor_for_shape(shape, container, container_abs)`: ports via
`resolvePortForFallback` + `fallbackAnchorForPort`, nodes at their center, relative to the
container. -/
private def fallbackAnchorForShape (g : ElkGraph) (shape : Option ConnectableId) (container : NodeId)
    (containerAbs : KVector) : Option KVector :=
  match shape with
  | some (.port p) => fallbackAnchorForPort g (resolvePortForFallback g container p) container containerAbs
  | some (.node n) =>
    let node := g.node n
    (ElkUtil.absolutePosition g (.node n)).map fun nodeAbs =>
      ⟨nodeAbs.x + node.width / 2.0 - containerAbs.x, nodeAbs.y + node.height / 2.0 - containerAbs.y⟩
  | none => none

/-- Rust `apply_fallback_sections(elk_edges, container)`: every edge without a section that has
anchors at both ends gets a straight section from the first source to the first target. -/
private def applyFallbackSections (elkEdges : Array EdgeId) (container : NodeId) : ElkM Unit := do
  let containerAbs := (← ElkM.withGraph fun g => ElkUtil.absolutePosition g (.node container)).getD KVector.zero
  for e in elkEdges do
    let edge ← ElkM.getEdge e
    if !edge.sections.isEmpty then continue
    let incomingShape := firstShape edge.sources
    let outgoingShape := firstShape edge.targets
    let start ← ElkM.withGraph fun g => fallbackAnchorForShape g incomingShape container containerAbs
    let endPoint ← ElkM.withGraph fun g => fallbackAnchorForShape g outgoingShape container containerAbs
    let (some start, some endPoint) := (start, endPoint) | continue
    let sec ← ElkM.createSection (some e)
    ElkM.modifySection sec fun s => { s with incomingShape := incomingShape, outgoingShape := outgoingShape }
    ElkUtil.applyVectorChain #[start, endPoint] sec

/-- Rust `apply_fallback_sections_recursive(container)`: fallback sections for the contained
edges of `container`, then for each child (depth first). -/
private partial def applyFallbackSectionsRecursive (container : NodeId) : ElkM Unit := do
  let node ← ElkM.getNode container
  let edges := node.containedEdges
  let children := node.children
  applyFallbackSections edges container
  for child in children do
    applyFallbackSectionsRecursive child

/-! ## Graphs -/

/-- Rust `apply_parent_node_layout(lgraph)` (Java `applyParentNodeLayout`): for root graphs the
ElkNode is resized to the graph's actual size (with external ports: `PORT_CONSTRAINTS =
FIXED_POS` and ports not moved; otherwise only without `NODE_SIZE_FIXED_GRAPH_SIZE`); then the
size constraints are reset to `{PORT_LABELS}` (if they contained it) or fixed. -/
private def applyParentNodeLayout (a : LGraphArena) (elkGraph : NodeId) (lgraph : LGraphId) : ElkM Unit := do
  let some graphId := graphOrigin a elkGraph lgraph | return
  let some elkNode ← elkNodeOf? graphId | return
  let sizeConstraintsIncludedPortLabels :=
    ((← ElkM.getNode elkNode).props.getD LayeredOptions.NODE_SIZE_CONSTRAINTS SizeConstraint.fixed).contains .portLabels
  let gr := a.graph lgraph
  -- Java parity: only root graphs are resized; nested graphs were resized by the pipeline
  if gr.parentNode.isNone then
    let graphProps := gr.internal.graphProperties
    let actualGraphSize := gr.actualSize
    if graphProps.contains .externalPorts then
      ElkM.setNodeProp elkNode LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedPos
      discard <| ElkUtil.resizeNodeWith elkNode actualGraphSize.x actualGraphSize.y false true
    else
      let fixedGraphSize := (← ElkM.getNode elkNode).props.getD CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE false
      if !fixedGraphSize then
        discard <| ElkUtil.resizeNodeWith elkNode actualGraphSize.x actualGraphSize.y true true
  let constraints : EnumSet SizeConstraint :=
    if sizeConstraintsIncludedPortLabels then EnumSet.of #[.portLabels] else SizeConstraint.fixed
  ElkM.setNodeProp elkNode LayeredOptions.NODE_SIZE_CONSTRAINTS constraints

/-- Collects the edges of `ports` (outgoing edges in port order) whose target node satisfies
`keep` (edges without target node: `whenNoTarget`); the edge collection loops of Rust
`apply_layout`. -/
private def collectOutgoingEdges (a : LGraphArena) (ports : Array LPortId) (keep : LNodeId → IO Bool)
    (whenNoTarget : Bool) (edgeList : Array LEdgeId) : IO (Array LEdgeId) := do
  let mut edgeList := edgeList
  for port in ports do
    for edge in (a.port port).outgoingEdges do
      let includeEdge ← match (a.edge edge).target.bind fun p => (a.port p).owner with
        | some targetNode => keep targetNode
        | none => pure whenNoTarget
      if includeEdge then edgeList := edgeList.push edge
  return edgeList

/-- Rust `apply_layout(lgraph)` on the arena `a`; returns the arena with the external port
dummies moved by `LGraphUtil.getExternalPortPosition`. -/
private partial def applyLayoutImpl (a : LGraphArena) (elkGraph : NodeId) (lgraph : LGraphId) :
    ElkM LGraphArena := do
  -- offset (graph offset + padding left/top) and padding
  let gr := a.graph lgraph
  let padding := gr.padding
  let baseOffset : KVector := ⟨gr.offset.x + padding.left, gr.offset.y + padding.top⟩
  let some graphId := graphOrigin a elkGraph lgraph | return a
  let some elkNode ← elkNodeOf? graphId | return a
  -- content alignment for graphs enlarged by a minimum size
  let offset := applyContentAlignmentOffset a lgraph baseOffset
  -- computed padding
  let sizeOptions := (← ElkM.getNode elkNode).props.getD CoreOptions.NODE_SIZE_OPTIONS EnumSet.noneOf
  if sizeOptions.contains .computePadding then
    let elkPadding : ElkPadding :=
      { top := padding.top, right := padding.right, bottom := padding.bottom, left := padding.left }
    ElkM.setNodeProp elkNode CoreOptions.PADDING elkPadding
  -- nodes (layerless and layered) and the edges to process later
  let parentNode := gr.parentNode
  let allNodes := collectNodesFromGraph a lgraph
  let elkEdges := (← ElkM.getNode elkNode).containedEdges
  let mut a := a
  let mut edgeList : Array LEdgeId := #[]
  for lnode in allNodes do
    let nd := a.node lnode
    match nd.internal.origin with
    | some (.elkNode _) => applyNodeLayout a lnode offset
    | some (.elkPort portId) =>
      -- external port dummy on the top-most hierarchy level of the layout run
      if nd.type == .externalPort && parentNode.isNone then
        match ← elkPortOf? portId with
        | some elkPort =>
          let port ← ElkM.getPort elkPort
          let (portPos, a') ← LayeredM.run (LGraphUtil.getExternalPortPosition lgraph lnode port.width port.height) a
          a := a'
          ElkM.modifyPort elkPort fun p => { p with x := portPos.x, y := portPos.y }
        | none => pure ()
    | _ => pure ()
    -- edges, except those into a nested subgraph of this node (handled by the recursive call)
    let arena := a
    edgeList ← collectOutgoingEdges a (a.node lnode).ports
      (fun target => do return !(← isDescendant arena target lnode)) true edgeList
  -- edges from the representing node down into its descendants
  if let some parentLNode := parentNode then
    let arena := a
    edgeList ← collectOutgoingEdges a (a.node parentLNode).ports
      (fun target => isDescendant arena target parentLNode) false edgeList
  let edgeRouting := (← ElkM.getNode elkNode).props.getD LayeredOptions.EDGE_ROUTING EdgeRouting.undefined
  for edge in edgeList do
    let some (.elkEdge edgeId) := (a.edge edge).internal.origin | continue
    applyEdgeLayout a edge edgeId offset edgeRouting
  applyFallbackSections elkEdges elkNode
  applyParentNodeLayout a elkGraph lgraph
  -- nested subgraphs
  for node in allNodes do
    if let some nested := (a.node node).nestedGraph then
      a ← applyLayoutImpl a elkGraph nested
  -- every contained edge gets at least a fallback section
  applyFallbackSectionsRecursive elkNode
  return a

/-- `ElkGraphLayoutTransferrer.applyLayout(lgraph)` (Rust `apply_layout`): "Applies the layout
information contained in the given LGraph to the ElkGraph elements it was created from. All
source ElkGraph elements are expected to be accessible through their LGraph counterparts through
the `ORIGIN` property."

* `a`: the layered arena after layout (read-only; the external port dummy moves of
  `getExternalPortPosition` stay local).
* `_ledges`: the importer's `ElkEdge → LEdge` registry (Rust `OriginStore::register_ledge`);
  the Rust transferrer never calls `get_ledge`, so it is unused (kept for the transformer
  interface).
* `lgraph`: the root layered graph returned by the importer.
* `elkGraph`: the ElkNode `lgraph` was imported from (Rust `lgraph.ORIGIN`; nested graphs
  resolve their ElkNode through the origin of their representing `LNode`). -/
def applyLayout (a : LGraphArena) (_ledges : Std.HashMap Elk.Graph.EdgeId LEdgeId) (lgraph : LGraphId)
    (elkGraph : Elk.Graph.NodeId) : ElkM Unit := do
  discard <| applyLayoutImpl a elkGraph lgraph

end ElkGraphLayoutTransferrer

end Elk.Alg.Layered.Graph.Transform
