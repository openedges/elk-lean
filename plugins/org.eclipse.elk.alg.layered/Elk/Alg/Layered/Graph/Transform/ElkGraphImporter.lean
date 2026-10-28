import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Core.Util.ElkUtil
import Elk.Core.Util.Adapters.ElkGraphAdapters
import Elk.Alg.Common.NodeSpacing.Calculators.NodeLabelAndSizeCalculator
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Alg.Layered.Graph.Transform.IGraphTransformer
import Elk.Alg.Layered.Graph.Transform.ElkGraphLayoutTransferrer
/-!
# `org.eclipse.elk.alg.layered.graph.transform.ElkGraphImporter`

Port of elk-rs `graph/transform/elk_graph_importer.rs` (Java `ElkGraphImporter`): "Implements the
graph import aspect of `ElkGraphTransformer`." It turns an ElkGraph (`ElkM` state) into layered
graphs in the arena (`LayeredM` state), both inside `LImportM`.

State (Rust struct fields, kept in an `IO.Ref` so that `importGraph`/`applyLayout` take the
importer by value): `nodeMap : ElkNode → LNode`, `portMap : ElkPort → LPort` (external ports map
to the port of their dummy node), `labelMap`, the top-level ElkGraph/`LGraph`, and the shared
`OriginStore` (`ledges : ElkEdge → LEdge`). The Rust origin ids are the ElkGraph ids carried by
`Origin.elkNode/elkPort/elkEdge/elkLabel` (also on every `LGraph`: `LGraphInternals.origin`).

Internal properties are typed fields (`PORTING.md` §15): `ORIGIN` → `internal.origin`,
`COMPOUND_NODE`, `INSIDE_CONNECTIONS`, `GRAPH_PROPERTIES`, `MAX_MODEL_ORDER_NODES`,
`CB_NUM_MODEL_ORDER_GROUPS`, `COORDINATE_SYSTEM_ORIGIN`. `MODEL_ORDER` is stored on the ElkGraph
elements under its Java id `modelOrder` (`ELK_MODEL_ORDER`, as Rust/Java do) and moved into
`internal.modelOrder` when a node, port or edge is created; the key is removed from the copied
option map so that the typed field is the only copy.

elk-rs behaviour reproduced where it differs from Java (Rust is the oracle):
* `createLGraph` neither defaults `DIRECTION` nor installs a `LABEL_MANAGER`; the padding is
  `PADDING` + `computeInsideNodeLabelPadding(node, RIGHT)`. `SPACING_BASE_VALUE` is ignored
  (Java applies `LayeredSpacings.withBaseValue`). `RANDOM` is left to `GraphConfigurator`.
* `checkExternalPorts` also treats a root graph with ports and side-fixed `PORT_CONSTRAINTS` as
  having external ports.
* Hierarchical import is recursive: per level the children are transformed (a child's nested
  graph is imported right after its node, also for `INHERIT` hierarchy handling), then the level's
  edges with `importFlatGraphEdges`; model order indices, `MAX_MODEL_ORDER_NODES` and
  `CB_NUM_MODEL_ORDER_GROUPS` are per level. `NO_LAYOUT` children are skipped before they get a
  model order.
* The edge loop of one hierarchical level (`importFlatGraphEdges`) imports every contained edge
  whose end points are laid out; an edge into a node outside the layout scope throws (Java's
  `transformEdge` text, `throwEdgeEndNotFound`). Inside self loops of the graph itself are
  collected from the parent's edges. The flat import follows Java instead
  (`importFlatGraphEdgesJava`: only edges between children or between a child and the graph,
  hierarchy-crossing edges are left to no run without an error).
* `COMPOUND_NODE` on a node requires children or an actual inside self loop edge.
* `transformPort` marks `INSIDE_CONNECTIONS` via `ElkGraphAdapters.hasCompoundConnections`;
  `transformEdge` additionally marks the ports of descendant-connecting and inside self-loop edges.
* `transformEdge` checks Java's `checkEdgeValidity`, takes the first source/target, copies all options
  (junction points included) and sets `NO_LAYOUT = false`, creates node ports with
  `LGraphUtil.createPort(node, none, …)` (target ports in the target node's graph), lazily
  transforms ports missing from `portMap` (e.g. `NO_LAYOUT` ports), and does not import the
  original bend points.

ELK Java followed where elk-rs differs (ELK Java is the result reference):
* the flat import's edge selection (`importFlatGraphEdgesJava`) and the exception texts of
  `transformEdge` / `checkEdgeValidity` / `ElkGraphUtil.getSourceNode` (EMF `toString` of the edge);
* `calculateMinimumGraphSize`: the parent's `DIRECTION`, no fixed-port-label shortcut, and the
  aliasing of the ElkNode's own `NODE_SIZE_CONSTRAINTS` / `NODE_SIZE_MINIMUM` values.

Not ported: the `ElkTrace` diagnostics (`compound_width`, `import_port_order`,
`import_edge_selection`, `inside_yo`, `edge_origin_map`), which only print to stderr.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Layered.Graph.Transform

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Util.Adapters
open Elk.Alg.Common.NodeSpacing Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Components
open LayeredM

/-- The mutable part of the importer (Rust `ElkGraphImporter` fields). -/
structure ElkGraphImporterState where
  /-- Rust `node_map` (Java `nodeAndPortMap` for nodes). -/
  nodeMap : Std.HashMap NodeId LNodeId := {}
  /-- Rust `port_map` (external ports: the dummy's port). -/
  portMap : Std.HashMap PortId LPortId := {}
  /-- Rust `label_map`. -/
  labelMap : Std.HashMap LabelId LLabelId := {}
  /-- Rust `top_level_elkgraph`. -/
  topLevelElkGraph : Option NodeId := none
  /-- Rust `top_level_lgraph`. -/
  topLevelLGraph : Option LGraphId := none

/-- `ElkGraphImporter`: the importer state plus the (possibly shared) `OriginStore`. -/
structure ElkGraphImporter where
  state : IO.Ref ElkGraphImporterState
  /-- Rust `OriginStore::register_ledge` registry. -/
  ledges : IO.Ref OriginStore

namespace ElkGraphImporter

/-- `InternalProperties.MODEL_ORDER` (`modelOrder`) as stored on ElkGraph elements. -/
def ELK_MODEL_ORDER : Property Int := Property.mk' "modelOrder"

/-- `new ElkGraphImporter()` with a fresh origin store. -/
def new : IO ElkGraphImporter := do
  return { state := ← IO.mkRef {}, ledges := ← IO.mkRef {} }

/-- Rust `ElkGraphImporter::new(origin_store)`: an importer registering edges in `store`. -/
def withOriginStore (store : IO.Ref OriginStore) : IO ElkGraphImporter := do
  return { state := ← IO.mkRef {}, ledges := store }

/-! ## Small helpers -/

@[inline] private def elkNode (n : NodeId) : LImportM ElkNode := liftElk (ElkM.getNode n)
@[inline] private def elkPort (p : PortId) : LImportM ElkPort := liftElk (ElkM.getPort p)
@[inline] private def elkEdge (e : EdgeId) : LImportM ElkEdge := liftElk (ElkM.getEdge e)
@[inline] private def elkLabel (l : LabelId) : LImportM ElkLabel := liftElk (ElkM.getLabel l)
@[inline] private def withElk {α : Type} (f : ElkGraph → α) : LImportM α := liftElk (ElkM.withGraph f)

/-- The node of the first shape of an edge end list (`connectable_shape_to_node(shapes[0])`). -/
private def firstNode (g : ElkGraph) (shapes : Array ConnectableId) : Option NodeId :=
  shapes[0]?.bind (ElkGraphUtil.connectableShapeToNode g)

/-- EMF `ElkNodeImpl.toString()` / `ElkPortImpl.toString()`: `<kind>`, then ` "<identifier>"` (else
` "<first label text>"` when non-empty), then ` (x,y | width,height)` (Java `Double.toString`). -/
private def shapeJavaString (g : ElkGraph) (kind : String) (identifier : Option String) (labels : Array LabelId)
    (x y w h : Float) : String :=
  let name := match identifier with
    | some id => if id.isEmpty then none else some id
    | none => none
  let name := match name with
    | some n => some n
    | none => labels[0]?.bind fun l => let t := (g.label l).text; if t.isEmpty then none else some t
  let nameStr := match name with
    | some n => s!" \"{n}\""
    | none => ""
  s!"{kind}{nameStr} ({Float.toJavaString x},{Float.toJavaString y} | {Float.toJavaString w},{Float.toJavaString h})"

/-- `toString()` of an edge end (`ElkConnectableShape`). -/
private def connectableJavaString (g : ElkGraph) : ConnectableId → String
  | .node n => let nd := g.node n; shapeJavaString g "ElkNode" nd.identifier nd.labels nd.x nd.y nd.width nd.height
  | .port p => let pt := g.port p; shapeJavaString g "ElkPort" pt.identifier pt.labels pt.x pt.y pt.width pt.height

/-- EMF `ElkEdgeImpl.toString()`: `ElkEdge`, ` "<identifier>"` (else the first non-empty label
text), then the sources and targets joined by `, ` around ` -> ` (a hyperedge brackets both lists). -/
def elkEdgeJavaString (g : ElkGraph) (e : EdgeId) : String :=
  let edge := g.edge e
  let name := match edge.identifier with
    | some id => if id.isEmpty then none else some id
    | none => none
  let name := match name with
    | some n => some n
    | none => edge.labels[0]?.bind fun l => let t := (g.label l).text; if t.isEmpty then none else some t
  let nameStr := match name with
    | some n => s!" \"{n}\""
    | none => ""
  let hyperedge := !(edge.sources.size <= 1 && edge.targets.size <= 1)
  let srcs := ", ".intercalate (edge.sources.toList.map (connectableJavaString g))
  let tgts := ", ".intercalate (edge.targets.toList.map (connectableJavaString g))
  if hyperedge then s!"ElkEdge{nameStr} [{srcs}] -> [{tgts}]"
  else s!"ElkEdge{nameStr} {srcs} -> {tgts}"

/-- Java's `UnsupportedGraphException` of `transformEdge` when the source or the target of an edge
was not transformed (a `NO_LAYOUT` end node, or an end in a part of the hierarchy that another
layout run handles). -/
def throwEdgeEndNotFound {α : Type} (elkedge : EdgeId) : LImportM α := do
  let text ← withElk (elkEdgeJavaString · elkedge)
  throwUnsupportedGraph s!"The source or the target of edge {text} could not be found. This usually happens when an edge connects a node laid out by ELK Layered to a node in another level of hierarchy laid out by either another instance of ELK Layered or another layout algorithm alltogether. The former can be solved by setting the hierarchyHandling option to INCLUDE_CHILDREN."

/-- Java `checkEdgeValidity(edge)`: one source and one target (`UnsupportedGraphException`). -/
def checkEdgeValidity (elkedge : EdgeId) : LImportM Unit := do
  let edge ← elkEdge elkedge
  if edge.sources.isEmpty then throwUnsupportedGraph "Edges must have a source."
  else if edge.targets.isEmpty then throwUnsupportedGraph "Edges must have a target."
  else if !(edge.sources.size <= 1 && edge.targets.size <= 1) then throwUnsupportedGraph "Hyperedges are not supported."

/-- The `GRAPH_PROPERTIES` of an `LGraph`. -/
@[inline] private def graphProperties (lgraph : LGraphId) : LImportM (EnumSet GraphProperties) := do
  return (← getGraph lgraph).internal.graphProperties

/-- Sets the `GRAPH_PROPERTIES` of an `LGraph`. -/
@[inline] private def setGraphProperties (lgraph : LGraphId) (gp : EnumSet GraphProperties) : LImportM Unit :=
  modifyGraph lgraph fun g => { g with internal := { g.internal with graphProperties := gp } }

/-- Rust `node_for(node)`. -/
@[inline] private def nodeFor (imp : ElkGraphImporter) (n : NodeId) : LImportM (Option LNodeId) := do
  return (← imp.state.get).nodeMap.get? n

/-- Copy of an ElkGraph option map for a layered element (`copy_properties` into an empty map)
without the `modelOrder` key, which becomes the typed `internal.modelOrder`. -/
private def copyOptions (props : PropertyMap) : PropertyMap × Option Int :=
  ((({} : PropertyMap).copyFrom props).remove ELK_MODEL_ORDER, props.get? ELK_MODEL_ORDER)

/-! ## Model order -/

/-- Rust `needs_model_order_based_on_parent(elkgraph)`: model-order based cycle breaking,
layering or node promotion, or any model-order crossing minimization option. -/
def needsModelOrderBasedOnParent (props : PropertyMap) : Bool :=
  let cycleBreaking := props.get! LayeredOptions.CYCLE_BREAKING_STRATEGY
  let modelOrderCycleBreaking := match cycleBreaking with
    | .modelOrder | .bfsNodeOrder | .dfsNodeOrder | .greedyModelOrder | .sccConnectivity | .sccNodeType => true
    | _ => false
  let layering := props.get! LayeredOptions.LAYERING_STRATEGY
  let nodePromotion := props.get! LayeredOptions.LAYERING_NODE_PROMOTION_STRATEGY
  let modelOrderLayering := (match layering with
    | .bfModelOrder | .dfModelOrder => true
    | _ => false) || (match nodePromotion with
    | .modelOrderLeftToRight | .modelOrderRightToLeft => true
    | _ => false)
  let orderingStrategy := props.getD LayeredOptions.CONSIDER_MODEL_ORDER_STRATEGY OrderingStrategy.none
  let forceNodeModelOrder := props.getD LayeredOptions.CROSSING_MINIMIZATION_FORCE_NODE_MODEL_ORDER false
  let componentOrdering := props.getD LayeredOptions.CONSIDER_MODEL_ORDER_COMPONENTS ComponentOrderingStrategy.none
  let nodeInfluence := props.getD LayeredOptions.CONSIDER_MODEL_ORDER_CROSSING_COUNTER_NODE_INFLUENCE 0.0
  let portInfluence := props.getD LayeredOptions.CONSIDER_MODEL_ORDER_CROSSING_COUNTER_PORT_INFLUENCE 0.0
  let modelOrderCrossingMinimization := orderingStrategy != .none || forceNodeModelOrder ||
    componentOrdering != .none || nodeInfluence != 0.0 || portInfluence != 0.0
  modelOrderCycleBreaking || modelOrderLayering || modelOrderCrossingMinimization

/-- Rust `needs_model_order(child)`: the parent asks for model order and the child does not opt
out (`CONSIDER_MODEL_ORDER_NO_MODEL_ORDER`). -/
private def needsModelOrder (child : NodeId) : LImportM Bool := do
  let nd ← elkNode child
  match nd.parent with
  | none => return false
  | some parent =>
    let parentNeeds := needsModelOrderBasedOnParent (← elkNode parent).props
    return parentNeeds && !nd.props.getD LayeredOptions.CONSIDER_MODEL_ORDER_NO_MODEL_ORDER false

/-- Rust `set_element_model_order_for_node`. -/
private def setElementModelOrderForNode (n : NodeId) (modelOrder : Int) : LImportM Unit :=
  liftElk (ElkM.setNodeProp n ELK_MODEL_ORDER modelOrder)

/-- Rust `set_element_model_order_for_edge`. -/
private def setElementModelOrderForEdge (e : EdgeId) (modelOrder : Int) : LImportM Unit :=
  liftElk (ElkM.modifyEdge e fun x => { x with props := x.props.set ELK_MODEL_ORDER modelOrder })

/-- Rust `set_element_model_order_for_port`. -/
private def setElementModelOrderForPort (p : PortId) (modelOrder : Int) : LImportM Unit :=
  liftElk (ElkM.modifyPort p fun x => { x with props := x.props.set ELK_MODEL_ORDER modelOrder })

/-! ## Pure ElkGraph queries -/

/-- Rust `has_inside_self_loop_edge(node)` (Java `hasInsideSelfLoops`): inside self loops are
activated on the node and one of its outgoing edges is a self loop with `INSIDE_SELF_LOOPS_YO`. -/
def hasInsideSelfLoopEdge (g : ElkGraph) (node : NodeId) : Bool := Id.run do
  if !(g.node node).props.getD CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false then return false
  for e in ElkGraphUtil.allOutgoingEdges g node do
    if !ElkGraphUtil.isSelfloop g e then continue
    if (g.edge e).props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false then return true
  return false

/-- Rust `calculate_external_port_net_flow(elkport)` (Java `calculateNetFlow`): outgoing minus
incoming votes (edges into the graph's children count as input, inside self loops reversed).
`none` for a port without parent node (Rust `expect` panics). -/
def calculateExternalPortNetFlow (g : ElkGraph) (elkport : PortId) : Option Int := Id.run do
  let pt := g.port elkport
  let some elkgraph := pt.parent | return none
  let insideSelfLoopsEnabled := (g.node elkgraph).props.getD CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false
  let mut outputPortVote : Int := 0
  let mut inputPortVote : Int := 0
  for e in pt.outgoingEdges do
    let edge := g.edge e
    let isSelfLoop := ElkGraphUtil.isSelfloop g e
    let insideLoop := edge.props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false
    let isInsideSelfLoop := isSelfLoop && insideSelfLoopsEnabled && insideLoop
    if isSelfLoop && isInsideSelfLoop then inputPortVote := inputPortVote + 1
    else if isSelfLoop && !isInsideSelfLoop then outputPortVote := outputPortVote + 1
    else
      match firstNode g edge.targets with
      | some targetNode =>
        if (g.node targetNode).parent == some elkgraph || targetNode == elkgraph then
          inputPortVote := inputPortVote + 1
        else outputPortVote := outputPortVote + 1
      | none => outputPortVote := outputPortVote + 1
  for e in pt.incomingEdges do
    let edge := g.edge e
    let isSelfLoop := ElkGraphUtil.isSelfloop g e
    let insideLoop := edge.props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false
    let isInsideSelfLoop := isSelfLoop && insideSelfLoopsEnabled && insideLoop
    if isSelfLoop && isInsideSelfLoop then outputPortVote := outputPortVote + 1
    else if isSelfLoop && !isInsideSelfLoop then inputPortVote := inputPortVote + 1
    else
      match firstNode g edge.sources with
      | some sourceNode =>
        if (g.node sourceNode).parent == some elkgraph || sourceNode == elkgraph then
          outputPortVote := outputPortVote + 1
        else inputPortVote := inputPortVote + 1
      | none => inputPortVote := inputPortVote + 1
  return some (outputPortVote - inputPortVote)

/-- Rust `is_connected_to_external_nodes(elkport)`: an edge of the port leads to a node that is
not a descendant of the port's node. `none` for a port without parent node. -/
def isConnectedToExternalNodes (g : ElkGraph) (elkport : PortId) : Option Bool := Id.run do
  let pt := g.port elkport
  let some parent := pt.parent | return none
  for e in pt.outgoingEdges do
    if let some targetNode := firstNode g (g.edge e).targets then
      if !ElkGraphUtil.isDescendant g targetNode parent then return some true
  for e in pt.incomingEdges do
    if let some sourceNode := firstNode g (g.edge e).sources then
      if !ElkGraphUtil.isDescendant g sourceNode parent then return some true
  return some false

/-- The number of edges of `port` that make it an external port of `elkgraph` (inside self loops
and edges to children), counting stops at 2 (Rust `check_external_ports` inner loop). -/
private def externalPortEdgeCount (g : ElkGraph) (elkgraph : NodeId) (enableSelfLoops : Bool) (port : PortId) : Nat := Id.run do
  let mut externalPortEdges := 0
  for e in ElkGraphUtil.allIncidentEdgesForShape g (.port port) do
    let edge := g.edge e
    let portIsSource := edge.sources.any (· == .port port)
    let portIsTarget := edge.targets.any (· == .port port)
    let isSelfLoop := ElkGraphUtil.isSelfloop g e
    let insideLoop := edge.props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false
    let isInsideSelfLoop := enableSelfLoops && isSelfLoop && insideLoop
    let connectsToChild :=
      if portIsSource then
        ((firstNode g edge.targets).bind fun n => (g.node n).parent) == some elkgraph
      else if portIsTarget then
        ((firstNode g edge.sources).bind fun n => (g.node n).parent) == some elkgraph
      else false
    if isInsideSelfLoop || connectsToChild then
      externalPortEdges := externalPortEdges + 1
      if externalPortEdges > 1 then break
  return externalPortEdges

/-- Rust `check_external_ports(elkgraph, graph_properties)`: `EXTERNAL_PORTS` if a port has an
edge to a child or an inside self loop (or, with inside port labels, a label), `HYPEREDGES` if a
port has more than one such edge; a root graph with ports and side-fixed `PORT_CONSTRAINTS` also
has external ports (elk-rs addition). -/
def checkExternalPorts (g : ElkGraph) (elkgraph : NodeId) (graphProperties : EnumSet GraphProperties) :
    EnumSet GraphProperties := Id.run do
  let nd := g.node elkgraph
  let enableSelfLoops := nd.props.getD CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false
  let portLabelPlacement := nd.props.getD CoreOptions.PORT_LABELS_PLACEMENT PortLabelPlacement.outsideSet
  let mut hasExternalPorts := false
  let mut hasHyperedges := false
  for port in nd.ports do
    if hasExternalPorts && hasHyperedges then break
    let externalPortEdges := externalPortEdgeCount g elkgraph enableSelfLoops port
    if externalPortEdges > 0 then hasExternalPorts := true
    else if portLabelPlacement.contains .inside && !(g.port port).labels.isEmpty then
      hasExternalPorts := true
    if externalPortEdges > 1 then hasHyperedges := true
  -- edgeless ports of a root graph with side-fixed port constraints are external ports too
  if nd.parent.isNone && !hasExternalPorts && !nd.ports.isEmpty then
    if (nd.props.getD CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined).isSideFixed then
      hasExternalPorts := true
  let mut result := graphProperties
  if hasExternalPorts then result := result.insert .externalPorts
  if hasHyperedges then result := result.insert .hyperedges
  return result

/-- Rust `find_coordinate_system_origin(elkedge, top_level_elkgraph, top_level_lgraph)`: the
`LGraph` the edge coordinates must be made relative to on export, `none` when the edge's
containment in ELK Layered matches the ElkGraph containment. -/
private def findCoordinateSystemOrigin (imp : ElkGraphImporter) (elkedge : EdgeId) (topLevelElkGraph : NodeId)
    (topLevelLGraph : LGraphId) : LImportM (Option LGraphId) := do
  let edge ← elkEdge elkedge
  let some source ← withElk (firstNode · edge.sources) | return none
  let some target ← withElk (firstNode · edge.targets) | return none
  let sourceParent := (← elkNode source).parent
  let targetParent := (← elkNode target).parent
  match sourceParent, targetParent with
  | some sp, some tp => if sp == tp then return none
  | none, none => return none
  | _, _ => pure ()
  if ← withElk (ElkGraphUtil.isDescendant · target source) then return none
  let some origin := edge.containingNode | return none
  if origin == topLevelElkGraph then return some topLevelLGraph
  let some lnode ← nodeFor imp origin | return none
  return (← getNode lnode).nestedGraph

/-! ## Graph creation -/

/-- Rust `create_lgraph(elkgraph)` (Java `createLGraph`): a new `LGraph` with the ElkNode's options,
padding `PADDING + computeInsideNodeLabelPadding(node, RIGHT)`, `ORIGIN` and empty
`GRAPH_PROPERTIES`. -/
def createLGraph (elkgraph : NodeId) : LImportM LGraphId := do
  let adapters ← ElkGraphAdapters.adaptSingleNode elkgraph
  let nodeLabelPadding ← liftElk (NodeLabelAndSizeCalculator.computeInsideNodeLabelPadding adapters elkgraph .right)
  let props := (← elkNode elkgraph).props
  let padding := props.getD CoreOptions.PADDING {}
  LayeredM.createGraph {
    props := ({} : PropertyMap).copyFrom props
    padding := { top := padding.top + nodeLabelPadding.top, right := padding.right + nodeLabelPadding.right,
                 bottom := padding.bottom + nodeLabelPadding.bottom, left := padding.left + nodeLabelPadding.left }
    internal := { origin := some (.elkNode elkgraph), graphProperties := EnumSet.noneOf } }

/-- Rust `should_calculate_minimum_graph_size(elkgraph)`: the node has size constraints. -/
private def shouldCalculateMinimumGraphSize (elkgraph : NodeId) : LImportM Bool := do
  return !((← elkNode elkgraph).props.getD LayeredOptions.NODE_SIZE_CONSTRAINTS EnumSet.noneOf).isEmpty

/-- Java `calculateMinimumGraphSize(elkgraph, lgraph)` (Rust `calculate_minimum_graph_size`): for a
non-root graph with size constraints, `UNDEFINED` port constraints of the ElkNode become `FREE` and
`NodeLabelAndSizeCalculator.process(adapt(parent), adaptSingleNode(elkgraph), false, true)` computes
(without applying anything, ignoring inside port labels) the minimum size; it is merged into
`NODE_SIZE_MINIMUM` (`Math.max`) and `MINIMUM_SIZE` is added to the size constraints.

Java details reproduced (ELK Java is the result reference; elk-rs differs in all three):
* the label cells are laid out for the parent graph's `DIRECTION` when the parent ElkNode has one
  (`process` reads `graph.getProperty(DIRECTION)` only if `graph.hasProperty(DIRECTION)`), else
  horizontally — not for the node's own direction;
* there is no early return for fixed port label placements;
* `lgraph.copyProperties(elkgraph)` shares the value objects, so the `EnumSet` that gets
  `MINIMUM_SIZE` and the `KVector` that gets the minimum are the ElkNode's own when it sets
  `NODE_SIZE_CONSTRAINTS` / `NODE_SIZE_MINIMUM` explicitly: both are written back to the ElkNode,
  and every `LNode` later imported from it (the compound node in the parent graph, or the node in
  the parent's own layout run after a separate child layout) sees them. Without an explicit
  `NODE_SIZE_MINIMUM` Java stores a fresh default copy on the `LGraph` only. -/
def calculateMinimumGraphSize (elkgraph : NodeId) (lgraph : LGraphId) : LImportM Unit := do
  let some parent := (← elkNode elkgraph).parent | return
  let mut sizeConstraints := (← getGraph lgraph).props.getD LayeredOptions.NODE_SIZE_CONSTRAINTS EnumSet.noneOf
  if sizeConstraints.isEmpty then return
  if (← elkNode elkgraph).props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined == .undefined then
    liftElk (ElkM.setNodeProp elkgraph LayeredOptions.PORT_CONSTRAINTS PortConstraints.free)
  let mut minSize := (← getGraph lgraph).props.getD LayeredOptions.NODE_SIZE_MINIMUM KVector.zero
  -- Java: NodeLabelAndSizeCalculator.process(adapt(parent), adaptSingleNode(elkgraph), false, true),
  -- i.e. compute-only and ignoring inside port labels; the label cells follow the parent's DIRECTION
  let parentProps := (← elkNode parent).props
  let layoutDirection := if parentProps.has CoreOptions.DIRECTION then
      parentProps.getD CoreOptions.DIRECTION Direction.undefined
    else Direction.undefined
  let adapters ← ElkGraphAdapters.adaptSingleNode elkgraph
  let calculatedMin ← liftElk (NodeLabelAndSizeCalculator.processWithOptions adapters elkgraph layoutDirection false true)
  minSize := ⟨javaMax calculatedMin.x minSize.x, javaMax calculatedMin.y minSize.y⟩
  sizeConstraints := sizeConstraints.insert .minimumSize
  let finalConstraints := sizeConstraints
  let finalMinSize := minSize
  modifyGraph lgraph fun g => { g with
    props := (g.props.set LayeredOptions.NODE_SIZE_CONSTRAINTS finalConstraints).set LayeredOptions.NODE_SIZE_MINIMUM finalMinSize }
  -- Java's aliasing: the ElkNode's own EnumSet / KVector were mutated
  let nodeProps := (← elkNode elkgraph).props
  if nodeProps.has LayeredOptions.NODE_SIZE_CONSTRAINTS then
    liftElk (ElkM.setNodeProp elkgraph LayeredOptions.NODE_SIZE_CONSTRAINTS finalConstraints)
  if nodeProps.has LayeredOptions.NODE_SIZE_MINIMUM then
    liftElk (ElkM.setNodeProp elkgraph LayeredOptions.NODE_SIZE_MINIMUM finalMinSize)

/-! ## External port sides -/

/-- Rust `ensure_defined_port_side(lgraph, elkport)` (Java `ensureDefinedPortSide`): without
side-fixed port constraints the side follows the net flow (positive: the layout direction's side,
else the opposite); otherwise an undefined side is computed from the position (falling back to the
layout direction's side). The side is stored as the ElkPort's `PORT_SIDE`. -/
def ensureDefinedPortSide (lgraph : LGraphId) (elkport : PortId) : LImportM Unit := do
  let direction ← LGraphUtil.getDirection lgraph
  let portConstraints := (← getGraph lgraph).props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  let mut portSide := (← elkPort elkport).props.getD LayeredOptions.PORT_SIDE PortSide.undefined
  if !portConstraints.isSideFixed then
    let some netFlow ← withElk (calculateExternalPortNetFlow · elkport)
      | throwIllegalState "port must have a parent node"
    portSide := if netFlow > 0 then PortSide.fromDirection direction else (PortSide.fromDirection direction).opposed
  else if portSide == .undefined then
    let calculated ← withElk (ElkUtil.calcPortSide · elkport direction)
    portSide := if calculated != .undefined then calculated else PortSide.fromDirection direction
  let side := portSide
  liftElk (ElkM.modifyPort elkport fun p => { p with props := p.props.set LayeredOptions.PORT_SIDE side })

/-! ## Labels, ports, nodes -/

/-- Rust `transform_label(elklabel)` (Java `transformLabel`): an `LLabel` with the text, options,
position, size and `ORIGIN` of the ElkLabel. -/
def transformLabel (imp : ElkGraphImporter) (elklabel : LabelId) : LImportM LLabelId := do
  let lb ← elkLabel elklabel
  let llabel ← LayeredM.createLabel lb.text {
    props := ({} : PropertyMap).copyFrom lb.props
    position := ⟨lb.x, lb.y⟩
    size := ⟨lb.width, lb.height⟩
    internal := { origin := some (.elkLabel elklabel) } }
  imp.state.modify fun s => { s with labelMap := s.labelMap.insert elklabel llabel }
  return llabel

/-- Whether an ElkLabel is imported: not `NO_LAYOUT` and with a non-empty text. -/
private def isImportedLabel (l : LabelId) : LImportM Bool := do
  let lb ← elkLabel l
  return !(lb.props.getD CoreOptions.NO_LAYOUT false) && !lb.text.isEmpty

/-- `NORTH_SOUTH_PORTS` if the port side is not on the layout direction's axis. -/
private def northSouthPortProperty (gp : EnumSet GraphProperties) (layoutDirection : Direction) (side : PortSide) :
    EnumSet GraphProperties :=
  match layoutDirection with
  | .left | .right => if side == .north || side == .south then gp.insert .northSouthPorts else gp
  | .up | .down => if side == .east || side == .west then gp.insert .northSouthPorts else gp
  | .undefined => gp

/-- Rust `transform_port(elkport, lnode, graph_properties, layout_direction, port_constraints)`
(Java `transformPort`): a port of `lnode` with the ElkPort's options, position, size, side and
`ORIGIN`, `INSIDE_CONNECTIONS` from `ElkGraphAdapters.hasCompoundConnections`, initialised with
`LGraphUtil.initializePort` (anchor: `PORT_ANCHOR`), registered in `portMap`, and its labels.
Returns the updated graph properties (`NORTH_SOUTH_PORTS`) and the port. -/
def transformPort (imp : ElkGraphImporter) (elkport : PortId) (lnode : LNodeId) (gp : EnumSet GraphProperties)
    (layoutDirection : Direction) (portConstraints : PortConstraints) : LImportM (EnumSet GraphProperties × LPortId) := do
  let lport ← LayeredM.createPort
  setPortNode lport (some lnode)
  let pt ← elkPort elkport
  let (props, modelOrder) := copyOptions pt.props
  let anchor := pt.props.get CoreOptions.PORT_ANCHOR
  -- Java parity: non-external ports keep the model-provided side (possibly UNDEFINED)
  let portSide := pt.props.getD LayeredOptions.PORT_SIDE PortSide.undefined
  let insideConnections ← liftElk (ElkGraphAdapters.hasCompoundConnections elkport)
  modifyPort lport fun p =>
    let p := { p with props := props, position := ⟨pt.x, pt.y⟩, size := ⟨pt.width, pt.height⟩ }
    let p := p.setSide portSide
    { p with internal := { p.internal with
        origin := some (.elkPort elkport), insideConnections := insideConnections, modelOrder := modelOrder } }
  LGraphUtil.initializePort lport portConstraints layoutDirection anchor
  let gp := northSouthPortProperty gp layoutDirection (← getPort lport).side
  imp.state.modify fun s => { s with portMap := s.portMap.insert elkport lport }
  for label in pt.labels do
    if !(← isImportedLabel label) then continue
    let llabel ← transformLabel imp label
    modifyPort lport fun p => { p with labels := p.labels.push llabel }
  return (gp, lport)

/-- The node's `PORT_CONSTRAINTS` with `UNDEFINED` replaced by `FREE` (stored), and `NON_FREE_PORTS`
for constraints other than `FREE` (the shared prologue of Rust `transform_node`/`resolve_port`). -/
private def normalizePortConstraints (lnode : LNodeId) (gp : EnumSet GraphProperties) :
    LImportM (PortConstraints × EnumSet GraphProperties) := do
  let portConstraints := (← getNode lnode).props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  if portConstraints == .undefined then
    setNodeProp lnode LayeredOptions.PORT_CONSTRAINTS PortConstraints.free
    return (.free, gp)
  else if portConstraints != .free then
    return (portConstraints, gp.insert .nonFreePorts)
  else return (portConstraints, gp)

/-- Rust `transform_node(elknode, lgraph)` (Java `transformNode`): a layerless node of `lgraph`
with the ElkNode's options (`PARTITIONING_PARTITION` re-stored typed), position, size, `ORIGIN`,
`COMPOUND_NODE` (children or inside self loops), `modelOrder`; its ports (port model order by index
when needed, `NO_LAYOUT` ports skipped), labels, and the graph properties `NON_FREE_PORTS`,
`COMMENTS`, `HYPERNODES`/`HYPEREDGES` (hypernodes get `FREE` port constraints). -/
def transformNode (imp : ElkGraphImporter) (elknode : NodeId) (lgraph : LGraphId) : LImportM LNodeId := do
  let nd ← elkNode elknode
  let isHierarchical := nd.isHierarchical || (← withElk (hasInsideSelfLoopEdge · elknode))
  let (props, modelOrder) := copyOptions nd.props
  -- explicitly transfer PARTITIONING_PARTITION with the correct type
  let props := match nd.props.get CoreOptions.PARTITIONING_PARTITION with
    | some partition => props.set CoreOptions.PARTITIONING_PARTITION partition
    | none => props
  let lnode ← LayeredM.createNode lgraph {
    props := props
    position := ⟨nd.x, nd.y⟩
    size := ⟨nd.width, nd.height⟩
    internal := { origin := some (.elkNode elknode), compoundNode := isHierarchical, modelOrder := modelOrder } }
  modifyGraph lgraph fun g => { g with layerlessNodes := g.layerlessNodes.push lnode }
  imp.state.modify fun s => { s with nodeMap := s.nodeMap.insert elknode lnode }
  let direction ← LGraphUtil.getDirection lgraph
  let (portConstraints, gp) ← normalizePortConstraints lnode (← graphProperties lgraph)
  let mut gp := gp
  let assignPortModelOrder ← needsModelOrder elknode
  for h : portIndex in [0:nd.ports.size] do
    let port := nd.ports[portIndex]
    if assignPortModelOrder then setElementModelOrderForPort port portIndex
    if (← elkPort port).props.getD CoreOptions.NO_LAYOUT false then continue
    let (gp', _) ← transformPort imp port lnode gp direction portConstraints
    gp := gp'
  for label in nd.labels do
    if !(← isImportedLabel label) then continue
    let llabel ← transformLabel imp label
    modifyNode lnode fun n => { n with labels := n.labels.push llabel }
  if (← getNode lnode).props.getD LayeredOptions.COMMENT_BOX false then
    gp := gp.insert .comments
  if (← getNode lnode).props.getD LayeredOptions.HYPERNODE false then
    gp := (gp.insert .hypernodes).insert .hyperedges
    setNodeProp lnode LayeredOptions.PORT_CONSTRAINTS PortConstraints.free
  setGraphProperties lgraph gp
  return lnode

/-! ## Edges -/

/-- Rust `resolve_port(shape, port_type, lgraph)`: the `LPort` for an edge end point. Ports come
from `portMap` or are transformed on demand when their node is known (graph properties of
`lgraph` updated); nodes get a new port from `LGraphUtil.createPort(node, none, type, graph)`
(target ports in the target node's graph). `none` when the end point is outside the scope. -/
def resolvePort (imp : ElkGraphImporter) (shape : ConnectableId) (portType : PortType) (lgraph : LGraphId) :
    LImportM (Option LPortId) := do
  match shape with
  | .port port =>
    if let some existing := (← imp.state.get).portMap.get? port then return some existing
    let some parent := (← elkPort port).parent | return none
    let some lnode ← nodeFor imp parent | return none
    let direction ← LGraphUtil.getDirection lgraph
    let (portConstraints, gp) ← normalizePortConstraints lnode (← graphProperties lgraph)
    let (gp, result) ← transformPort imp port lnode gp direction portConstraints
    setGraphProperties lgraph gp
    return some result
  | .node node =>
    let some lnode ← nodeFor imp node | return none
    -- Java parity: source ports in the edge's graph, target ports in the target node's graph
    let graphForPort ← if portType == .input then do pure ((← nodeGraph lnode).getD lgraph) else pure lgraph
    return some (← LGraphUtil.createPort lnode none portType graphForPort)

/-- `INSIDE_CONNECTIONS` for the end ports of an edge into the source's descendants (source port)
or from the target's descendants (target port), and for inside self loops (both). -/
private def markInsideConnections (sourceShape targetShape : ConnectableId) (insideSelfLoops : Bool)
    (sourcePort targetPort : LPortId) : LImportM Unit := do
  let some sourceNode ← withElk (ElkGraphUtil.connectableShapeToNode · sourceShape) | return
  let some targetNode ← withElk (ElkGraphUtil.connectableShapeToNode · targetShape) | return
  let sourceInside := (← withElk (ElkGraphUtil.isDescendant · targetNode sourceNode)) ||
    (insideSelfLoops && targetNode == sourceNode)
  let targetInside := (← withElk (ElkGraphUtil.isDescendant · sourceNode targetNode)) ||
    (insideSelfLoops && sourceNode == targetNode)
  if sourceInside then
    modifyPort sourcePort fun p => { p with internal := { p.internal with insideConnections := true } }
  if targetInside then
    modifyPort targetPort fun p => { p with internal := { p.internal with insideConnections := true } }

/-- The edge labels of Rust `transform_edge`: imported labels are added to the edge; `HEAD`/`TAIL`
placements add `END_LABELS`, `CENTER` adds `CENTER_LABELS` and is stored explicitly. -/
private def transformEdgeLabels (imp : ElkGraphImporter) (labels : Array LabelId) (ledge : LEdgeId)
    (gp : EnumSet GraphProperties) : LImportM (EnumSet GraphProperties) := do
  let mut gp := gp
  for label in labels do
    if !(← isImportedLabel label) then continue
    let llabel ← transformLabel imp label
    match (← getLabel llabel).props.getD LayeredOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.center with
    | .head | .tail => gp := gp.insert .endLabels
    | .center =>
      gp := gp.insert .centerLabels
      setLabelProp llabel LayeredOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.center
    modifyEdge ledge fun e => { e with labels := e.labels.push llabel }
  return gp

/-- Rust `transform_edge(elkedge, lgraph)` (Java `transformEdge`): an `LEdge` between the resolved
end ports (first source, first target; edges without one are skipped) with the edge's options
(`NO_LAYOUT = false`), `ORIGIN`, registered in the origin store, its labels and
`COORDINATE_SYSTEM_ORIGIN`; updates `SELF_LOOPS`, `HYPEREDGES`, `END_LABELS`, `CENTER_LABELS` of
`lgraph`. Throws `UnsupportedGraphException` when an end point is outside the layout scope. -/
def transformEdge (imp : ElkGraphImporter) (elkedge : EdgeId) (lgraph : LGraphId) : LImportM Unit := do
  checkEdgeValidity elkedge
  let edge ← elkEdge elkedge
  let some sourceShape := edge.sources[0]? | return
  let some targetShape := edge.targets[0]? | return
  -- Java throws one exception for a missing source or target (elk-rs: two messages naming the edge id)
  let some sourcePort ← resolvePort imp sourceShape .output lgraph | throwEdgeEndNotFound elkedge
  let some targetPort ← resolvePort imp targetShape .input lgraph | throwEdgeEndNotFound elkedge
  let insideSelfLoops := edge.props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false
  markInsideConnections sourceShape targetShape insideSelfLoops sourcePort targetPort
  let ledge ← LayeredM.createEdge
  setEdgeSource ledge (some sourcePort)
  setEdgeTarget ledge (some targetPort)
  let mut gp ← graphProperties lgraph
  -- Java parity: self loops and hyperedges are tracked while importing edges
  if (← get).edgeIsSelfLoop ledge then gp := gp.insert .selfLoops
  let sp ← getPort sourcePort
  let tp ← getPort targetPort
  if sp.incomingEdges.size > 1 || sp.outgoingEdges.size > 1 || tp.incomingEdges.size > 1 || tp.outgoingEdges.size > 1 then
    gp := gp.insert .hyperedges
  let (props, modelOrder) := copyOptions edge.props
  modifyEdge ledge fun e => { e with
    props := props.set CoreOptions.NO_LAYOUT false
    internal := { e.internal with origin := some (.elkEdge elkedge), modelOrder := modelOrder } }
  imp.ledges.modify fun m => m.insert elkedge ledge
  gp ← transformEdgeLabels imp edge.labels ledge gp
  let st ← imp.state.get
  if let (some topLevelElkGraph, some topLevelLGraph) := (st.topLevelElkGraph, st.topLevelLGraph) then
    let coordOrigin ← findCoordinateSystemOrigin imp elkedge topLevelElkGraph topLevelLGraph
    modifyEdge ledge fun e => { e with internal := { e.internal with coordinateSystemOrigin := coordOrigin } }
  setGraphProperties lgraph gp

/-! ## External ports -/

/-- The external port dummy's labels (Rust `transform_external_port` label loop): imported labels
are added to the dummy port; unless the graph places port labels inside, their width (east/west)
or height (north/south) becomes the part inside the node for fixed port labels, else `0`. -/
private def transformExternalPortLabels (imp : ElkGraphImporter) (labels : Array LabelId) (dummyPort : Option LPortId)
    (portSize : KVector) (portSide : PortSide) (insidePortLabels portLabelsFixed : Bool) : LImportM Unit := do
  for label in labels do
    let lb ← elkLabel label
    if lb.props.getD CoreOptions.NO_LAYOUT false || lb.text.isEmpty then continue
    let llabel ← transformLabel imp label
    if let some dp := dummyPort then
      modifyPort dp fun p => { p with labels := p.labels.push llabel }
    if !insidePortLabels then
      let insidePart :=
        if portLabelsFixed then ElkUtil.computeInsidePart ⟨lb.x, lb.y⟩ ⟨lb.width, lb.height⟩ portSize fl0p0 portSide
        else fl0p0
      modifyLabel llabel fun l =>
        match portSide with
        | .east | .west => { l with size := { l.size with x := insidePart } }
        | .north | .south => { l with size := { l.size with y := insidePart } }
        | .undefined => l

/-- Rust `transform_external_port(elkgraph, lgraph, elkport)` (Java `transformExternalPort`): the
external port dummy (`LGraphUtil.createExternalPortDummy`; a missing `PORT_BORDER_OFFSET` is
inferred and stored on the ElkPort, as is a side chosen by the dummy creation) with `ORIGIN`,
outside port labels, `connectedToExternalNodes`, the port labels and the parent's label spacings;
added to `lgraph` and registered as the port's `LPort`. -/
def transformExternalPort (imp : ElkGraphImporter) (elkgraph : NodeId) (lgraph : LGraphId) (elkport : PortId) :
    LImportM Unit := do
  let port ← elkPort elkport
  let portSide := port.props.getD LayeredOptions.PORT_SIDE PortSide.undefined
  let portPosition : KVector := ⟨port.x + port.width / fl2p0, port.y + port.height / fl2p0⟩
  let portSize : KVector := ⟨port.width, port.height⟩
  let some netFlow ← withElk (calculateExternalPortNetFlow · elkport)
    | throwIllegalState "port must have a parent node"
  let graphNode ← elkNode elkgraph
  let portConstraints := graphNode.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  let layoutDirection ← LGraphUtil.getDirection lgraph
  let graphSize : KVector := ⟨graphNode.width, graphNode.height⟩
  if !port.props.has LayeredOptions.PORT_BORDER_OFFSET then
    -- port coordinates (0, 0) default to offset 0 to make the common case frustration-free
    let portBorderOffset ← if port.x == fl0p0 && port.y == fl0p0 then pure fl0p0
      else withElk (ElkUtil.calcPortOffset · elkport portSide)
    liftElk (ElkM.modifyPort elkport fun p => { p with props := p.props.set LayeredOptions.PORT_BORDER_OFFSET portBorderOffset })
  let holder := (← elkPort elkport).props
  let (dummy, holder) ← LGraphUtil.createExternalPortDummy holder portConstraints portSide netFlow graphSize
    portPosition portSize layoutDirection lgraph
  liftElk (ElkM.modifyPort elkport fun p => { p with props := holder })
  modifyNode dummy fun n => { n with
    internal := { n.internal with origin := some (.elkPort elkport) }
    props := n.props.set CoreOptions.PORT_LABELS_PLACEMENT PortLabelPlacement.outsideSet }
  let dummyPort := (← getNode dummy).ports[0]?
  if let some dp := dummyPort then
    let some connected ← withElk (isConnectedToExternalNodes · elkport)
      | throwIllegalState "port must have a parent node"
    modifyPort dp fun p => { p with connectedToExternalNodes := connected }
  let portLabelPlacement := graphNode.props.getD CoreOptions.PORT_LABELS_PLACEMENT PortLabelPlacement.outsideSet
  transformExternalPortLabels imp port.labels dummyPort portSize portSide
    (portLabelPlacement.contains .inside) (PortLabelPlacement.isFixed portLabelPlacement)
  -- the spacings that apply to the labels are those of the parent graph
  if let some parent := graphNode.parent then
    let parentProps := (← elkNode parent).props
    let horizontal := parentProps.getD LayeredOptions.SPACING_LABEL_PORT_HORIZONTAL fl1p0
    let vertical := parentProps.getD LayeredOptions.SPACING_LABEL_PORT_VERTICAL fl1p0
    let labelLabel := parentProps.getD LayeredOptions.SPACING_LABEL_LABEL fl0p0
    modifyNode dummy fun n => { n with props :=
      ((n.props.set LayeredOptions.SPACING_LABEL_PORT_HORIZONTAL horizontal).set
        LayeredOptions.SPACING_LABEL_PORT_VERTICAL vertical).set LayeredOptions.SPACING_LABEL_LABEL labelLabel }
  modifyGraph lgraph fun g => { g with layerlessNodes := g.layerlessNodes.push dummy }
  if let some dp := dummyPort then
    imp.state.modify fun s => { s with portMap := s.portMap.insert elkport dp }

/-! ## Graph import -/

/-- Rust `should_skip_node(node)`: `NO_LAYOUT`. -/
private def shouldSkipNode (node : NodeId) : LImportM Bool := do
  return (← elkNode node).props.getD CoreOptions.NO_LAYOUT false

/-- The model order step shared by the node loops of Rust `import_flat_graph_nodes` and
`import_hierarchical_graph`: assigns the next index (and records the cycle breaking group id)
when the child needs a model order. -/
private def assignNodeModelOrder (child : NodeId) (index : Int) (groups : Std.HashSet Int) :
    LImportM (Int × Std.HashSet Int) := do
  if !(← needsModelOrder child) then return (index, groups)
  setElementModelOrderForNode child index
  let props := (← elkNode child).props
  let groups := if props.has LayeredOptions.GROUP_MODEL_ORDER_CYCLE_BREAKING_ID then
      match props.get LayeredOptions.GROUP_MODEL_ORDER_CYCLE_BREAKING_ID with
      | some groupId => groups.insert groupId
      | none => groups
    else groups
  return (index + 1, groups)

/-- Stores `MAX_MODEL_ORDER_NODES` and `CB_NUM_MODEL_ORDER_GROUPS`. -/
private def setModelOrderCounts (lgraph : LGraphId) (index : Int) (groups : Std.HashSet Int) : LImportM Unit :=
  modifyGraph lgraph fun g => { g with internal := { g.internal with
    maxModelOrderNodes := index, cbNumModelOrderGroups := groups.size } }

/-- Rust `import_flat_graph_nodes(elkgraph, lgraph)`: the children that are laid out, with model
orders. -/
def importFlatGraphNodes (imp : ElkGraphImporter) (elkgraph : NodeId) (lgraph : LGraphId) : LImportM Unit := do
  let mut index : Int := 0
  let mut groups : Std.HashSet Int := {}
  for child in (← elkNode elkgraph).children do
    if ← shouldSkipNode child then continue
    (index, groups) ← assignNodeModelOrder child index groups
    discard <| transformNode imp child lgraph
  setModelOrderCounts lgraph index groups

/-- The graph an edge of Rust `import_flat_graph_edges` is placed in: the inside of the source for
inside self loops and edges into the source's descendants, the inside of the target for edges
from its descendants, else `lgraph` (also when that node has no nested graph). -/
private def edgeParentLGraph (imp : ElkGraphImporter) (elkgraph : NodeId) (lgraph : LGraphId)
    (sourceNode targetNode : NodeId) (isInsideSelfLoop : Bool) : LImportM LGraphId := do
  let parentElkGraph ←
    if isInsideSelfLoop || (← withElk (ElkGraphUtil.isDescendant · targetNode sourceNode)) then pure sourceNode
    else if ← withElk (ElkGraphUtil.isDescendant · sourceNode targetNode) then pure targetNode
    else pure elkgraph
  match ← nodeFor imp parentElkGraph with
  | some parentLNode => return (← getNode parentLNode).nestedGraph.getD lgraph
  | none => return lgraph

/-- The inside self loops of `elkgraph` that are contained in its parent (second loop of Rust
`import_flat_graph_edges`). -/
private def importParentInsideSelfLoops (imp : ElkGraphImporter) (elkgraph : NodeId) (lgraph : LGraphId) :
    LImportM Unit := do
  let some parentGraph := (← elkNode elkgraph).parent | return
  for e in (← elkNode parentGraph).containedEdges do
    let edge ← elkEdge e
    let some sourceNode ← withElk (firstNode · edge.sources) | continue
    let isSelfLoop ← withElk (ElkGraphUtil.isSelfloop · e)
    if sourceNode != elkgraph || !isSelfLoop then continue
    let insideSelfLoopsEnabled := (← elkNode sourceNode).props.getD CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false
    if insideSelfLoopsEnabled && edge.props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false then
      transformEdge imp e lgraph

/-- Rust `import_flat_graph_edges(elkgraph, lgraph)`, the edge loop of one level of
`importHierarchicalGraph` (Java's hierarchical edge loop): the contained edges (edge model order by
index when needed; Java's `checkEdgeValidity` first) whose edge and end nodes are laid out, each
placed by `edgeParentLGraph`; then the inside self loops of `elkgraph` contained in its parent. -/
def importFlatGraphEdges (imp : ElkGraphImporter) (elkgraph : NodeId) (lgraph : LGraphId) : LImportM Unit := do
  let graphNode ← elkNode elkgraph
  let needsEdgeModelOrder := needsModelOrderBasedOnParent graphNode.props
  let mut edgeModelOrderIndex : Int := 0
  for e in graphNode.containedEdges do
    -- Java: hyperedges and edges without an end are rejected before anything else
    checkEdgeValidity e
    if needsEdgeModelOrder then
      setElementModelOrderForEdge e edgeModelOrderIndex
      edgeModelOrderIndex := edgeModelOrderIndex + 1
    let edge ← elkEdge e
    let some sourceNode ← withElk (firstNode · edge.sources) | continue
    let some targetNode ← withElk (firstNode · edge.targets) | continue
    let isSelfLoop ← withElk (ElkGraphUtil.isSelfloop · e)
    let insideSelfLoopYo := edge.props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false
    let edgeNoLayout := edge.props.getD CoreOptions.NO_LAYOUT false
    let sourceProps := (← elkNode sourceNode).props
    let targetNoLayout := (← elkNode targetNode).props.getD CoreOptions.NO_LAYOUT false
    if edgeNoLayout || sourceProps.getD CoreOptions.NO_LAYOUT false || targetNoLayout then continue
    let insideSelfLoopsEnabled := sourceProps.getD CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false
    let isInsideSelfLoop := isSelfLoop && insideSelfLoopsEnabled && insideSelfLoopYo
    let parentLGraph ← edgeParentLGraph imp elkgraph lgraph sourceNode targetNode isInsideSelfLoop
    transformEdge imp e parentLGraph
  importParentInsideSelfLoops imp elkgraph lgraph

/-- The edge loop of Java `importFlatGraph(elkgraph, lgraph)`: for every contained edge (edge model
order by index when needed) `ElkGraphUtil.getSourceNode/getTargetNode` (Java
`IllegalArgumentException("Passed edge is not 'simple'.")` unless it has exactly one source and one
target), then the edge is transformed only if it is not `NO_LAYOUT`, not an inside self loop and
connects two children of `elkgraph` or a child with `elkgraph` itself (exclusive or). Other edges
(into a child's descendants, or between descendants) belong to no layout run of this graph and are
left alone without an error; the end nodes' `NO_LAYOUT` is not checked, so an edge to a skipped
child fails in `transformEdge` (Java's "could not be found" exception). Then the inside self loops
of `elkgraph` contained in its parent. elk-rs instead imports every contained edge whose ends are
laid out (placing edges into descendants in their nested graphs) and throws for ends outside the
layout scope. -/
def importFlatGraphEdgesJava (imp : ElkGraphImporter) (elkgraph : NodeId) (lgraph : LGraphId) : LImportM Unit := do
  let graphNode ← elkNode elkgraph
  let needsEdgeModelOrder := needsModelOrderBasedOnParent graphNode.props
  let mut edgeModelOrderIndex : Int := 0
  for e in graphNode.containedEdges do
    if needsEdgeModelOrder then
      setElementModelOrderForEdge e edgeModelOrderIndex
      edgeModelOrderIndex := edgeModelOrderIndex + 1
    let edge ← elkEdge e
    if edge.sources.size != 1 || edge.targets.size != 1 then
      throwIllegalArgument "Passed edge is not 'simple'."
    let some source ← withElk (firstNode · edge.sources) | continue
    let some target ← withElk (firstNode · edge.targets) | continue
    let enableInsideSelfLoops := (← elkNode source).props.getD CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false
    let isToBeLaidOut := !edge.props.getD CoreOptions.NO_LAYOUT false
    let isInsideSelfLoop := enableInsideSelfLoops && (← withElk (ElkGraphUtil.isSelfloop · e)) &&
      edge.props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false
    let sourceParent := (← elkNode source).parent
    let targetParent := (← elkNode target).parent
    let connectsSiblings := sourceParent == some elkgraph && sourceParent == targetParent
    let connectsToGraph := (sourceParent == some elkgraph && target == elkgraph) !=
      (targetParent == some elkgraph && source == elkgraph)
    if isToBeLaidOut && !isInsideSelfLoop && (connectsToGraph || connectsSiblings) then
      transformEdge imp e lgraph
  importParentInsideSelfLoops imp elkgraph lgraph

/-- Java `importFlatGraph(elkgraph, lgraph)`: nodes, then `importFlatGraphEdgesJava`. -/
def importFlatGraph (imp : ElkGraphImporter) (elkgraph : NodeId) (lgraph : LGraphId) : LImportM Unit := do
  importFlatGraphNodes imp elkgraph lgraph
  importFlatGraphEdgesJava imp elkgraph lgraph

/-- Rust `uses_elk_layered` of `import_hierarchical_graph`: no `ALGORITHM`, or one that the layered
algorithm id ends with (trimmed). -/
private def usesElkLayered (props : PropertyMap) : Bool :=
  match props.get CoreOptions.ALGORITHM with
  | some algorithmId => LayeredOptions.ALGORITHM_ID.endsWith algorithmId.trimAscii.toString
  | none => true

/-- The nested graph Rust `import_hierarchical_graph` creates for a child that is laid out by
layered in the same run (`INCLUDE_CHILDREN` or `INHERIT`) and has children or inside self loops:
`DIRECTION` of the parent level, port sides and minimum size when it has size constraints. -/
private def createNestedGraph (child : NodeId) (parentGraphDirection : Direction) : LImportM (Option LGraphId) := do
  let childNode ← elkNode child
  let hasChildren := !childNode.children.isEmpty
  let hasInsideSelfLoops ← withElk (hasInsideSelfLoopEdge · child)
  let childHierarchyHandling := childNode.props.getD LayeredOptions.HIERARCHY_HANDLING HierarchyHandling.inherit
  -- Java resolves a child's INHERIT against the parent's INCLUDE_CHILDREN; this importer only
  -- recurses under INCLUDE_CHILDREN, so INHERIT counts as enabled
  let hasHierarchyHandlingEnabled := childHierarchyHandling == .includeChildren || childHierarchyHandling == .inherit
  if !(usesElkLayered childNode.props && hasHierarchyHandlingEnabled && (hasChildren || hasInsideSelfLoops)) then
    return none
  let nested ← createLGraph child
  setGraphProp nested LayeredOptions.DIRECTION parentGraphDirection
  if ← shouldCalculateMinimumGraphSize child then
    for port in childNode.ports do
      ensureDefinedPortSide nested port
    calculateMinimumGraphSize child nested
  return some nested

/-- Rust `import_hierarchical_graph(elkgraph, lgraph)` (Java `importHierarchicalGraph`, but
recursive): the children that are laid out (model orders per level), each child's nested graph
imported right after its node (`COMPOUND_NODE`, parent/nested links), then the level's edges. -/
partial def importHierarchicalGraph (imp : ElkGraphImporter) (elkgraph : NodeId) (lgraph : LGraphId) : LImportM Unit := do
  let parentGraphDirection ← LGraphUtil.getDirection lgraph
  let mut index : Int := 0
  let mut groups : Std.HashSet Int := {}
  for child in (← elkNode elkgraph).children do
    if ← shouldSkipNode child then continue
    (index, groups) ← assignNodeModelOrder child index groups
    let nested ← createNestedGraph child parentGraphDirection
    let lnode ← transformNode imp child lgraph
    if let some nestedGraph := nested then
      modifyGraph nestedGraph fun g => { g with parentNode := some lnode }
      modifyNode lnode fun n => { n with
        nestedGraph := some nestedGraph, internal := { n.internal with compoundNode := true } }
      importHierarchicalGraph imp child nestedGraph
  setModelOrderCounts lgraph index groups
  importFlatGraphEdges imp elkgraph lgraph

/-- `importGraph(elkgraph)` (Rust `import_graph`): creates the top-level `LGraph` (`PARTITIONS`
when partitioning is active), defines the sides of the graph's ports, transforms them into external
port dummies when the graph has external ports, computes the minimum graph size, and imports the
graph hierarchically (`INCLUDE_CHILDREN`) or flat. -/
def importGraph (imp : ElkGraphImporter) (elkgraph : NodeId) : LImportM LGraphId := do
  let lgraph ← createLGraph elkgraph
  imp.state.modify fun s => { s with topLevelElkGraph := some elkgraph, topLevelLGraph := some lgraph }
  let graphNode ← elkNode elkgraph
  if graphNode.props.getD CoreOptions.PARTITIONING_ACTIVATE false then
    setGraphProperties lgraph ((← graphProperties lgraph).insert .partitions)
  let ports := graphNode.ports
  for port in ports do
    ensureDefinedPortSide lgraph port
  let gp ← graphProperties lgraph
  let gp ← withElk (checkExternalPorts · elkgraph gp)
  setGraphProperties lgraph gp
  if gp.contains .externalPorts then
    for port in ports do
      transformExternalPort imp elkgraph lgraph port
  if ← shouldCalculateMinimumGraphSize elkgraph then
    calculateMinimumGraphSize elkgraph lgraph
  let hierarchyHandling := (← elkNode elkgraph).props.getD LayeredOptions.HIERARCHY_HANDLING HierarchyHandling.inherit
  if hierarchyHandling == .includeChildren then importHierarchicalGraph imp elkgraph lgraph
  else importFlatGraph imp elkgraph lgraph
  return lgraph

/-- `applyLayout(lgraph)`: `ElkGraphLayoutTransferrer.applyLayout` with the arena of `LImportM`,
the importer's `ledges` and the ElkNode the graph was imported from (`LGraphInternals.origin`;
nothing happens for a graph without an ElkNode origin, like the Rust transferrer). -/
def applyLayout (imp : ElkGraphImporter) (lgraph : LGraphId) : LImportM Unit := do
  let a ← get
  let ledges ← imp.ledges.get
  match (a.graph lgraph).internal.origin with
  | some (.elkNode root) => liftElk (ElkGraphLayoutTransferrer.applyLayout a ledges lgraph root)
  | _ => pure ()

end ElkGraphImporter

end Elk.Alg.Layered.Graph.Transform
