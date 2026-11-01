import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Alg.Common.NetworkSimplex
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.p4nodes.NetworkSimplexPlacer` (elk-rs `p4nodes/network_simplex_placer.rs`)

Node placement via network simplex on an auxiliary graph (Gansner et al., *A technique for
drawing directed graphs*, 1993; flexible nodes after Ulrich Rüegg et al., *Improving the
Layout of Flexible Nodes…*): every node becomes one auxiliary node (fixed port positions) or
a head/tail pair with one auxiliary node per east/west port (flexible nodes); every edge
becomes a dummy node with two weighted auxiliary edges towards the port representations; the
layers of the network simplex result are the y coordinates.

Port notes (Rust is the oracle):

* like Rust, `prepare` overwrites `LNode.id` (index over all layer nodes) and `LEdge.id` (index
  over the nodes' outgoing edges); `nodeReps`/`edgeReps`/`nodeState`/`crossing` are indexed
  by these ids, ids outside the arrays read as missing;
* the auxiliary `NGraph` lives in the local `State` (`StateRefT` over `LayeredM`); its node
  and edge origins are `NOrigin` (Rust `Arc<dyn Any>`); the port map is keyed by `LPortId`
  (Rust `Arc::as_ptr`);
* the Rust `ArenaSync` snapshot, taken after `prepare`, equals the live arena for everything
  read from it here (sizes, margins, port anchors/positions, port lists by side), so the arena
  is read live (`PORTING.md` §15.1); `markCrossingEdges` follows ELK Java (the ports' own
  incoming edge lists and Java's `ListIterator` scan, see there; elk-rs differs);
* `f64 as i32` conversions saturate (`f64AsI32`), `i32` products wrap (`Int.wrap32`);
* the `debug_assert!` on integral port offsets in `transformEdge` is not ported.
-/

namespace Elk.Alg.Layered.P4Nodes

open Elk.Graph Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Common.NetworkSimplex
open Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace NetworkSimplexPlacer

/-- `EDGE_WEIGHT_BASE`. -/
def EDGE_WEIGHT_BASE : Float := 4.0
/-- `SMALL_EDGE_WEIGHT`: weight of the auxiliary edges towards north/south port dummies. -/
def SMALL_EDGE_WEIGHT : Float := 0.1
/-- `LONG_EDGE_VS_PATH_FACTOR`. -/
def LONG_EDGE_VS_PATH_FACTOR : Float := 2.0
/-- `NODE_SIZE_WEIGHT_STATIC`: weight of the head/tail edge of a flexible node of fixed size. -/
def NODE_SIZE_WEIGHT_STATIC : Float := 10000.0
/-- `NODE_SIZE_WEIGHT_FLEXIBLE`: weight of the head/tail edge of a node of flexible size. -/
def NODE_SIZE_WEIGHT_FLEXIBLE : Float := 1.0
/-- `EPSILON`. -/
def EPSILON : Float := 0.00001
/-- Node state `VISITED` (path identification). -/
def VISITED : Int := -1
/-- Node state `OTHER`. -/
def OTHER : Int := 0
/-- Node state `JUNCTION`: a node with more than one incoming or outgoing edge, or a leaf. -/
def JUNCTION : Int := 2

/-- `HIERARCHY_PROCESSING_ADDITIONS`: the hierarchical port position processor before edge routing. -/
def HIERARCHY_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p5EdgeRouting .hierarchicalPortPositionProcessor

/-- `getLayoutProcessorConfiguration(graph)`: the hierarchy additions if the graph has external ports. -/
def getLayoutProcessorConfiguration (graph : LGraphId) : LayeredM (Option LayeredProcessorConfiguration) := do
  if (← getGraph graph).internal.graphProperties.contains .externalPorts then
    return some (LayoutProcessorConfiguration.createFrom HIERARCHY_PROCESSING_ADDITIONS)
  else
    return none

/-- Origin of an auxiliary node or edge (Rust `Arc<dyn Any>` holding an `LNodeRef`,
`LPortRef` or `LEdgeRef`). -/
inductive NOrigin where
  | node (n : LNodeId)
  | port (p : LPortId)
  | edge (e : LEdgeId)
  deriving BEq, Repr, Inhabited

/-- `NodeRep`: the auxiliary representation of a node (`head = tail` for fixed nodes). -/
structure NodeRep where
  origin : LNodeId
  head : NNodeId
  tail : NNodeId
  isFlexible : Bool
  deriving Inhabited

/-- `EdgeRep`: the two auxiliary edges (from the edge dummy to the source/target port rep). -/
structure EdgeRep where
  left : NEdgeId
  right : NEdgeId
  deriving Inhabited

/-- `Path`: a chain of edges between two junction nodes. -/
structure Path where
  edges : Array LEdgeId := #[]
  deriving Inhabited

/-- Rust `x as i32`: truncation toward zero, saturating at the `i32` bounds, NaN → 0. -/
def f64AsI32 (x : Float) : Int :=
  if x.isNaN then 0
  else if x >= 2147483647.0 then 2147483647
  else if x <= -2147483648.0 then -2147483648
  else Float.toIntTrunc x

/-- `NodeFlexibility.getNodeFlexibility(node)` (Rust `get_node_flexibility`): the node's
`NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY`, else the graph's default. -/
def getNodeFlexibility (graphProps : PropertyMap) (nd : LNode) : NodeFlexibility :=
  match nd.props.get LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY with
  | some v => v
  | none =>
    match graphProps.get LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT with
    | some v => v
    | none => LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT.default.getD .none

/-- `Spacings.getIndividualOrDefault(graph, node, property)`; throws `UnspecifiedSpacingException`. -/
private def individualOrDefault {α : Type} [PropCodec α] (graphProps nodeProps : PropertyMap) (p : Property α) : IO α :=
  match Spacings.getIndividualOrDefaultWithGraph? graphProps nodeProps p with
  | some v => pure v
  | none => throw (unspecifiedSpacing)

/-- `isFlexibleNode(node)`: a normal node with at least two ports, free port positions, a
flexibility other than `NONE` and (unless its size may grow) enough height for its east and
west ports. -/
def isFlexibleNode (graphProps : PropertyMap) (n : LNodeId) : LayeredM Bool := do
  let nd ← getNode n
  if nd.type != .normal then
    return false
  if nd.ports.size <= 1 then
    return false
  if (nd.props.get LayeredOptions.PORT_CONSTRAINTS |>.getD .undefined).isPosFixed then
    return false
  let nf := getNodeFlexibility graphProps nd
  if nf == .none then
    return false
  if !nf.isFlexibleSizeWhereSpacePermits then
    let portSpacing ← individualOrDefault graphProps nd.props LayeredOptions.SPACING_PORT_PORT
    let mut additionalPortSpacing ← individualOrDefault graphProps nd.props LayeredOptions.SPACING_PORTS_SURROUNDING
    if additionalPortSpacing == ({} : ElkMargin) then
      additionalPortSpacing := ⟨portSpacing, portSpacing, portSpacing, portSpacing⟩
    let westCount := (← withArena (·.nodePortSideView n .west)).size
    let eastCount := (← withArena (·.nodePortSideView n .east)).size
    let sizeY := nd.size.y
    let requiredWestHeight :=
      additionalPortSpacing.top + additionalPortSpacing.bottom + Float.ofNat (westCount - 1) * portSpacing
    if requiredWestHeight > sizeY then
      return false
    let requiredEastHeight :=
      additionalPortSpacing.top + additionalPortSpacing.bottom + Float.ofNat (eastCount - 1) * portSpacing
    if requiredEastHeight > sizeY then
      return false
  return true

/-- `getEdgeTypeWeight(nodeType1, nodeType2)`: 1, 2 or 8 times `EDGE_WEIGHT_BASE` for
normal–normal, normal–dummy and dummy–dummy edges. -/
def edgeTypeWeight (t1 t2 : NodeType) : Float :=
  if t1 == .normal && t2 == .normal then EDGE_WEIGHT_BASE
  else if t1 == .normal || t2 == .normal then fl2p0 * EDGE_WEIGHT_BASE
  else fl8p0 * EDGE_WEIGHT_BASE

/-- `isHandledEdge(edge)`: neither a self loop nor an in-layer edge. -/
def isHandledEdge (a : LGraphArena) (e : LEdgeId) : Bool :=
  !a.edgeIsSelfLoop e && !a.edgeIsInLayerEdge e

/-- `getNodeState(node)`: `JUNCTION` for nodes with more than one (non self loop) incoming or
outgoing edge (counted cumulatively over the ports) or exactly one edge, else `OTHER`. -/
def getNodeState (a : LGraphArena) (n : LNodeId) : Int := Id.run do
  let mut inco := 0
  let mut ouco := 0
  for port in (a.node n).ports do
    let pt := a.port port
    inco := inco + (pt.incomingEdges.filter fun e => !a.edgeIsSelfLoop e).size
    ouco := ouco + (pt.outgoingEdges.filter fun e => !a.edgeIsSelfLoop e).size
    if inco > 1 || ouco > 1 then
      return JUNCTION
  if inco + ouco == 1 then
    return JUNCTION
  return OTHER

/-- Rust `ArenaSync` pass 2 incoming lists (`LGraphArena.arenaIncomingEdges`, `LGraphQueries`). -/
def arenaIncomingEdges (a : LGraphArena) (g : LGraphId) : Std.HashMap LPortId (Array LEdgeId) :=
  a.arenaIncomingEdges g

/-- Phase-local state of one `process` run (the Rust placer fields). -/
structure State where
  graph : LGraphId
  graphProps : PropertyMap
  spacings : Spacings
  nGraph : NGraph NOrigin := {}
  nodeReps : Array (Option NodeRep) := #[]
  edgeReps : Array (Option EdgeRep) := #[]
  portMap : Std.HashMap LPortId NNodeId := {}
  nodeCount : Nat := 0
  edgeCount : Nat := 0
  nodeState : Array Int := #[]
  twoPaths : Array Path := #[]
  crossing : Array Bool := #[]
  flexibleWhereSpacePermitsEdges : Array NEdgeId := #[]

/-- The placer monad: phase state over the layered arena. -/
abbrev NspM := StateRefT State LayeredM

/-- Runs `f` on the auxiliary graph taken out of the state (keeps it uniquely referenced). -/
@[inline] private def withNGraph {α : Type} (f : NGraph NOrigin → IO (NGraph NOrigin × α)) : NspM α := do
  let g ← modifyGet fun s => (s.nGraph, { s with nGraph := {} })
  let (g, r) ← f g
  modify fun s => { s with nGraph := g }
  return r

@[inline] private def nnode (n : NNodeId) : NspM (NNode NOrigin) := do return (← get).nGraph.node n
@[inline] private def nedge (e : NEdgeId) : NspM (NEdge NOrigin) := do return (← get).nGraph.edge e
@[inline] private def nlayer (n : NNodeId) : NspM Int := do return (← get).nGraph.node n |>.layer

@[inline] private def modifyNNode (n : NNodeId) (f : NNode NOrigin → NNode NOrigin) : NspM Unit :=
  modify fun s => { s with nGraph := s.nGraph.modifyNode n f }

@[inline] private def modifyNEdge (e : NEdgeId) (f : NEdge NOrigin → NEdge NOrigin) : NspM Unit :=
  modify fun s => { s with nGraph := s.nGraph.modifyEdge e f }

/-- `NNode.of().origin(origin).type(type).create(nGraph)`. -/
private def createNNode (origin : Option NOrigin) (type : String) : NspM NNodeId :=
  withNGraph fun g =>
    let b : NNodeBuilder NOrigin := NNode.of
    let b := match origin with
      | some o => b.origin o
      | none => b
    pure ((b.type type).create g)

/-- `NEdge.of(origin).weight(weight).delta(delta).source(source).target(target).create()`. -/
private def createNEdge (weight : Float) (delta : Int) (source target : NNodeId)
    (origin : Option NOrigin := none) : NspM NEdgeId :=
  withNGraph fun g =>
    let b : NEdgeBuilder NOrigin := match origin with
      | some o => NEdge.ofOrigin o
      | none => NEdge.of
    (b.weight weight |>.delta delta |>.source source |>.target target).create g

/-- `nodeReps.get(nodeId)` (`none` for ids outside the array). -/
private def nodeRepAt? (nodeId : Int) : NspM (Option NodeRep) := do
  if nodeId < 0 then return none
  return ((← get).nodeReps[nodeId.toNat]?).bind fun r => r

/-- `nodeReps[node.id]` (Rust panics when missing). -/
private def nodeRepOf (n : LNodeId) : NspM NodeRep := do
  match (← nodeRepAt? (← getNode n).id) with
  | some r => return r
  | none => throw (IO.userError "java.lang.IllegalStateException: Missing node rep")

/-- `edgeReps.get(edge.id)` (Rust `get(..).and_then(..)`). -/
private def edgeRepOf? (e : LEdgeId) : NspM (Option EdgeRep) := do
  let edgeId := (← getEdge e).id
  if edgeId < 0 then return none
  return ((← get).edgeReps[edgeId.toNat]?).bind fun r => r

/-- `Spacings.getVerticalSpacing(n1, n2)` for two arena nodes. -/
private def verticalSpacing (n1 n2 : LNodeId) : NspM Float := do
  let a ← getNode n1
  let b ← getNode n2
  (← get).spacings.getVerticalSpacing a.type a.props b.type b.props

-- ============================================================================================
-- Preparation

/-- `prepare(graph)`: assigns `LNode.id` (index over the layer nodes) and `LEdge.id` (index
over their outgoing edges), and rounds port anchors (flexible nodes) and port positions to
integers (`y - round(y)` offsets). -/
private def prepare : NspM Unit := do
  let s ← get
  let graph := s.graph
  let graphProps := s.graphProps
  let layers := (← getGraph graph).layers
  let mut nodeIdx : Nat := 0
  let mut edgeIdx : Nat := 0
  for layer in layers do
    for node in (← getLayer layer).nodes do
      let ni := nodeIdx
      modifyNode node fun n => { n with id := (ni : Int) }
      let outgoingEdges ← withArena (·.nodeOutgoingEdges node)
      nodeIdx := nodeIdx + 1
      for edge in outgoingEdges do
        let ei := edgeIdx
        modifyEdge edge fun e => { e with id := (ei : Int) }
        edgeIdx := edgeIdx + 1
      let anchorMustBeInteger ← isFlexibleNode graphProps node
      for port in (← getNode node).ports do
        modifyPort port fun p => Id.run do
          let mut p := p
          if anchorMustBeInteger then
            let y := p.anchor.y
            if y != y.floor then
              -- Java `Math.round` (half up, also for negative values), not C `round`
              let offset := y - (Float.javaRound y).toFloat
              p := { p with anchor := { p.anchor with y := p.anchor.y - offset } }
          let y := p.position.y + p.anchor.y
          if y != y.floor then
            let offset := y - (Float.javaRound y).toFloat
            p := { p with position := { p.position with y := p.position.y - offset } }
          return p
  let nc := nodeIdx
  let ec := edgeIdx
  modify fun s => { s with
    nodeCount := nc, edgeCount := ec,
    nodeReps := Array.replicate nc none, edgeReps := Array.replicate ec none,
    nodeState := #[], twoPaths := #[], crossing := #[] }

-- ============================================================================================
-- Initial auxiliary graph

/-- `transformNodeFixedPos(node)`: a single auxiliary node, which also represents the node's
east and west ports. -/
private def transformFixedPosNode (node : LNodeId) : NspM NodeRep := do
  let single ← createNNode (some (.node node)) "non-flexible"
  for port in (← getNode node).ports do
    let side := (← getPort port).side
    if side == .east || side == .west then
      modify fun s => { s with portMap := s.portMap.insert port single }
  return { origin := node, isFlexible := false, head := single, tail := single }

/-- `transformPorts(ports, corners)`: a chain of auxiliary port nodes from the head to the
tail of a flexible node, separated by the port spacing and the port sizes. -/
private def transformPorts (ports : Array LPortId) (corners : NodeRep) : NspM Unit := do
  if ports.isEmpty then
    return
  let s ← get
  let originProps := (← getNode corners.origin).props
  let portSpacing ← individualOrDefault s.graphProps originProps LayeredOptions.SPACING_PORT_PORT
  let portSurrounding ← individualOrDefault s.graphProps originProps LayeredOptions.SPACING_PORTS_SURROUNDING
  let mut lastNNode := corners.head
  let mut lastPort : Option LPortId := none
  for port in ports do
    let spacing ← match lastPort with
      | some last => pure (portSpacing + (← getPort last).size.y)
      | none => pure portSurrounding.top
    let nnode ← createNNode (some (.port port)) "port"
    modify fun s => { s with portMap := s.portMap.insert port nnode }
    let _ ← createNEdge fl0p0 (f64AsI32 spacing.ceil) lastNNode nnode
    lastPort := some port
    lastNNode := nnode
  if let some last := lastPort then
    let lastSize := (← getPort last).size.y
    let _ ← createNEdge fl0p0 (f64AsI32 (portSurrounding.bottom + lastSize).ceil) lastNNode corners.tail

/-- `transformNodeFixedOrder(node)`: a head and a tail node connected by the node size edge
(flexible size: weight `NODE_SIZE_WEIGHT_FLEXIBLE`), west ports (bottom-up) and east ports
(top-down) as chains between them. -/
private def transformFixedOrderNode (node : LNodeId) : NspM NodeRep := do
  let topLeft ← createNNode (some (.node node)) "flexible-head"
  let bottomLeft ← createNNode (some (.node node)) "flexible-tail"
  let corners : NodeRep := { origin := node, isFlexible := true, head := topLeft, tail := bottomLeft }
  let nd ← getNode node
  let minHeight := nd.size.y
  let nf := getNodeFlexibility (← get).graphProps nd
  let sizeWeight := if nf.isFlexibleSize then NODE_SIZE_WEIGHT_FLEXIBLE else NODE_SIZE_WEIGHT_STATIC
  let nodeSizeEdge ← createNEdge sizeWeight (f64AsI32 minHeight.ceil) topLeft bottomLeft
  if nf == .nodeSizeWhereSpacePermits then
    modify fun s => { s with flexibleWhereSpacePermitsEdges := s.flexibleWhereSpacePermitsEdges.push nodeSizeEdge }
  let westPorts ← withArena (·.nodePortSideView node .west)
  let eastPorts ← withArena (·.nodePortSideView node .east)
  transformPorts westPorts.reverse corners
  transformPorts eastPorts corners
  return corners

/-- `transformLayer(layer)`: node representations plus the separation edges between
consecutive nodes (margins, vertical spacing and, for fixed nodes, the node height). -/
private def transformLayer (layer : LayerId) : NspM Unit := do
  let mut lastRep : Option NodeRep := none
  for node in (← getLayer layer).nodes do
    let rep ← if (← isFlexibleNode (← get).graphProps node) then transformFixedOrderNode node
      else transformFixedPosNode node
    let nid := (← getNode node).id
    if nid >= 0 then
      modify fun s => { s with nodeReps := s.nodeReps.modify nid.toNat fun _ => some rep }
    if let some last := lastRep then
      let lastNd ← getNode last.origin
      let nd ← getNode node
      let vertical ← verticalSpacing last.origin node
      let mut value := lastNd.margin.bottom + vertical + nd.margin.top
      if !last.isFlexible then
        value := value + lastNd.size.y
      let _ ← createNEdge fl0p0 (f64AsI32 value.ceil) last.tail rep.head
    lastRep := some rep

/-- The auxiliary node of a port (Rust `port_map[&port]`, which panics when missing). -/
private def portRep (port : LPortId) : NspM NNodeId := do
  match (← get).portMap.get? port with
  | some n => return n
  | none => throw (IO.userError "java.lang.IllegalStateException: Port without auxiliary node")

/-- `getEdgeWeight(edge)`: `max(1, PRIORITY_STRAIGHTNESS)` times the edge type weight. -/
private def getEdgeWeight (edge : LEdgeId) : LayeredM Float := do
  let a ← get
  let ed := a.edge edge
  let priority := max (ed.props.get LayeredOptions.PRIORITY_STRAIGHTNESS |>.getD 1) 1
  let types : Option (NodeType × NodeType) := do
    let sn ← (a.port (← ed.source)).owner
    let tn ← (a.port (← ed.target)).owner
    return ((a.node sn).type, (a.node tn).type)
  let (st, tt) := types.getD (.normal, .normal)
  return Float.ofInt priority * edgeTypeWeight st tt

/-- `transformEdge(edge)`: an edge dummy with two auxiliary edges towards the port
representations; the deltas encode the difference of the port offsets. -/
private def transformEdge (edge : LEdgeId) : NspM Unit := do
  let dummy ← createNNode none "edge"
  let ed ← getEdge edge
  let some sourcePort := ed.source | return
  let some targetPort := ed.target | return
  let some sourceNode := (← getPort sourcePort).owner | return
  let some targetNode := (← getPort targetPort).owner | return
  let srcRep ← nodeRepOf sourceNode
  let tgtRep ← nodeRepOf targetNode
  let sp ← getPort sourcePort
  let tp ← getPort targetPort
  let srcOffset := if !srcRep.isFlexible then sp.anchor.y + sp.position.y else sp.anchor.y
  let tgtOffset := if !tgtRep.isFlexible then tp.anchor.y + tp.position.y else tp.anchor.y
  -- Java `(int) Math.max(0, srcOffset - tgtOffset)`: truncation (elk-rs rounds; the offsets are only
  -- nearly integral after the `y - Math.round(y)` port shifts above)
  let tgtDelta := f64AsI32 (fmax (srcOffset - tgtOffset) fl0p0)
  let srcDelta := f64AsI32 (fmax (tgtOffset - srcOffset) fl0p0)
  let weight ← getEdgeWeight edge
  let left ← createNEdge weight srcDelta dummy (← portRep sourcePort) (some (.edge edge))
  let right ← createNEdge weight tgtDelta dummy (← portRep targetPort) (some (.edge edge))
  let eid := ed.id
  if eid >= 0 then
    modify fun s => { s with edgeReps := s.edgeReps.modify eid.toNat fun _ => some { left := left, right := right } }

/-- `transformEdges(graph)`: the handled outgoing edges of all layer nodes. -/
private def transformEdges : NspM Unit := do
  let layers := (← getGraph (← get).graph).layers
  for layer in layers do
    for node in (← getLayer layer).nodes do
      for edge in (← withArena (·.nodeOutgoingEdges node)) do
        if !(← withArena (isHandledEdge · edge)) then
          continue
        transformEdge edge

/-- `buildInitialAuxiliaryGraph(graph)`: all layers, then all edges. -/
private def buildInitialAuxiliaryGraph : NspM Unit := do
  for layer in (← getGraph (← get).graph).layers do
    transformLayer layer
  transformEdges

-- ============================================================================================
-- Further auxiliary edges

/-- `insertInLayerEdgeAuxiliaryEdges(graph)`: in-layer edges of normal nodes keep the dummy
close to the port (weight `EDGE_WEIGHT_BASE`, delta `0`), oriented by the in-layer order. -/
private def insertInLayerEdgeAuxiliaryEdges : NspM Unit := do
  let layers := (← getGraph (← get).graph).layers
  for layer in layers do
    for node in (← getLayer layer).nodes do
      if (← getNode node).type != .normal then
        continue
      for edge in (← withArena (·.nodeConnectedEdges node)) do
        if !(← withArena (·.edgeIsInLayerEdge edge)) then
          continue
        let ed ← getEdge edge
        let srcIsDummy ← match ed.source with
          | some sp => match (← getPort sp).owner with
            | some sn => pure ((← getNode sn).type != .normal)
            | none => pure false
          | none => pure false
        let some sourcePort := ed.source | continue
        let some targetPort := ed.target | continue
        let port := if srcIsDummy then targetPort else sourcePort
        let some dummyPort ← withArena (·.edgeOtherPort edge port) | continue
        let some dummyNode := (← getPort dummyPort).owner | continue
        let portRep? := (← get).portMap.get? port
        let dummyRep? := (← nodeRepAt? (← getNode dummyNode).id).map (·.head)
        let some pRep := portRep? | continue
        let some dRep := dummyRep? | continue
        let portIndex ← match (← getPort port).owner with
          | some owner => pure ((← withArena (·.nodeIndex owner)).getD 0)
          | none => pure 0
        let dummyIndex := (← withArena (·.nodeIndex dummyNode)).getD 0
        let (src, tgt) := if portIndex < dummyIndex then (pRep, dRep) else (dRep, pRep)
        let _ ← createNEdge EDGE_WEIGHT_BASE 0 src tgt

/-- `insertNorthSouthAuxiliaryEdges(graph)`: north/south port dummies are kept above/below
their node (weight `SMALL_EDGE_WEIGHT`, delta `0`). -/
private def insertNorthSouthAuxiliaryEdges : NspM Unit := do
  let layers := (← getGraph (← get).graph).layers
  for layer in layers do
    for node in (← getLayer layer).nodes do
      let southPorts ← withArena (·.nodePortSideView node .south)
      let northPorts ← withArena (·.nodePortSideView node .north)
      for port in southPorts do
        if let some dummy := (← getPort port).internal.portDummy then
          let nodeRep ← nodeRepOf node
          let dummyRep ← nodeRepOf dummy
          let _ ← createNEdge SMALL_EDGE_WEIGHT 0 nodeRep.tail dummyRep.head
      for port in northPorts do
        if let some dummy := (← getPort port).internal.portDummy then
          let dummyRep ← nodeRepOf dummy
          let nodeRep ← nodeRepOf node
          let _ ← createNEdge SMALL_EDGE_WEIGHT 0 dummyRep.tail nodeRep.head

/-- Minimum and maximum layer of the auxiliary nodes (`0` for an empty graph). -/
private def layerRange (g : NGraph NOrigin) : Int × Int := Id.run do
  let mut minLayer : Option Int := none
  let mut maxLayer : Option Int := none
  for n in g.nodeList do
    let l := (g.node n).layer
    minLayer := some (match minLayer with | some m => min m l | none => l)
    maxLayer := some (match maxLayer with | some m => max m l | none => l)
  return (minLayer.getD 0, maxLayer.getD 0)

/-- `insertFlexibleWhereSpaceAuxiliaryEdges()`: a global source and sink keep the extent of the
current layering, every normal node with more than one port is fixed between them, so that
`NODE_SIZE_WHERE_SPACE_PERMITS` nodes can only grow into free space. -/
private def insertFlexibleWhereSpaceAuxiliaryEdges : NspM Unit := do
  let (minLayer, maxLayer) := layerRange (← get).nGraph
  let usedLayers := maxLayer - minLayer
  let globalSource ← createNNode none ""
  let globalSink ← createNNode none ""
  let _ ← createNEdge (NODE_SIZE_WEIGHT_STATIC * fl2p0) usedLayers globalSource globalSink
  for rep? in (← get).nodeReps do
    let some rep := rep? | continue
    let nd ← getNode rep.origin
    if nd.type != .normal || nd.ports.size <= 1 then
      continue
    let tailLayer ← nlayer rep.tail
    let headLayer ← nlayer rep.head
    let _ ← createNEdge fl0p0 (tailLayer - minLayer) globalSource rep.tail
    let _ ← createNEdge fl0p0 (usedLayers - headLayer) rep.head globalSink

-- ============================================================================================
-- Straight edges

/-- `crossing[id] = true` for ids inside the array (Rust `if id < crossing.len()`). -/
@[inline] private def setCrossing (crossing : Array Bool) (id : Int) : Array Bool :=
  if id >= 0 && id.toNat < crossing.size then crossing.set! id.toNat true else crossing

/-- `markCrossingEdges(left, right)`: marks the edges between two layers that cross, using the
order of the east port edges of the left layer and the west port edges (`port.getIncomingEdges()`)
of the right layer (nodes bottom-up). For every closing edge, Java's `ListIterator` scans the open
edges from the end: every open edge after the closing edge is marked together with it, the closing
edge is removed — except that the open edge at index 0 is neither marked nor removed (the loop
stops when there is no previous element; elk-rs, which elk-lean followed before agent RJ3, marks and
removes down to index 0 and iterates the `ArenaSync` incoming lists instead of the ports' own). -/
private def markCrossingEdges (left right : LayerId) : NspM Unit := do
  let mut openEdges : Array LEdgeId := #[]
  for node in (← getLayer left).nodes do
    for port in (← withArena (·.nodePortSideView node .east)) do
      for edge in (← getPort port).outgoingEdges do
        let a ← getThe LGraphArena
        let ed := a.edge edge
        let isSelf := a.edgeIsSelfLoop edge
        let isInLayer := if isSelf then false else a.edgeIsInLayerEdge edge
        let targetLayer := ed.target.bind (fun p => (a.port p).owner) |>.bind (fun n => (a.node n).layer)
        let targetNotInRight := match targetLayer with
          | some l => l != right
          | none => true
        if isSelf || isInLayer || targetNotInRight then
          continue
        openEdges := openEdges.push edge
  for node in (← getLayer right).nodes.reverse do
    for port in (← withArena (·.nodePortSideView node .west)) do
      for edge in (← getPort port).incomingEdges do
        let a ← getThe LGraphArena
        let ed := a.edge edge
        let isSelf := a.edgeIsSelfLoop edge
        let isInLayer := if isSelf then false else a.edgeIsInLayerEdge edge
        let sourceLayer := ed.source.bind (fun p => (a.port p).owner) |>.bind (fun n => (a.node n).layer)
        let sourceNotInLeft := match sourceLayer with
          | some l => l != left
          | none => true
        if isSelf || isInLayer || sourceNotInLeft then
          continue
        if openEdges.isEmpty then
          continue
        let edgeIdVal := ed.id
        -- `last = openEdgesIt.previous()`, then `while (last != edge && openEdgesIt.hasPrevious())`
        let mut idx := openEdges.size - 1
        while openEdges[idx]! != edge && idx > 0 do
          let lastId := (a.edge openEdges[idx]!).id
          modify fun s => { s with crossing := setCrossing (setCrossing s.crossing lastId) edgeIdVal }
          idx := idx - 1
        -- `if (openEdgesIt.hasPrevious()) openEdgesIt.remove()`
        if idx > 0 then
          openEdges := openEdges.eraseIdx! idx

/-- `markEdgeCrossings(graph)`: crossing flags for every pair of consecutive layers. -/
private def markEdgeCrossings : NspM Unit := do
  let ec := (← get).edgeCount
  modify fun s => { s with crossing := Array.replicate ec false }
  let graph := (← get).graph
  let layers := (← getGraph graph).layers
  for i in [0:layers.size - 1] do
    markCrossingEdges layers[i]! layers[i + 1]!

/-- The node state of a node id (`OTHER` outside the array, like Rust `get(..).unwrap_or`). -/
private def nodeStateOf (id : Int) : NspM Int := do
  if id < 0 then return OTHER
  return (← get).nodeState.getD id.toNat OTHER

/-- `follow(edge, current, path)`: extends the path over non-junction nodes; stops at visited
or junction nodes and at crossing edges. The Rust recursion is a tail call, written as a loop. -/
private def follow (edge0 : LEdgeId) (current0 : LNodeId) (path0 : Path) : NspM Path := do
  let mut edge := edge0
  let mut current := current0
  let mut path := path0
  while true do
    let a ← getThe LGraphArena
    let ed := a.edge edge
    let sourceNode := ed.source.bind fun p => (a.port p).owner
    let targetNode := ed.target.bind fun p => (a.port p).owner
    let other := if sourceNode == some current then targetNode else sourceNode
    path := { path with edges := path.edges.push edge }
    let some other := other | return path
    let otherId := (a.node other).id
    let st ← nodeStateOf otherId
    let edgeIdVal := ed.id
    let crossingArr := (← get).crossing
    let crossing := if edgeIdVal < 0 then false else crossingArr.getD edgeIdVal.toNat false
    if st == VISITED || st == JUNCTION || crossing then
      return path
    if otherId >= 0 then
      modify fun s => { s with nodeState := s.nodeState.modify otherId.toNat fun _ => VISITED }
    let mut next : Option LEdgeId := none
    for incident in a.nodeConnectedEdges other do
      if !isHandledEdge a incident then
        continue
      if incident == edge then
        continue
      next := some incident
      break
    match next with
    | some n =>
      edge := n
      current := other
    | none => return path
  return path

/-- `identifyPaths(graph)`: the paths starting at junction nodes. -/
private def identifyPaths : NspM (Array Path) := do
  let mut paths : Array Path := #[]
  let layers := (← getGraph (← get).graph).layers
  for layer in layers do
    for node in (← getLayer layer).nodes do
      if (← nodeStateOf (← getNode node).id) != JUNCTION then
        continue
      for edge in (← withArena (·.nodeConnectedEdges node)) do
        if !(← withArena (isHandledEdge · edge)) then
          continue
        let path ← follow edge node {}
        if path.edges.size > 1 then
          paths := paths.push path
  return paths

/-- Source node of the first edge and target node of every edge of a path (the nodes checked
by `containsLongEdgeDummy` / `containsFlexibleNode`). -/
private def pathCheckedNodes (a : LGraphArena) (path : Path) : Array LNodeId := Id.run do
  let mut nodes : Array LNodeId := #[]
  if let some first := path.edges[0]? then
    if let some n := ((a.edge first).source).bind fun p => (a.port p).owner then
      nodes := nodes.push n
  for e in path.edges do
    if let some n := ((a.edge e).target).bind fun p => (a.port p).owner then
      nodes := nodes.push n
  return nodes

/-- `Path.containsLongEdgeDummy()`. -/
private def containsLongEdgeDummy (a : LGraphArena) (path : Path) : Bool :=
  (pathCheckedNodes a path).any fun n => (a.node n).type == .longEdge

/-- `Path.containsFlexibleNode(predicate)` (on `getNodeFlexibility`). -/
private def containsFlexibleNode (a : LGraphArena) (graphProps : PropertyMap) (path : Path)
    (pred : NodeFlexibility → Bool) : Bool :=
  (pathCheckedNodes a path).any fun n => pred (getNodeFlexibility graphProps (a.node n))

/-- `Path.orderTwoPath()`: swaps the two edges unless the first ends where the second starts. -/
private def orderTwoPath (a : LGraphArena) (path : Path) : Path :=
  match path.edges[0]?, path.edges[1]? with
  | some first, some second =>
    let firstTarget := ((a.edge first).target).bind fun p => (a.port p).owner
    let secondSource := ((a.edge second).source).bind fun p => (a.port p).owner
    let swap := match firstTarget, secondSource with
      | some x, some y => x != y
      | _, _ => true
    if swap then { edges := #[second, first] } else path
  | _, _ => path

/-- `Path.isTwoPathCenterNodeFlexible()`: whether the target of the first edge is flexible. -/
private def isTwoPathCenterNodeFlexible (path : Path) : NspM Bool := do
  if path.edges.size != 2 then
    return false
  let a ← getThe LGraphArena
  match ((a.edge path.edges[0]!).target).bind fun p => (a.port p).owner with
  | some n => isFlexibleNode (← getThe State).graphProps n
  | none => return false

/-- `preferStraightEdges(graph)`: two-paths are collected for post-processing; longer paths
without long edge dummies and size-flexible nodes get higher edge weights. -/
private def preferStraightEdges : NspM Unit := do
  let nc := (← get).nodeCount
  modify fun s => { s with nodeState := Array.replicate nc 0, twoPaths := #[] }
  let layers := (← getGraph (← get).graph).layers
  for layer in layers do
    for node in (← getLayer layer).nodes do
      let id := (← getNode node).id
      if id >= 0 && id.toNat < nc then
        let st ← withArena (getNodeState · node)
        modify fun s => { s with nodeState := s.nodeState.set! id.toNat st }
  markEdgeCrossings
  let paths ← identifyPaths
  for path in paths do
    if path.edges.size <= 1 then
      continue
    if path.edges.size == 2 then
      let path := orderTwoPath (← getThe LGraphArena) path
      if !(← isTwoPathCenterNodeFlexible path) then
        modify fun s => { s with twoPaths := s.twoPaths.push path }
      continue
    let a ← getThe LGraphArena
    if containsLongEdgeDummy a path ||
        containsFlexibleNode a (← get).graphProps path (·.isFlexibleSizeWhereSpacePermits) then
      continue
    for h : index in [0:path.edges.size] do
      let edge := path.edges[index]
      let base := if index == 0 || index + 1 == path.edges.size then edgeTypeWeight .normal .longEdge
        else edgeTypeWeight .longEdge .longEdge
      let weight := base * LONG_EDGE_VS_PATH_FACTOR
      if let some rep ← edgeRepOf? edge then
        -- Java `Math.max(old, old + (weight - old))`
        modifyNEdge rep.left fun e => { e with weight := javaMax e.weight (e.weight + (weight - e.weight)) }
        modifyNEdge rep.right fun e => { e with weight := javaMax e.weight (e.weight + (weight - e.weight)) }

/-- `NEdge` length beyond its minimum: `|layer(source) - layer(target)| - delta`. -/
private def length (e : NEdgeId) : NspM Int := do
  let ed ← nedge e
  let sl ← nlayer ed.source
  let tl ← nlayer ed.target
  return ((sl - tl).natAbs : Int) - ed.delta

/-- `(layer of the target, delta)` of an auxiliary edge. -/
private def targetLayerAndDelta (e : NEdgeId) : NspM (Int × Int) := do
  let ed ← nedge e
  return (← nlayer ed.target, ed.delta)

/-- `EdgeRep.isStraight()`: the two auxiliary edges place both ports at the same height. -/
private def isStraight (rep : EdgeRep) : NspM Bool := do
  let (ltl, ld) ← targetLayerAndDelta rep.left
  let (rtl, rd) ← targetLayerAndDelta rep.right
  return (ltl - ld) - (rtl - rd) == 0

/-- `improveTwoPath(path, probe)`: moves the center node of a two-path so that one of its
edges becomes straight if there is room. In probe mode, paths with equal room above and
below are deferred (returns `true`). -/
private def improveTwoPath (path : Path) (probe : Bool) : NspM Bool := do
  let some leftEdge ← edgeRepOf? path.edges[0]!
    | throw (IO.userError "java.lang.IllegalStateException: Missing edge rep")
  let some rightEdge ← edgeRepOf? path.edges[1]!
    | throw (IO.userError "java.lang.IllegalStateException: Missing edge rep")
  if (← isStraight leftEdge) && (← isStraight rightEdge) then
    return false
  let centerTarget := (← nedge leftEdge.right).target
  let some (.node centerNode) := (← nnode centerTarget).origin | return false
  let nNode ← nodeRepOf centerNode
  let mut aboveDist := Float.posInf
  let mut belowDist := Float.posInf
  let nodeIndex := (← withArena (·.nodeIndex centerNode)).getD 0
  let center ← getNode centerNode
  let layerNodes ← match center.layer with
    | some l => pure (← getLayer l).nodes
    | none => pure #[]
  let nHeadLayer := Float.ofInt (← nlayer nNode.head)
  if nodeIndex > 0 then
    let above := layerNodes[nodeIndex - 1]!
    let aboveRep ← nodeRepOf above
    let spacing := (← verticalSpacing above centerNode).ceil
    let ab ← getNode above
    aboveDist := (nHeadLayer - center.margin.top) -
      (Float.ofInt (← nlayer aboveRep.head) + ab.size.y + ab.margin.bottom) - spacing
  if nodeIndex + 1 < layerNodes.size then
    let below := layerNodes[nodeIndex + 1]!
    let belowRep ← nodeRepOf below
    let spacing := (← verticalSpacing below centerNode).ceil
    let bl ← getNode below
    belowDist := (Float.ofInt (← nlayer belowRep.head) - bl.margin.top) -
      (nHeadLayer + center.size.y + center.margin.bottom) - spacing
  -- Guava `DoubleMath.fuzzyEquals(aboveDist, belowDist, EPSILON)`: `|a - b| <= ε`, or `a == b` (both
  -- `+∞` for a node alone in its layer), or both NaN (elk-rs `(a - b).abs() < ε` missed the infinities)
  if probe && ((aboveDist - belowDist).abs <= EPSILON || aboveDist == belowDist ||
      (aboveDist.isNaN && belowDist.isNaN)) then
    return true
  let a ← length leftEdge.left
  let b := -(← length leftEdge.right)
  let c := -(← length rightEdge.left)
  let d ← length rightEdge.right
  let (leftLtl, leftLd) ← targetLayerAndDelta leftEdge.left
  let (leftRtl, leftRd) ← targetLayerAndDelta leftEdge.right
  let (rightLtl, rightLd) ← targetLayerAndDelta rightEdge.left
  let (rightRtl, rightRd) ← targetLayerAndDelta rightEdge.right
  let leftNsb := (leftLtl - leftLd) - (leftRtl - leftRd)
  let rightNsb := (rightLtl - rightLd) - (rightRtl - rightRd)
  let caseD := leftNsb > 0 && rightNsb < 0
  let caseC := leftNsb < 0 && rightNsb > 0
  let leftValue := leftLtl + leftRd
  let rightValue := rightRtl + rightLd
  let caseB := leftValue < rightValue
  let caseA := leftValue > rightValue
  let mut moveBy : Int := 0
  if !caseD && !caseC then
    if caseA then
      if aboveDist + Float.ofInt c > fl0p0 then
        moveBy := c
      else if belowDist - Float.ofInt a > fl0p0 then
        moveBy := a
    else if caseB then
      if aboveDist + Float.ofInt b > fl0p0 then
        moveBy := b
      else if belowDist - Float.ofInt d > fl0p0 then
        moveBy := d
  let mv := moveBy
  modifyNNode nNode.head fun n => { n with layer := n.layer + mv }
  if nNode.isFlexible then
    modifyNNode nNode.tail fun n => { n with layer := n.layer + mv }
  return false

/-- `postProcessTwoPaths()`: improves the two-paths in order; deferred ones afterwards in
reverse order. -/
private def postProcessTwoPaths : NspM Unit := do
  let queue ← modifyGet fun s => (s.twoPaths, { s with twoPaths := #[] })
  let mut stack : Array Path := #[]
  for path in queue do
    if (← improveTwoPath path true) then
      stack := stack.push path
  while !stack.isEmpty do
    let path := stack.back!
    stack := stack.pop
    let _ ← improveTwoPath path false

-- ============================================================================================
-- Result

/-- `adjustLabelPosition(placement, label, sizeDelta)`: bottom labels move with the bottom,
centred labels by half of it. -/
private def adjustLabelPosition (placement : EnumSet NodeLabelPlacement) (label : LLabelId) (sizeDelta : Float) :
    LayeredM Unit := do
  if placement.contains .vBottom then
    modifyLabel label fun l => { l with position := { l.position with y := l.position.y + sizeDelta } }
  else if placement.contains .vCenter then
    modifyLabel label fun l => { l with position := { l.position with y := l.position.y + sizeDelta / fl2p0 } }

/-- `applyPositions(graph)`: node y = layer of the head; flexible nodes also get their size,
east/west port positions, label and south port adjustments. -/
private def applyPositions : NspM Unit := do
  let s ← get
  let graphProps := s.graphProps
  let layers := (← getGraph s.graph).layers
  for layer in layers do
    for node in (← getLayer layer).nodes do
      let rep ← nodeRepOf node
      let minY := Float.ofInt (← nlayer rep.head)
      let maxY := Float.ofInt (← nlayer rep.tail)
      let nf := getNodeFlexibility graphProps (← getNode node)
      let flexibleNode ← isFlexibleNode graphProps node
      modifyNode node fun n => { n with position := { n.position with y := minY } }
      let sizeDelta := (maxY - minY) - (← getNode node).size.y
      if flexibleNode && nf.isFlexibleSizeWhereSpacePermits then
        modifyNode node fun n => { n with size := { n.size with y := n.size.y + sizeDelta } }
      if flexibleNode && nf.isFlexiblePorts then
        let nd ← getNode node
        for port in nd.ports do
          let side := (← getPort port).side
          if side == .east || side == .west then
            if let some nn := (← get).portMap.get? port then
              let layerVal := Float.ofInt (← nlayer nn)
              modifyPort port fun p => { p with position := { p.position with y := layerVal - minY } }
        let placement := nd.props.get LayeredOptions.NODE_LABELS_PLACEMENT |>.getD NodeLabelPlacement.fixed
        for label in nd.labels do
          adjustLabelPosition placement label sizeDelta
        if nf.isFlexibleSizeWhereSpacePermits then
          for port in (← withArena (·.nodePortSideView node .south)) do
            modifyPort port fun p => { p with position := { p.position with y := p.position.y + sizeDelta } }

/-- One network simplex run on the auxiliary graph (`forGraph … withIterationLimit …
withBalancing(false) … execute(monitor)`). -/
private def runNetworkSimplex (iterLimit : Int) (monitor : ProgressMonitor) : NspM Unit :=
  withNGraph fun g => do
    let ns := NetworkSimplex.forGraph g |>.withIterationLimit iterLimit |>.withBalancing false
    let g ← NetworkSimplex.execute ns monitor
    return (g, ())

/-- The body of `process` after the spacings check. -/
private def run (monitor : ProgressMonitor) : NspM Unit := do
  prepare
  buildInitialAuxiliaryGraph
  insertNorthSouthAuxiliaryEdges
  insertInLayerEdgeAuxiliaryEdges
  let graphProps := (← get).graphProps
  let favorStraightEdges := graphProps.get LayeredOptions.NODE_PLACEMENT_FAVOR_STRAIGHT_EDGES |>.getD false
  if favorStraightEdges then
    let pm ← monitor.subTask fl1p0
    let _ ← pm.begin "Straight Edges Pre-Processing" fl1p0
    preferStraightEdges
    pm.done
  withNGraph fun g => pure (g.makeConnected.1, ())
  let thoroughness := graphProps.get LayeredOptions.THOROUGHNESS |>.getD 7
  let iterLimit := Int.wrap32 (thoroughness * Int.wrap32 ((← get).nGraph.nodeList.size : Int))
  runNetworkSimplex iterLimit (← monitor.subTask fl1p0)
  let flexibleEdges := (← get).flexibleWhereSpacePermitsEdges
  if !flexibleEdges.isEmpty then
    let pm ← monitor.subTask fl1p0
    let _ ← pm.begin "Flexible Where Space Processing" fl1p0
    insertFlexibleWhereSpaceAuxiliaryEdges
    for edge in flexibleEdges do
      modifyNEdge edge fun e => { e with weight := NODE_SIZE_WEIGHT_FLEXIBLE }
    runNetworkSimplex iterLimit (← pm.subTask fl1p0)
    pm.done
  if favorStraightEdges then
    let pm ← monitor.subTask fl1p0
    let _ ← pm.begin "Straight Edges Post-Processing" fl1p0
    postProcessTwoPaths
    pm.done
  applyPositions

/-- `process(graph, monitor)` (Rust `NetworkSimplexPlacer::process`). -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Network simplex node placement" 1.0
  let gr ← getGraph graph
  let some spacings := gr.internal.spacings
    | throw (IO.userError "java.lang.IllegalStateException: Missing spacings configuration for network simplex node placement")
  let _ ← (run monitor).run { graph := graph, graphProps := gr.props, spacings := spacings }
  monitor.done

/-- The `NetworkSimplexPlacer` phase. -/
def phase : LayeredPhase :=
  { name := "NetworkSimplexPlacer"
    process := process
    getLayoutProcessorConfiguration := getLayoutProcessorConfiguration }

end NetworkSimplexPlacer

/-- Registers `NodePlacementStrategy.NETWORK_SIMPLEX` → `NetworkSimplexPlacer`. -/
builtin_initialize registerNetworkSimplexPlacer : Unit ←
  LayeredPhases.registerPhase .p4NodePlacement (ElkEnum.ordinal NodePlacementStrategy.networkSimplex)
    (pure NetworkSimplexPlacer.phase)

end Elk.Alg.Layered.P4Nodes
