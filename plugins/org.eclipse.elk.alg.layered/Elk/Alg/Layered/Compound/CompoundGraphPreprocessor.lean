import Std.Data.HashMap
import Elk.Core.Alg.LayoutProcessor
import Elk.Core.Util.ElkUtil
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Alg.Layered.Compound.CrossHierarchyEdgeComparator
import Elk.Alg.Layered.Compound.ExternalPort
/-!
# `org.eclipse.elk.alg.layered.compound.CompoundGraphPreprocessor`

Port of `CompoundGraphPreprocessor` of `compound/mod.rs` (elk-rs) and
`CompoundGraphPreprocessor.java`: splits every cross-hierarchy edge into hierarchy-local
segments connected through external port dummies (in the nested graphs) and ports on the
compound nodes. The segments are recorded in the cross-hierarchy map, which is stored in
`LGraphInternals.crossHierarchyMap` of the top-level graph; the labels of the original edges
move to the segments and the original edges are disconnected.

The graphs are processed bottom-up (`transformHierarchyEdges` recurses into the nested graph of
every layerless node first). Each level connects the external ports exported by its children
(`processInnerHierarchicalEdgeSegments`) and introduces its own external ports for edges
leaving its parent node (`processOuterHierarchicalEdgeSegments`), merging the edges of one port
into one external port if `MERGE_HIERARCHY_EDGES` is set.

Order notes: the Rust `dummy_node_map` (`HashMap<PortRefKey, LNodeRef>`) is only iterated by
`setSidesOfPortsToSidesOfDummyNodes`, whose per-entry updates are independent of each other;
this port iterates it in insertion order. The `ElkTrace` debug prints of the Rust code
(`[compound-pre]`, `[inside-self]`) are not ported.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.Layered.Compound

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace CompoundGraphPreprocessor

/-- The mutable state of a preprocessor run: the cross-hierarchy map and the Rust
`dummy_node_map` (port → external port dummy; insertion-ordered with a lookup index). -/
structure PreState where
  crossHierarchyMap : CrossHierarchyMap := #[]
  dummyNodeMap : Array (LPortId × LNodeId) := #[]
  dummyNodeIndex : Std.HashMap LPortId Nat := {}

/-- The preprocessor monad. -/
abbrev PreM := StateT PreState LayeredM

private def illegalState {α : Type} (msg : String) : PreM α :=
  throw (IO.userError s!"java.lang.IllegalStateException: {msg}")

/-- `crossHierarchyMap.put(origEdge, crossEdge)`. -/
def putCrossEdge (origEdge : LEdgeId) (crossEdge : CrossHierarchyEdge) : PreM Unit :=
  modify fun s => { s with crossHierarchyMap := CrossHierarchyMap.put s.crossHierarchyMap origEdge crossEdge }

/-- `dummyNodeMap.get(port)`. -/
def dummyFor? (port : LPortId) : PreM (Option LNodeId) := do
  let s ← get
  return (s.dummyNodeIndex[port]?).bind fun i => (s.dummyNodeMap[i]?).map (·.2)

/-- `dummyNodeMap.put(port, dummy)`. -/
def putDummy (port : LPortId) (dummy : LNodeId) : PreM Unit :=
  modify fun s =>
    match s.dummyNodeIndex[port]? with
    | some i => { s with dummyNodeMap := s.dummyNodeMap.set! i (port, dummy) }
    | none => { s with dummyNodeMap := s.dummyNodeMap.push (port, dummy),
                       dummyNodeIndex := s.dummyNodeIndex.insert port s.dummyNodeMap.size }

/-- Adds a flag to the graph's `GRAPH_PROPERTIES`. -/
def addGraphProperty (graph : LGraphId) (p : GraphProperties) : LayeredM Unit :=
  modifyGraph graph fun g => { g with internal := { g.internal with graphProperties := g.internal.graphProperties.insert p } }

/-- Rust `port_property_holder(port)`: a property holder with the port's `PORT_BORDER_OFFSET`,
`PORT_ANCHOR` and `PORT_INDEX` (where set). -/
def portPropertyHolder (port : LPortId) : LayeredM PropertyMap := do
  let pt ← getPort port
  let mut holder : PropertyMap := {}
  if let some v := pt.props.get LayeredOptions.PORT_BORDER_OFFSET then
    holder := holder.set LayeredOptions.PORT_BORDER_OFFSET v
  if let some v := pt.props.get LayeredOptions.PORT_ANCHOR then
    holder := holder.set LayeredOptions.PORT_ANCHOR v
  if let some v := pt.props.get LayeredOptions.PORT_INDEX then
    holder := holder.set LayeredOptions.PORT_INDEX v
  return holder

/-- Rust `create_external_port_properties(graph)`: `PORT_BORDER_OFFSET = SPACING_EDGE_EDGE / 2`. -/
def createExternalPortProperties (graph : LGraphId) : LayeredM PropertyMap := do
  let spacing := (← getGraph graph).props.getD LayeredOptions.SPACING_EDGE_EDGE 0.0
  return ({} : PropertyMap).set LayeredOptions.PORT_BORDER_OFFSET (spacing / 2.0)

/-- Rust `create_dummy_edge(orig_edge)` (Java `createDummyEdge`): a new edge with the original
edge's properties (public and internal), without `JUNCTION_POINTS`, with `ORIGIN` = the original
edge. -/
def createDummyEdge (origEdge : LEdgeId) : LayeredM LEdgeId := do
  let orig ← getEdge origEdge
  createEdge {
    props := orig.props.remove LayeredOptions.JUNCTION_POINTS,
    internal := { orig.internal with origin := some (.lEdge origEdge) } }

/-- The ends of an edge (Rust `unwrap`/`expect`). -/
private def edgeEnds (edge : LEdgeId) : PreM (LPortId × LPortId) := do
  let ed ← getEdge edge
  match ed.source, ed.target with
  | some s, some t => return (s, t)
  | _, _ => illegalState "edge missing endpoints"

/-- The first port of a dummy node (Rust `ports().first().cloned().unwrap()`). -/
private def firstPort (node : LNodeId) : PreM LPortId := do
  match (← getNode node).ports[0]? with
  | some p => return p
  | none => illegalState "external port dummy has a port"

/-- The owner of a port, if any. -/
private def ownerOf (port : LPortId) : LayeredM (Option LNodeId) := do
  return (← getPort port).owner

/-- The parent node of the graph containing `node` (Rust `node.graph().and_then(|g| g.parent_node())`). -/
private def parentNodeOfGraphOf (node : LNodeId) : LayeredM (Option LNodeId) := do
  match ← nodeGraph node with
  | some g => return (← getGraph g).parentNode
  | none => return none

/-- Rust `calculate_net_flow(port)`: output votes minus input votes of the port's edges, where
edges into the port's node's inside count reversed and inside self loops are treated
specially. -/
def calculateNetFlow (port : LPortId) : PreM Int := do
  let pt ← getPort port
  let some node := pt.owner | illegalState "port without node"
  let insideSelfLoopsEnabled := (← getNode node).props.getD CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false
  let mut outputPortVote : Int := 0
  let mut inputPortVote : Int := 0
  for outgoingEdge in pt.outgoingEdges do
    let ed ← getEdge outgoingEdge
    let isSelfLoop ← withArena (·.edgeIsSelfLoop outgoingEdge)
    let yo := ed.props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false
    let targetNode ← match ed.target with
      | some t => ownerOf t
      | none => pure none
    let isInsideSelfLoop := isSelfLoop && insideSelfLoopsEnabled && yo
    if isSelfLoop && isInsideSelfLoop then
      inputPortVote := inputPortVote + 1
    else if isSelfLoop && !isInsideSelfLoop then
      outputPortVote := outputPortVote + 1
    else if let some targetNode := targetNode then
      match ← parentNodeOfGraphOf targetNode with
      | some parent =>
        if parent == node then inputPortVote := inputPortVote + 1
        else outputPortVote := outputPortVote + 1
      | none => outputPortVote := outputPortVote + 1
    else
      outputPortVote := outputPortVote + 1
  for incomingEdge in pt.incomingEdges do
    let ed ← getEdge incomingEdge
    let isSelfLoop ← withArena (·.edgeIsSelfLoop incomingEdge)
    let yo := ed.props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false
    let sourceNode ← match ed.source with
      | some s => ownerOf s
      | none => pure none
    let isInsideSelfLoop := isSelfLoop && insideSelfLoopsEnabled && yo
    if isSelfLoop && isInsideSelfLoop then
      outputPortVote := outputPortVote + 1
    else if isSelfLoop && !isInsideSelfLoop then
      inputPortVote := inputPortVote + 1
    else if let some sourceNode := sourceNode then
      match ← parentNodeOfGraphOf sourceNode with
      | some parent =>
        if parent == node then outputPortVote := outputPortVote + 1
        else inputPortVote := inputPortVote + 1
      | none => inputPortVote := inputPortVote + 1
    else
      inputPortVote := inputPortVote + 1
  return outputPortVote - inputPortVote

/-- Rust `create_port_for_dummy(dummy_node, parent_node, port_type)`: a new port on the parent
node on the side given by the layout direction, with the dummy's `PORT_BORDER_OFFSET`. -/
def createPortForDummy (dummyNode parentNode : LNodeId) (portType : PortType) : PreM LPortId := do
  let some graph ← nodeGraph parentNode | illegalState "parent node without graph"
  let direction ← LGraphUtil.getDirection graph
  let port ← LayeredM.createPort
  setPortNode port (some parentNode)
  match portType with
  | .input => modifyPort port fun pt => pt.setSide (PortSide.fromDirection direction).opposed
  | .output => modifyPort port fun pt => pt.setSide (PortSide.fromDirection direction)
  | .undefined => pure ()
  let borderOffset := (← getNode dummyNode).props.getD LayeredOptions.PORT_BORDER_OFFSET 0.0
  setPortProp port LayeredOptions.PORT_BORDER_OFFSET borderOffset
  return port

/-- The `GRAPH_PROPERTIES`/`PORT_CONSTRAINTS` update after creating external ports in a graph:
`EXTERNAL_PORTS` is set and the port constraints become `FIXED_SIDE` (if side-fixed) or `FREE`. -/
private def markExternalPorts (graph : LGraphId) : LayeredM Unit := do
  addGraphProperty graph .externalPorts
  let graphConstraints := (← getGraph graph).props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  let newConstraints := if graphConstraints.isSideFixed then PortConstraints.fixedSide else PortConstraints.free
  setGraphProp graph LayeredOptions.PORT_CONSTRAINTS newConstraints

/-- Rust `create_external_port_dummy(graph, parent_node, port_type, port_side, edge)` (Java
`createExternalPortDummy`): the dummy for the edge's end outside the graph. For a port of the
parent node the dummy is shared per port (an existing dummy is returned immediately); for other
ends a new port is created on the parent node. The dummy is not yet added to the graph. -/
def createExternalPortDummyFor (graph : LGraphId) (parentNode : LNodeId) (portType : PortType)
    (portSide : PortSide) (edge : LEdgeId) : PreM LNodeId := do
  let (source, target) ← edgeEnds edge
  let outsidePort := if portType == .input then source else target
  let layoutDirection ← LGraphUtil.getDirection graph
  let isParentPort := (← ownerOf outsidePort) == some parentNode
  if isParentPort then
    -- an existing dummy is returned without touching the graph properties (Rust early return)
    if let some existing ← dummyFor? outsidePort then return existing
  let portConstraints := (← getNode parentNode).props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  let dummy ← if isParentPort then do
      let netFlow ← calculateNetFlow outsidePort
      let op ← getPort outsidePort
      let props ← portPropertyHolder outsidePort
      let (dummy, _) ← LGraphUtil.createExternalPortDummy props portConstraints portSide netFlow
        ⟨0.0, 0.0⟩ op.position op.size layoutDirection graph
      modifyNode dummy fun nd => { nd with internal := { nd.internal with origin := some (.lPort outsidePort) } }
      putDummy outsidePort dummy
      pure dummy
    else do
      let netFlow : Int := if portType == .input then -1 else 1
      let props ← createExternalPortProperties graph
      let (dummy, _) ← LGraphUtil.createExternalPortDummy props portConstraints portSide netFlow
        ⟨0.0, 0.0⟩ ⟨0.0, 0.0⟩ ⟨0.0, 0.0⟩ layoutDirection graph
      let dummyPort ← createPortForDummy dummy parentNode portType
      modifyNode dummy fun nd => { nd with internal := { nd.internal with origin := some (.lPort dummyPort) } }
      putDummy dummyPort dummy
      pure dummy
  markExternalPorts graph
  return dummy

/-- Rust `introduce_hierarchical_edge_segment(graph, parent_node, orig_edge, opposite_port,
port_type, default_external_port)`: either merges the edge into the default external port
(`created[defaultIdx]`, returned updated) or creates a new external port with its dummy and the
dummy edge segment. -/
def introduceHierarchicalEdgeSegment (graph : LGraphId) (parentNode : LNodeId) (origEdge : LEdgeId)
    (oppositePort : LPortId) (portType : PortType) (created : Array ExternalPort) (defaultIdx : Option Nat) :
    PreM (Array ExternalPort × Option ExternalPort) := do
  let mergeExternalPorts := (← getGraph graph).props.getD LayeredOptions.MERGE_HIERARCHY_EDGES true
  let orig ← getEdge origEdge
  let parentEndPort : Option LPortId ← match portType with
    | .input =>
      match orig.source with
      | some p => pure (if (← ownerOf p) == some parentNode then some p else none)
      | none => pure none
    | .output =>
      match orig.target with
      | some p => pure (if (← ownerOf p) == some parentNode then some p else none)
      | none => pure none
    | .undefined => pure none
  if mergeExternalPorts && parentEndPort.isNone then
    if let some idx := defaultIdx then
      if let some defaultPort := created[idx]? then
        let created := created.set! idx { defaultPort with origEdges := defaultPort.origEdges.push origEdge }
        let origThickness := orig.props.getD CoreOptions.EDGE_THICKNESS 1.0
        let existingThickness := (← getEdge defaultPort.newEdge).props.getD CoreOptions.EDGE_THICKNESS 1.0
        setEdgeProp defaultPort.newEdge CoreOptions.EDGE_THICKNESS (fmax existingThickness origThickness)
        putCrossEdge origEdge { edge := defaultPort.newEdge, graph, portType }
        return (created, none)
  let isSideFixed := ((← getNode parentNode).props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined).isSideFixed
  let portSide ← match parentEndPort with
    | some p => pure (← getPort p).side
    | none => pure (if isSideFixed then (if portType == .input then PortSide.west else PortSide.east) else PortSide.undefined)
  let dummyNode ← createExternalPortDummyFor graph parentNode portType portSide origEdge
  let dummyPort ← firstPort dummyNode
  let dummyEdge ← createDummyEdge origEdge
  if portType == .input then
    setEdgeSource dummyEdge (some dummyPort)
    setEdgeTarget dummyEdge (some oppositePort)
  else
    setEdgeSource dummyEdge (some oppositePort)
    setEdgeTarget dummyEdge (some dummyPort)
  let originPort := match (← getNode dummyNode).internal.origin with
    | some (.lPort p) => p
    | _ => oppositePort
  let externalPort := ExternalPort.new origEdge dummyEdge dummyNode originPort portType parentEndPort.isNone
  putCrossEdge origEdge { edge := dummyEdge, graph, portType }
  return (created, some externalPort)

/-- Rust `connect_child(graph, external_port, orig_edge, source_port, target_port)`: a dummy
edge between the two ports inside `graph`. -/
def connectChild (graph : LGraphId) (externalPort : ExternalPort) (origEdge : LEdgeId)
    (sourcePort targetPort : LPortId) : PreM Unit := do
  let dummyEdge ← createDummyEdge origEdge
  setEdgeSource dummyEdge (some sourcePort)
  setEdgeTarget dummyEdge (some targetPort)
  putCrossEdge origEdge { edge := dummyEdge, graph, portType := externalPort.portType }

/-- Rust `connect_siblings(graph, external_output_port, contained_external_ports, orig_edge)`:
a dummy edge from the output port to the (other) contained external port of the same edge.
`outputIdx` identifies the output port in `contained` (Rust compares references). -/
def connectSiblings (graph : LGraphId) (outputIdx : Nat) (contained : Array ExternalPort)
    (origEdge : LEdgeId) : PreM Unit := do
  let some output := contained[outputIdx]? | illegalState "target external port missing"
  let mut target : Option ExternalPort := none
  for i in [0:contained.size] do
    if i != outputIdx && contained[i]!.origEdges.contains origEdge then
      target := some contained[i]!
      break
  let some targetPort := target | illegalState "target external port missing"
  let dummyEdge ← createDummyEdge origEdge
  setEdgeSource dummyEdge (some output.dummyPort)
  setEdgeTarget dummyEdge (some targetPort.dummyPort)
  putCrossEdge origEdge { edge := dummyEdge, graph, portType := output.portType }

/-- Appends the dummies of the created external ports to the graph (once) and returns the
exported ones (shared tail of Rust `process_inner/outer_hierarchical_edge_segments`). -/
private def finishCreatedPorts (graph : LGraphId) (created : Array ExternalPort) : PreM (Array ExternalPort) := do
  let mut exported : Array ExternalPort := #[]
  for externalPort in created do
    let nodes := (← getGraph graph).layerlessNodes
    if !nodes.contains externalPort.dummyNode then
      modifyGraph graph fun g => { g with layerlessNodes := g.layerlessNodes.push externalPort.dummyNode }
    if externalPort.exported then exported := exported.push externalPort
  return exported

/-- Records a created external port: pushes it and returns the new "current" index if it is
exported (Rust `if created[idx].exported { current = Some(idx) }`). -/
private def recordCreated (created : Array ExternalPort) (current : Option Nat) (newPort : Option ExternalPort) :
    Array ExternalPort × Option Nat :=
  match newPort with
  | some p => (created.push p, if p.exported then some created.size else current)
  | none => (created, current)

/-- Rust `process_inner_hierarchical_edge_segments(graph, parent_node, contained_external_ports,
exported_external_ports)`: connects the external ports exported by the child graphs (children
to nodes of this graph, siblings to each other, or further out through new external ports of
this graph). Returns the newly exported external ports. -/
def processInnerHierarchicalEdgeSegments (graph : LGraphId) (parentNode : Option LNodeId)
    (contained : Array ExternalPort) : PreM (Array ExternalPort) := do
  let mut created : Array ExternalPort := #[]
  for i in [0:contained.size] do
    let externalPort := contained[i]!
    let mut current : Option Nat := none
    if externalPort.portType == .output then
      for outEdge in externalPort.origEdges do
        let some targetPort := (← getEdge outEdge).target | continue
        let some targetNode ← ownerOf targetPort | continue
        let some targetGraph ← nodeGraph targetNode | continue
        if targetGraph == graph then
          connectChild graph externalPort outEdge externalPort.dummyPort targetPort
        else if (← match parentNode with
            | some parent => LGraphUtil.isDescendant targetNode parent
            | none => pure true) then
          connectSiblings graph i contained outEdge
        else
          let some parent := parentNode | continue
          let (c, newPort) ← introduceHierarchicalEdgeSegment graph parent outEdge externalPort.dummyPort .output created current
          (created, current) := recordCreated c current newPort
    else
      for inEdge in externalPort.origEdges do
        let some sourcePort := (← getEdge inEdge).source | continue
        let some sourceNode ← ownerOf sourcePort | continue
        let some sourceGraph ← nodeGraph sourceNode | continue
        if sourceGraph == graph then
          connectChild graph externalPort inEdge sourcePort externalPort.dummyPort
        else if (← match parentNode with
            | some parent => LGraphUtil.isDescendant sourceNode parent
            | none => pure true) then
          continue
        else
          let some parent := parentNode | continue
          let (c, newPort) ← introduceHierarchicalEdgeSegment graph parent inEdge externalPort.dummyPort .input created current
          (created, current) := recordCreated c current newPort
  finishCreatedPorts graph created

/-- Rust `process_outer_hierarchical_edge_segments(graph, parent_node, exported_external_ports)`:
introduces external ports for the edges of the graph's nodes that leave the parent node.
Returns the exported external ports. -/
def processOuterHierarchicalEdgeSegments (graph : LGraphId) (parentNode : LNodeId) : PreM (Array ExternalPort) := do
  let childNodes := (← getGraph graph).layerlessNodes
  let mut created : Array ExternalPort := #[]
  for childNode in childNodes do
    for childPort in (← getNode childNode).ports do
      let pt ← getPort childPort
      let outgoingEdges := pt.outgoingEdges
      let incomingEdges := pt.incomingEdges
      let mut currentOutput : Option Nat := none
      for outEdge in outgoingEdges do
        let ed ← getEdge outEdge
        let some targetPort := ed.target | continue
        let some targetNode ← ownerOf targetPort | continue
        if !(← LGraphUtil.isDescendant targetNode parentNode) then
          let some oppositePort := ed.source | illegalState "edge missing endpoints"
          let (c, newPort) ← introduceHierarchicalEdgeSegment graph parentNode outEdge oppositePort .output created currentOutput
          (created, currentOutput) := recordCreated c currentOutput newPort
      let mut currentInput : Option Nat := none
      for inEdge in incomingEdges do
        let ed ← getEdge inEdge
        let some sourcePort := ed.source | continue
        let some sourceNode ← ownerOf sourcePort | continue
        if !(← LGraphUtil.isDescendant sourceNode parentNode) then
          let some oppositePort := ed.target | illegalState "edge missing endpoints"
          let (c, newPort) ← introduceHierarchicalEdgeSegment graph parentNode inEdge oppositePort .input created currentInput
          (created, currentInput) := recordCreated c currentInput newPort
  finishCreatedPorts graph created

/-- Rust `ensure_external_port_dummy(graph, port, fallback_constraints, net_flow)`: the (shared)
external port dummy of a port of the compound node for inside self loops; new dummies are added
to the graph. -/
def ensureExternalPortDummy (graph : LGraphId) (port : LPortId) (fallbackConstraints : PortConstraints)
    (netFlow : Int) : PreM LNodeId := do
  if let some existing ← dummyFor? port then return existing
  let pt ← getPort port
  let direction ← LGraphUtil.getDirection graph
  let props ← portPropertyHolder port
  -- Java inside-self-loop path uses PortConstraints.FREE with null position/node-size context.
  let (dummy, _) ← LGraphUtil.createExternalPortDummy props fallbackConstraints pt.side netFlow
    ⟨0.0, 0.0⟩ ⟨0.0, 0.0⟩ pt.size direction graph
  modifyNode dummy fun nd => { nd with internal := { nd.internal with origin := some (.lPort port) } }
  putDummy port dummy
  modifyGraph graph fun g => { g with layerlessNodes := g.layerlessNodes.push dummy }
  markExternalPorts graph
  return dummy

/-- Rust `process_inside_self_loops(nested_graph, node)`: inside self loops of a compound node
(`INSIDE_SELF_LOOPS_ACTIVATE` on the node, `INSIDE_SELF_LOOPS_YO` on the edge) are routed
through external port dummies of the nested graph. -/
def processInsideSelfLoops (nestedGraph : LGraphId) (node : LNodeId) : PreM Unit := do
  let nd ← getNode node
  if !nd.props.getD CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false then return
  for port in nd.ports do
    for outEdge in (← getPort port).outgoingEdges do
      let isSelfLoop ← withArena (·.edgeIsSelfLoop outEdge)
      let insideSelfLoop := isSelfLoop && (← getEdge outEdge).props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false
      if !isSelfLoop || !insideSelfLoop then continue
      let (sourcePort, targetPort) ← edgeEnds outEdge
      let sourceDummy ← ensureExternalPortDummy nestedGraph sourcePort .free (-1)
      let targetDummy ← ensureExternalPortDummy nestedGraph targetPort .free 1
      let dummyEdge ← createDummyEdge outEdge
      let sourcePortDummy ← firstPort sourceDummy
      let targetPortDummy ← firstPort targetDummy
      setEdgeSource dummyEdge (some sourcePortDummy)
      setEdgeTarget dummyEdge (some targetPortDummy)
      putCrossEdge outEdge { edge := dummyEdge, graph := nestedGraph, portType := .output }
      addGraphProperty nestedGraph .externalPorts

/-- The external port dummies (and their port labels) of the ports of a compound node whose
nested graph has external ports (the `has_external_ports` block of Rust
`transform_hierarchy_edges`). -/
private def createPortDummiesOfCompoundNode (nestedGraph : LGraphId) (node : LNodeId) : PreM Unit := do
  let nd ← getNode node
  let portConstraints := nd.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  let portLabelPlacement := nd.props.getD CoreOptions.PORT_LABELS_PLACEMENT PortLabelPlacement.outsideSet
  let insidePortLabels := portLabelPlacement.contains .inside
  let direction ← LGraphUtil.getDirection nestedGraph
  for port in nd.ports do
    let mut existingDummy ← dummyFor? port
    if existingDummy.isNone then
      let pt ← getPort port
      let props ← portPropertyHolder port
      let (dummy, _) ← LGraphUtil.createExternalPortDummy props portConstraints pt.side (-pt.netFlow)
        ⟨fl0p0, fl0p0⟩ ⟨fl0p0, fl0p0⟩ pt.size direction nestedGraph
      modifyNode dummy fun x => { x with internal := { x.internal with origin := some (.lPort port) } }
      putDummy port dummy
      modifyGraph nestedGraph fun g => { g with layerlessNodes := g.layerlessNodes.push dummy }
      existingDummy := some dummy
    let some dummyNode := existingDummy | continue
    let some dummyPort := (← getNode dummyNode).ports[0]? | continue
    let pt ← getPort port
    let portSize := pt.size
    let portSide := pt.side
    for label in pt.labels do
      let lb ← getLabel label
      let labelSize := lb.size
      let labelPos := lb.position
      let mut dummySize := labelSize
      if !insidePortLabels then
        let mut insidePart := fl0p0
        if PortLabelPlacement.isFixed portLabelPlacement then
          insidePart := ElkUtil.computeInsidePart labelPos labelSize portSize fl0p0 portSide
        if portConstraints == .free || portSide == .east || portSide == .west then
          dummySize := { dummySize with x := insidePart }
        else
          dummySize := { dummySize with y := insidePart }
      let dummyLabel ← createLabel "" { size := dummySize }
      modifyPort dummyPort fun p => { p with labels := p.labels.push dummyLabel }

/-- Rust `transform_hierarchy_edges(graph, parent_node)`: processes the nested graphs first
(bottom-up), then the inner and outer hierarchical edge segments of this graph. Returns the
external ports exported to the parent level. Recursion over the (finite) nesting hierarchy. -/
partial def transformHierarchyEdges (graph : LGraphId) (parentNode : Option LNodeId) : PreM (Array ExternalPort) := do
  let layerlessNodes := (← getGraph graph).layerlessNodes
  let mut containedExternalPorts : Array ExternalPort := #[]
  for node in layerlessNodes do
    if let some nestedGraph := (← getNode node).nestedGraph then
      let childPorts ← transformHierarchyEdges nestedGraph (some node)
      containedExternalPorts := containedExternalPorts ++ childPorts
      processInsideSelfLoops nestedGraph node
      if (← getGraph nestedGraph).internal.graphProperties.contains .externalPorts then
        createPortDummiesOfCompoundNode nestedGraph node
  let mut exportedExternalPorts ← processInnerHierarchicalEdgeSegments graph parentNode containedExternalPorts
  if let some parent := parentNode then
    exportedExternalPorts := exportedExternalPorts ++ (← processOuterHierarchicalEdgeSegments graph parent)
  return exportedExternalPorts

/-- Rust `get_shallowest_edge_segment(edge_segments)`: the index of the last `OUTPUT` segment
before the first `INPUT` segment (or the last segment). -/
def getShallowestEdgeSegment (edgeSegments : Array CrossHierarchyEdge) : Nat := Id.run do
  let mut result := 0
  for index in [0:edgeSegments.size] do
    if edgeSegments[index]!.portType == .input then
      result := if index == 0 then 0 else index - 1
      break
    else if index == edgeSegments.size - 1 then
      result := index
  return result

/-- Rust `move_labels_and_remove_original_edges(graph, cross_hierarchy_map)`: moves the labels
of every original edge to its segments (`HEAD` → last, `TAIL` → first, `CENTER` → the
shallowest segment), marks them with `ORIGINAL_LABEL_EDGE` and disconnects the original edge. -/
def moveLabelsAndRemoveOriginalEdges (graph : LGraphId) : PreM Unit := do
  let crossMap := (← get).crossHierarchyMap
  for origEdge in CrossHierarchyMap.keys crossMap do
    let labels := (← getEdge origEdge).labels
    if !labels.isEmpty then
      let edgeSegments ← CrossHierarchyEdgeComparator.sortCrossHierarchyEdges (CrossHierarchyMap.get crossMap origEdge) graph
      let mut labelMoves : Array (LLabelId × Nat) := #[]
      for label in labels do
        let placement := (← getLabel label).props.getD LayeredOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.center
        let targetIndex := match placement with
          | .head => edgeSegments.size - 1
          | .center => getShallowestEdgeSegment edgeSegments
          | .tail => 0
        labelMoves := labelMoves.push (label, targetIndex)
        modifyLabel label fun lb => { lb with internal := { lb.internal with originalLabelEdge := some origEdge } }
      modifyEdge origEdge fun e => { e with labels := #[] }
      for (label, targetIndex) in labelMoves do
        if let some targetSegment := edgeSegments[targetIndex]? then
          modifyEdge targetSegment.edge fun e => { e with labels := e.labels.push label }
          let source := (← getEdge targetSegment.edge).source
          let graphRef ← match source with
            | some p => do
              match ← ownerOf p with
              | some n => nodeGraph n
              | none => pure none
            | none => pure none
          if let some g := graphRef then
            addGraphProperty g .endLabels
            addGraphProperty g .centerLabels
    setEdgeSource origEdge none
    setEdgeTarget origEdge none

/-- Rust `set_sides_of_ports_to_sides_of_dummy_nodes(dummy_node_map)`: every port represented
by an external port dummy gets the dummy's side, `PORT_DUMMY` and `INSIDE_CONNECTIONS`; its node
gets `FIXED_SIDE` port constraints and its graph `NON_FREE_PORTS`. -/
def setSidesOfPortsToSidesOfDummyNodes : PreM Unit := do
  for (externalPort, dummyNode) in (← get).dummyNodeMap do
    modifyNode dummyNode fun nd => { nd with internal := { nd.internal with origin := some (.lPort externalPort) } }
    let dummySide := (← getNode dummyNode).internal.extPortSide
    modifyPort externalPort fun pt =>
      let pt := { pt with internal := { pt.internal with portDummy := some dummyNode, insideConnections := true } }
      pt.setSide dummySide
    let some node ← ownerOf externalPort | continue
    let nodeGraphId ← nodeGraph node
    setNodeProp node LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
    if let some g := nodeGraphId then
      addGraphProperty g .nonFreePorts

/-- `process(graph, progressMonitor)` (Rust `process_with_ref`). -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  discard <| monitor.begin "Compound graph preprocessor" 1.0
  let run : PreM Unit := do
    discard <| transformHierarchyEdges graph none
    moveLabelsAndRemoveOriginalEdges graph
    setSidesOfPortsToSidesOfDummyNodes
  let ((), st) ← run.run {}
  let crossMap := st.crossHierarchyMap
  modifyGraph graph fun g => { g with internal := { g.internal with crossHierarchyMap := crossMap } }
  monitor.done

end CompoundGraphPreprocessor

/-- `new CompoundGraphPreprocessor()` as a layout processor. -/
def CompoundGraphPreprocessor.processor : LayoutProcessor LayeredM LGraphId where
  name := "CompoundGraphPreprocessor"
  process := CompoundGraphPreprocessor.process

end Elk.Alg.Layered.Compound
