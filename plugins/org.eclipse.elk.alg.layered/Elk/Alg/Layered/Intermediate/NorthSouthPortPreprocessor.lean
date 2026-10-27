import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.NorthSouthPortPreprocessor`

Port of elk-rs `intermediate/north_south_port_preprocessor.rs`. Inserts `NORTH_SOUTH_PORT` dummy
nodes for the north and south ports of normal nodes with fixed port sides: north dummies are
inserted before the node, south dummies after it (all in the node's layer); the node and its
dummies form one in-layer layout unit (`IN_LAYER_LAYOUT_UNIT = node`), north dummies get the node
as in-layer successor and the node gets the south dummies as successors (unless the origin port
allows switching sides). The dummies become the node's `BARYCENTER_ASSOCIATES`.

Rust behaviour followed here (deviations from Java):
* `sort_port_list` runs for **every** node whose port constraints do not fix the order (when no
  model order strategy is set), before the node type / side check; it does not write the ports'
  `id` fields and does not cache the port sides of nodes with at most one port;
* `origin_port_allows_switch` also returns `false` when the origin port's `PORT_CONSTRAINTS`
  (falling back to its node's) fix the positions;
* `CROSSING_HINT` is not set on the dummies (elk-rs has no such property);
* the `[north-south-pre]` debug trace is omitted.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace NorthSouthPortPreprocessor

/-- Comparator of `sort_port_list` on `(input index, port, side, id)`: side ordinal, then for equal
ids the input index, then ascending ids on the north side and descending ids elsewhere. -/
private def compareSortEntries (l r : Nat × LPortId × PortSide × Int) : Ordering :=
  let (indexLeft, _, sideLeft, idLeft) := l
  let (indexRight, _, sideRight, idRight) := r
  if sideLeft != sideRight then compare (ElkEnum.ordinal sideLeft) (ElkEnum.ordinal sideRight)
  else if idLeft == idRight then compare indexLeft indexRight
  else if sideLeft == .north then compare idLeft idRight
  else compare idRight idLeft

/-- `sort_port_list(node)` (Java `sortPortList`): sorts the ports by side; north/south ports are
ordered input-only, then in/out, then output-only (left to right in the diagram), and the port
sides are cached. Nodes with at most one port are left untouched. -/
def sortPortList (node : LNodeId) : LayeredM Unit := do
  let ports := (← getNode node).ports
  if ports.size <= 1 then return
  let mut entries : Array (Nat × LPortId × PortSide × Int) := #[]
  let mut inPorts : Int := 0
  let mut inOutPorts : Int := ports.size
  let mut outPorts : Int := 2 * ports.size
  for h : index in [0:ports.size] do
    let port := ports[index]
    let pt ← getPort port
    let side := pt.side
    let incoming := !pt.incomingEdges.isEmpty
    let outgoing := !pt.outgoingEdges.isEmpty
    let mut id : Int := -1
    if side == .north || side == .south then
      if incoming && outgoing then
        id := inOutPorts
        inOutPorts := inOutPorts + 1
      else if incoming then
        id := inPorts
        inPorts := inPorts + 1
      else if outgoing then
        id := outPorts
        outPorts := outPorts + 1
      else
        id := inPorts
        inPorts := inPorts + 1
    entries := entries.push (index, port, side, id)
  let sorted := stableSort entries compareSortEntries
  modifyNode node fun n => { n with ports := sorted.map (·.2.1) }
  cachePortSides node

/-- `model_order_north_south_input_reversing(ports)` (Java `modelOrderNorthSouthInputReversing`):
the ports with incoming edges in reverse order, followed by the others in order. -/
def modelOrderNorthSouthInputReversing (ports : Array LPortId) : LayeredM (Array LPortId) := do
  let mut incomingPorts : Array LPortId := #[]
  let mut outgoingPorts : Array LPortId := #[]
  for port in ports do
    if !(← getPort port).incomingEdges.isEmpty then
      incomingPorts := incomingPorts.push port
    else
      outgoingPorts := outgoingPorts.push port
  return incomingPorts.reverse ++ outgoingPorts

/-- A `NORTH_SOUTH_PORT` dummy with `FIXED_POS` port constraints (`LNode::new` + type +
`PORT_CONSTRAINTS`). -/
private def newDummy (graph : LGraphId) : LayeredM LNodeId := do
  let dummy ← createNode graph { type := .northSouthPort }
  setNodeProp dummy LayeredOptions.PORT_CONSTRAINTS PortConstraints.fixedPos
  return dummy

/-- A new port with `ORIGIN = origin` on `side`, attached to `node`. -/
private def newOriginPort (node : LNodeId) (origin : LPortId) (side : PortSide) : LayeredM LPortId := do
  let port ← LayeredM.createPort
  modifyPort port fun p =>
    let p := { p with internal := { p.internal with origin := some (.lPort origin) } }
    p.setSide side
  setPortNode port (some node)
  return port

/-- Sets `PORT_DUMMY` of a port. -/
private def setPortDummy (port : LPortId) (dummy : LNodeId) : LayeredM Unit :=
  modifyPort port fun p => { p with internal := { p.internal with portDummy := some dummy } }

/-- Sets `ORIGIN` of a node to the owner of `port` (when it has one). -/
private def setOriginToOwner (dummy : LNodeId) (port : LPortId) : LayeredM Unit := do
  if let some node := (← getPort port).owner then
    modifyNode dummy fun d => { d with internal := { d.internal with origin := some (.lNode node) } }

/-- `create_dummy_node(graph, in_port, out_port, dummy_nodes)` (Java `createDummyNode`): a dummy
with a western input port taking over the incoming edges of `inPort` and/or an eastern output
port taking over the outgoing edges of `outPort`; appended to the returned list. -/
def createDummyNode (graph : LGraphId) (inPort outPort : Option LPortId) (dummyNodes : Array LNodeId) :
    LayeredM (LNodeId × Array LNodeId) := do
  let dummy ← newDummy graph
  if let some inPort := inPort then
    let dummyInputPort ← newOriginPort dummy inPort .west
    for edge in (← getPort inPort).incomingEdges do
      setEdgeTarget edge (some dummyInputPort)
    setPortDummy inPort dummy
    setOriginToOwner dummy inPort
  if let some outPort := outPort then
    let dummyOutputPort ← newOriginPort dummy outPort .east
    for edge in (← getPort outPort).outgoingEdges do
      setEdgeSource edge (some dummyOutputPort)
    setPortDummy outPort dummy
    setOriginToOwner dummy outPort
  return (dummy, dummyNodes.push dummy)

/-- `create_same_side_self_loop_dummy_node(graph, self_loop, dummy_nodes)` (Java
`createSameSideSelfLoopDummyNode`): one dummy with `ORIGIN = self_loop` whose input/output ports
originate from the loop's target/source port; the loop is disconnected. -/
def createSameSideSelfLoopDummyNode (graph : LGraphId) (selfLoop : LEdgeId) (dummyNodes : Array LNodeId) :
    LayeredM (Array LNodeId) := do
  let ed ← getEdge selfLoop
  let (some sourcePort, some targetPort) := (ed.source, ed.target) | return dummyNodes
  let dummy ← newDummy graph
  modifyNode dummy fun d => { d with internal := { d.internal with origin := some (.lEdge selfLoop) } }
  let _ ← newOriginPort dummy targetPort .west
  let _ ← newOriginPort dummy sourcePort .east
  setPortDummy sourcePort dummy
  setPortDummy targetPort dummy
  setEdgeSource selfLoop none
  setEdgeTarget selfLoop none
  return dummyNodes.push dummy

/-- `create_north_south_self_loop_dummy_nodes(graph, self_loop, north_dummy_nodes,
south_dummy_nodes, side)` (Java `createNorthSouthSelfLoopDummyNodes`): a north dummy (prepended)
with an output port and a south dummy (appended) with an input port, both on `side`; the loop is
rerouted between them. -/
def createNorthSouthSelfLoopDummyNodes (graph : LGraphId) (selfLoop : LEdgeId)
    (northDummyNodes southDummyNodes : Array LNodeId) (side : PortSide) :
    LayeredM (Array LNodeId × Array LNodeId) := do
  let ed ← getEdge selfLoop
  let (some sourcePort, some targetPort) := (ed.source, ed.target) | return (northDummyNodes, southDummyNodes)
  let northDummy ← newDummy graph
  setOriginToOwner northDummy sourcePort
  let northDummyOutputPort ← newOriginPort northDummy sourcePort side
  setPortDummy sourcePort northDummy
  let southDummy ← newDummy graph
  setOriginToOwner southDummy targetPort
  let southDummyInputPort ← newOriginPort southDummy targetPort side
  setPortDummy targetPort southDummy
  setEdgeSource selfLoop (some northDummyOutputPort)
  setEdgeTarget selfLoop (some southDummyInputPort)
  return (#[northDummy] ++ northDummyNodes, southDummyNodes.push southDummy)

/-- First pass of `create_dummy_nodes`: the outgoing self loops of `ports` that stay on the same
side and those that go from north to south. -/
private def collectSelfLoops (ports : Array LPortId) : LayeredM (Array LEdgeId × Array LEdgeId) := do
  let mut sameSideSelfLoopEdges : Array LEdgeId := #[]
  let mut northSouthSelfLoopEdges : Array LEdgeId := #[]
  for port in ports do
    let portSide := (← getPort port).side
    for edge in (← getPort port).outgoingEdges do
      let ed ← getEdge edge
      let (some sourcePort, some targetPort) := (ed.source, ed.target) | continue
      let (some sourceNode, some targetNode) := ((← getPort sourcePort).owner, (← getPort targetPort).owner) | continue
      if sourceNode != targetNode then continue
      let targetSide := (← getPort targetPort).side
      if portSide == targetSide then
        sameSideSelfLoopEdges := sameSideSelfLoopEdges.push edge
      else if portSide == .north && targetSide == .south then
        northSouthSelfLoopEdges := northSouthSelfLoopEdges.push edge
  return (sameSideSelfLoopEdges, northSouthSelfLoopEdges)

/-- `create_dummy_nodes(graph, ports, dummy_nodes, opposing_side_dummy_nodes,
barycenter_associates)` (Java `createDummyNodes`, new approach): north→south self loops (only
when an opposing list is given), same-side self loops, then one dummy per input-only, output-only
and in/out port (in that order; these become barycenter associates). Returns the updated
`(dummyNodes, opposingSideDummyNodes, barycenterAssociates)`. -/
def createDummyNodes (graph : LGraphId) (ports : Array LPortId) (dummyNodes : Array LNodeId)
    (opposingSideDummyNodes : Option (Array LNodeId)) (barycenterAssociates : Array LNodeId) :
    LayeredM (Array LNodeId × Option (Array LNodeId) × Array LNodeId) := do
  let mut dummies := dummyNodes
  let mut opposing := opposingSideDummyNodes
  let mut associates := barycenterAssociates
  let (sameSideSelfLoopEdges, northSouthSelfLoopEdges) ← collectSelfLoops ports
  for edge in northSouthSelfLoopEdges do
    if let some opp := opposing then
      let (d, o) ← createNorthSouthSelfLoopDummyNodes graph edge dummies opp .east
      dummies := d
      opposing := some o
  for edge in sameSideSelfLoopEdges do
    dummies ← createSameSideSelfLoopDummyNode graph edge dummies
  let mut inPorts : Array LPortId := #[]
  let mut outPorts : Array LPortId := #[]
  let mut inOutPorts : Array LPortId := #[]
  for port in ports do
    let pt ← getPort port
    let hasIn := !pt.incomingEdges.isEmpty
    let hasOut := !pt.outgoingEdges.isEmpty
    if hasIn && hasOut then inOutPorts := inOutPorts.push port
    else if hasIn then inPorts := inPorts.push port
    else if hasOut then outPorts := outPorts.push port
  for inPort in inPorts do
    let (dummy, d) ← createDummyNode graph (some inPort) none dummies
    dummies := d
    associates := associates.push dummy
  for outPort in outPorts do
    let (dummy, d) ← createDummyNode graph none (some outPort) dummies
    dummies := d
    associates := associates.push dummy
  for inOutPort in inOutPorts do
    let (dummy, d) ← createDummyNode graph (some inOutPort) (some inOutPort) dummies
    dummies := d
    associates := associates.push dummy
  return (dummies, opposing, associates)

/-- `origin_port_allows_switch(dummy)`: whether the origin port of the dummy's first port allows
non-flow ports to switch sides (never when its port constraints fix positions). -/
def originPortAllowsSwitch (dummy : LNodeId) : LayeredM Bool := do
  let some firstPort := (← getNode dummy).ports[0]? | return false
  let some (Origin.lPort originPort) := (← getPort firstPort).internal.origin | return false
  let op ← getPort originPort
  let allowsSwitch := op.props.getD LayeredOptions.ALLOW_NON_FLOW_PORTS_TO_SWITCH_SIDES false
  let portConstraints ← match op.props.get LayeredOptions.PORT_CONSTRAINTS with
    | some pc => pure pc
    | none => match op.owner with
      | some node => pure ((← getNode node).props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined)
      | none => pure PortConstraints.undefined
  if portConstraints.isPosFixed then return false
  return allowsSwitch

/-- Appends a node to the `IN_LAYER_SUCCESSOR_CONSTRAINTS` of another. -/
private def addSuccessorConstraint (node successor : LNodeId) : LayeredM Unit :=
  modifyNode node fun n => { n with internal := { n.internal with
    inLayerSuccessorConstraints := n.internal.inLayerSuccessorConstraints.push successor } }

/-- Sets `IN_LAYER_LAYOUT_UNIT` of a node. -/
private def setLayoutUnit (node unit : LNodeId) : LayeredM Unit :=
  modifyNode node fun n => { n with internal := { n.internal with inLayerLayoutUnit := some unit } }

/-- The per-node body of `process`: returns the updated layer pointer. -/
private def processNode (layer : LayerId) (node : LNodeId) (pointer : Int) : LayeredM Int := do
  let mut pointer := pointer
  let nd ← getNode node
  let nodeType := nd.type
  let portConstraints := nd.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
  let modelOrderStrategy ← match ← nodeGraph node with
    | some g => pure ((← getGraph g).props.getD LayeredOptions.CONSIDER_MODEL_ORDER_STRATEGY OrderingStrategy.none)
    | none => pure OrderingStrategy.none
  if !portConstraints.isOrderFixed && modelOrderStrategy == .none then
    sortPortList node
  let mut northPorts ← withArena (·.nodePortsBySide node .north)
  let mut southPorts ← withArena (·.nodePortsBySide node .south)
  if modelOrderStrategy != .none then
    northPorts ← modelOrderNorthSouthInputReversing northPorts
  southPorts := southPorts.reverse
  if modelOrderStrategy != .none then
    southPorts ← modelOrderNorthSouthInputReversing southPorts
  let graphRef ← nodeGraph node
  if nodeType != .normal || !portConstraints.isSideFixed then return pointer
  let some graph := graphRef | return pointer
  setLayoutUnit node node
  if northPorts.isEmpty && southPorts.isEmpty then return pointer
  let (northDummyNodes, southFromNorth, barycenterAssociates) ←
    createDummyNodes graph northPorts #[] (some #[]) #[]
  let (southDummyNodes, _, barycenterAssociates) ←
    createDummyNodes graph southPorts (southFromNorth.getD #[]) none barycenterAssociates
  let insertPoint := pointer.toNat
  for dummy in northDummyNodes do
    setNodeLayerAtIndex dummy insertPoint (some layer)
    pointer := pointer + 1
    setLayoutUnit dummy node
    if !(← originPortAllowsSwitch dummy) then
      addSuccessorConstraint dummy node
  for dummy in southDummyNodes do
    setNodeLayerAtIndex dummy (pointer + 1).toNat (some layer)
    pointer := pointer + 1
    setLayoutUnit dummy node
    if !(← originPortAllowsSwitch dummy) then
      addSuccessorConstraint node dummy
  if !barycenterAssociates.isEmpty then
    modifyNode node fun n => { n with internal := { n.internal with barycenterAssociates := barycenterAssociates } }
  return pointer

/-- `process(graph, monitor)`: per layer over a copy of its node list; `pointer` is the index of
the current node while north dummies are inserted and of the last inserted south dummy after. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Odd port side processing" 1.0
  for layer in (← getGraph graph).layers do
    let nodeArray := (← getLayer layer).nodes
    let mut pointer : Int := -1
    for node in nodeArray do
      pointer := pointer + 1
      pointer ← processNode layer node pointer
  monitor.done

/-- The `NorthSouthPortPreprocessor` processor. -/
def processor : LayeredProcessor := { name := "NorthSouthPortPreprocessor", process := process }

end NorthSouthPortPreprocessor

builtin_initialize registerNorthSouthPortPreprocessor : Unit ←
  IntermediateProcessorStrategy.register .northSouthPortPreprocessor NorthSouthPortPreprocessor.processor

end Elk.Alg.Layered.Intermediate
