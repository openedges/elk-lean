import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.CommentPreprocessor`

Port of elk-rs `intermediate/comment_preprocessor.rs`. Comment boxes (`COMMENT_BOX`) connected by exactly
one edge to a port of degree one of a non-comment node are removed from the layerless nodes and attached
to that node: they are appended to its `TOP_COMMENTS` or `BOTTOM_COMMENTS`, remember the opposite port
(`COMMENT_CONN_PORT`), and the edge is detached from the opposite port (which is removed from its node when
it has no edges left; a hierarchical port dummy behind it is removed from its layer) and loses its bend
points. Other comment boxes get their oddly connected edges reversed (outgoing edges into ports with
outgoing edges, incoming edges from ports with incoming edges).

Side choice (`choose_comment_side`): with fixed port sides, ports connected to non-comment nodes decide
(`onlyTop` when there are southern but no northern connections, `onlyBottom` vice versa); otherwise the
mean label centre decides (`topFirst` when it is in the lower half); the box goes to the preferred side
unless the other side has fewer boxes.

Rust/Java parity notes (follows Rust): Java stops the port scan at the first southern connection too
(Rust keeps scanning for a northern one); Rust's `has_property(TOP_COMMENTS)` is "non-empty" here since
the lists only ever grow.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Options Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace CommentPreprocessor

/-- Rust `is_comment_box`: `COMMENT_BOX` set and `true`. -/
def isCommentBox (node : LNodeId) : LayeredM Bool := do
  let props := (← getNode node).props
  return props.has LayeredOptions.COMMENT_BOX && props.getD LayeredOptions.COMMENT_BOX false

/-- Whether the owner of a port is a comment box (`false` without owner). -/
def portOwnerIsCommentBox (port : LPortId) : LayeredM Bool := do
  match (← getPort port).owner with
  | some owner => isCommentBox owner
  | none => return false

/-- `reverseOddlyConnectedEdges(commentNode)`: collects (port order; outgoing then incoming) the edges
whose far port has edges in the "wrong" direction and reverses them in the comment's graph. -/
def reverseOddlyConnectedEdges (commentNode : LNodeId) : LayeredM Unit := do
  let mut reversedEdges : Array LEdgeId := #[]
  for port in (← getNode commentNode).ports do
    let pt ← getPort port
    for outEdge in pt.outgoingEdges do
      if let some targetPort := (← getEdge outEdge).target then
        if !(← getPort targetPort).outgoingEdges.isEmpty then reversedEdges := reversedEdges.push outEdge
    for inEdge in pt.incomingEdges do
      if let some sourcePort := (← getEdge inEdge).source then
        if !(← getPort sourcePort).incomingEdges.isEmpty then reversedEdges := reversedEdges.push inEdge
  if let some graph ← nodeGraph commentNode then
    for edge in reversedEdges do
      LGraphUtil.reverseEdge edge graph true

/-- The northern/southern connection flags of `choose_comment_side` (fixed port sides only); the scan
stops at the first northern connection. -/
def connectionSides (ports : Array LPortId) : LayeredM (Bool × Bool) := do
  let mut hasNorth := false
  let mut hasSouth := false
  for port in ports do
    let side := (← getPort port).side
    for connected in (← withArena (·.portConnectedPorts port)) do
      if ← portOwnerIsCommentBox connected then continue
      if side == .north then
        hasNorth := true
        break
      if side == .south then hasSouth := true
    if hasNorth then break
  return (hasNorth, hasSouth)

/-- Rust `choose_comment_side(realNode)`: `(onlyTop, onlyBottom, topFirst)`. -/
def chooseCommentSide (realNode : LNodeId) : LayeredM (Bool × Bool × Bool) := do
  let nd ← getNode realNode
  let portConstraints := if nd.props.has LayeredOptions.PORT_CONSTRAINTS then
      nd.props.getD LayeredOptions.PORT_CONSTRAINTS PortConstraints.undefined
    else PortConstraints.undefined
  let mut onlyTop := false
  let mut onlyBottom := false
  if portConstraints.isSideFixed then
    let (hasNorth, hasSouth) ← connectionSides nd.ports
    onlyTop := hasSouth && !hasNorth
    onlyBottom := hasNorth && !hasSouth
  let mut topFirst := !onlyBottom
  if !onlyTop && !onlyBottom && !nd.labels.isEmpty then
    let mut labelPosSum := fl0p0
    let mut count : Nat := 0
    for label in nd.labels do
      let lb ← getLabel label
      labelPosSum := labelPosSum + (lb.position.y + lb.size.y / fl2p0)
      count := count + 1
    if count != 0 then topFirst := labelPosSum / count.toFloat >= nd.size.y / fl2p0
  return (onlyTop, onlyBottom, topFirst)

/-- `removeHierarchicalPortDummyNode(oppositePort)`: removes the `PORT_DUMMY` of the port from its layer
and drops the layer from its graph when it became empty. -/
def removeHierarchicalPortDummyNode (oppositePort : LPortId) : LayeredM Unit := do
  let some dummy := (← getPort oppositePort).internal.portDummy | return
  let some layer := (← getNode dummy).layer | return
  setNodeLayer dummy none
  if !(← getLayer layer).nodes.isEmpty then return
  let owner := (← getLayer layer).owner
  modifyGraph owner fun g => { g with layers := g.layers.filter (· != layer) }

/-- `processBox(box, edge, oppositePort, realNode)`. -/
def processBox (boxNode : LNodeId) (edge : LEdgeId) (oppositePort : LPortId) (realNode : LNodeId) :
    LayeredM Unit := do
  let (onlyTop, onlyBottom, topFirst) ← chooseCommentSide realNode
  let rn ← getNode realNode
  let topBoxes := rn.internal.topComments
  let bottomBoxes := rn.internal.bottomComments
  let hasTop := !topBoxes.isEmpty
  let hasBottom := !bottomBoxes.isEmpty
  let useTop :=
    if topFirst then
      if !hasTop || onlyTop then true
      else if !hasBottom then false
      else topBoxes.size <= bottomBoxes.size
    else if !hasBottom || onlyBottom then false
    else if !hasTop then true
    else bottomBoxes.size > topBoxes.size
  if useTop then
    modifyNode realNode fun n => { n with internal := { n.internal with topComments := n.internal.topComments.push boxNode } }
  else
    modifyNode realNode fun n => { n with internal := { n.internal with bottomComments := n.internal.bottomComments.push boxNode } }
  modifyNode boxNode fun n => { n with internal := { n.internal with commentConnPort := some oppositePort } }
  if (← getEdge edge).target == some oppositePort then
    setEdgeTarget edge none
    if (← getPort oppositePort).degree == 0 then setPortNode oppositePort none
    removeHierarchicalPortDummyNode oppositePort
  else
    setEdgeSource edge none
    if (← getPort oppositePort).degree == 0 then setPortNode oppositePort none
  modifyEdge edge fun e => { e with bendPoints := #[] }

/-- The single edge of a comment box (last port with exactly one incoming/outgoing edge wins, outgoing
over incoming), its opposite port and the comment's total edge count. -/
def findSingleConnection (node : LNodeId) : LayeredM (Nat × Option LEdgeId × Option LPortId) := do
  let mut edgeCount := 0
  let mut edge : Option LEdgeId := none
  let mut oppositePort : Option LPortId := none
  for port in (← getNode node).ports do
    let pt ← getPort port
    edgeCount := edgeCount + pt.degree
    if let some incomingEdge := pt.incomingEdges[0]? then
      if pt.incomingEdges.size == 1 then
        edge := some incomingEdge
        oppositePort := (← getEdge incomingEdge).source
    if let some outgoingEdge := pt.outgoingEdges[0]? then
      if pt.outgoingEdges.size == 1 then
        edge := some outgoingEdge
        oppositePort := (← getEdge outgoingEdge).target
  return (edgeCount, edge, oppositePort)

/-- Whether the comment box qualifies for attachment: one edge in total, to a port of degree one whose
node is no comment box. -/
def qualifies (edgeCount : Nat) (oppositePort : Option LPortId) : LayeredM Bool := do
  let some op := oppositePort | return false
  let opt ← getPort op
  let ownerOk ← (do
    match opt.owner with
    | some owner => pure !(← isCommentBox owner)
    | none => pure false)
  return edgeCount == 1 && opt.degree == 1 && ownerOk

/-- Handles the comment box at `index` of the layerless nodes; returns whether it was removed from them. -/
def handleCommentBox (graph : LGraphId) (node : LNodeId) (index : Nat) : LayeredM Bool := do
  let (edgeCount, edge, oppositePort) ← findSingleConnection node
  if ← qualifies edgeCount oppositePort then
    if let (some e, some op) := (edge, oppositePort) then
      if let some realNode := (← getPort op).owner then
        processBox node e op realNode
        modifyGraph graph fun g => { g with layerlessNodes := g.layerlessNodes.eraseIdx! index }
        return true
  else
    reverseOddlyConnectedEdges node
  return false

/-- `process(layeredGraph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let mut index := 0
  while true do
    let nodes := (← getGraph graph).layerlessNodes
    if index >= nodes.size then break
    let node := nodes[index]!
    if !(← isCommentBox node) then
      index := index + 1
      continue
    if ← handleCommentBox graph node index then continue
    index := index + 1

/-- The `CommentPreprocessor` processor. -/
def processor : LayeredProcessor :=
  { name := "CommentPreprocessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Comment pre-processing" 1.0
      run graph
      monitor.done }

end CommentPreprocessor

builtin_initialize registerCommentPreprocessor : Unit ←
  IntermediateProcessorStrategy.register .commentPreprocessor CommentPreprocessor.processor

end Elk.Alg.Layered.Intermediate
