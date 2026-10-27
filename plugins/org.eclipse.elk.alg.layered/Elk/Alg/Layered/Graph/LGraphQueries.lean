import Elk.Alg.Layered.Graph.LGraphArena
import Elk.Core.Util.Java
/-!
# Read-only methods of `LNode`/`LPort`/`LEdge`/`Layer`/`LGraph` that need the arena

Java defines these on the element classes; here they are pure functions over the
`LGraphArena` (the element files cannot import the arena). Each docstring names the
Java method.
-/
namespace Elk.Alg.Layered.Graph

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Alg.Layered.Options

namespace LGraphArena

/-- `LNode.getPorts(PortType)`: input ports have incoming edges, output ports outgoing edges. -/
def nodePortsByType (a : LGraphArena) (n : LNodeId) (portType : PortType) : Array LPortId :=
  match portType with
  | .input => (a.node n).ports.filter fun p => !(a.port p).incomingEdges.isEmpty
  | .output => (a.node n).ports.filter fun p => !(a.port p).outgoingEdges.isEmpty
  | .undefined => #[]

/-- `LNode.getPorts(PortSide)` without the side cache. -/
def nodePortsBySide (a : LGraphArena) (n : LNodeId) (side : PortSide) : Array LPortId :=
  (a.node n).ports.filter fun p => (a.port p).side == side

/-- `LNode.findPortIndices()`: per `PortSide` ordinal the `[first, last)` range of the node's
ports on that side (ports are assumed to be sorted by side). -/
def findPortIndices (a : LGraphArena) (n : LNodeId) : Array (Option (Nat × Nat)) := Id.run do
  let ports := (a.node n).ports
  let mut indices : Array (Option (Nat × Nat)) := Array.replicate 5 none
  if ports.isEmpty then return indices
  let mut firstIndex := 0
  let mut currentSide := PortSide.north
  let mut currentIndex := 0
  for p in ports do
    let side := (a.port p).side
    if side != currentSide then
      if firstIndex != currentIndex then
        indices := indices.set! (ElkEnum.ordinal currentSide) (some (firstIndex, currentIndex))
      currentSide := side
      firstIndex := currentIndex
    currentIndex := currentIndex + 1
  indices := indices.set! (ElkEnum.ordinal currentSide) (some (firstIndex, currentIndex))
  return indices

/-- `LNode.getPortSideView(side)`: the cached index range when valid, else a filtered copy. -/
def nodePortSideView (a : LGraphArena) (n : LNodeId) (side : PortSide) : Array LPortId :=
  let nd := a.node n
  let indices := if nd.portSidesCached then
      match nd.portSideIndices with
      | some idx => some idx
      | none => some (a.findPortIndices n)
    else none
  let fromCache : Option (Array LPortId) := do
    let idx ← indices
    let (first, last) ← (idx[ElkEnum.ordinal side]?).bind id
    let slice := nd.ports.extract first last
    if slice.all (fun p => (a.port p).side == side) then some slice else none
  match fromCache with
  | some s => s
  | none => nd.ports.filter fun p => (a.port p).side == side

/-- `LNode.getPorts(PortType, PortSide)`. -/
def nodePortsByTypeAndSide (a : LGraphArena) (n : LNodeId) (portType : PortType) (side : PortSide) : Array LPortId :=
  (a.node n).ports.filter fun p =>
    let pt := a.port p
    pt.side == side && (match portType with
      | .input => !pt.incomingEdges.isEmpty
      | .output => !pt.outgoingEdges.isEmpty
      | .undefined => false)

/-- `LNode.getIncomingEdges()`: concatenation over the ports. -/
def nodeIncomingEdges (a : LGraphArena) (n : LNodeId) : Array LEdgeId :=
  (a.node n).ports.foldl (fun acc p => acc ++ (a.port p).incomingEdges) #[]

/-- `LNode.getOutgoingEdges()`. -/
def nodeOutgoingEdges (a : LGraphArena) (n : LNodeId) : Array LEdgeId :=
  (a.node n).ports.foldl (fun acc p => acc ++ (a.port p).outgoingEdges) #[]

/-- `LNode.getConnectedEdges()`: per port incoming then outgoing. -/
def nodeConnectedEdges (a : LGraphArena) (n : LNodeId) : Array LEdgeId :=
  (a.node n).ports.foldl (fun acc p => acc ++ (a.port p).connectedEdges) #[]

/-- `LNode.getIndex()`: index in its layer. -/
def nodeIndex (a : LGraphArena) (n : LNodeId) : Option Nat :=
  ((a.node n).layer.bind fun l => (a.layer l).nodes.findIdx? (· == n))

/-- `LNode.isInlineEdgeLabel()`. -/
def nodeIsInlineEdgeLabel (a : LGraphArena) (n : LNodeId) : Bool :=
  let nd := a.node n
  nd.type == .label && !nd.internal.representedLabels.isEmpty &&
    nd.internal.representedLabels.all fun l => (a.label l).props.getD CoreOptions.EDGE_LABELS_INLINE false

/-- `LNode.getDesignation()`: first non-empty label text, else the index in the layer (`-1`). -/
def nodeDesignation (a : LGraphArena) (n : LNodeId) : String :=
  let nd := a.node n
  match nd.labels[0]? with
  | some l =>
    let text := (a.label l).text
    if !text.isEmpty then text else (a.nodeIndex n).map toString |>.getD "-1"
  | none => (a.nodeIndex n).map toString |>.getD "-1"

/-- `LNode.toString()`: `n_<designation>` with `(<type>)` for dummies. -/
def nodeToString (a : LGraphArena) (n : LNodeId) : String :=
  let nd := a.node n
  let typePart := if nd.type != .normal then s!"({nd.type.name.toLower})" else ""
  s!"n{typePart}_{a.nodeDesignation n}"

/-- `LNode.borderToContentAreaCoordinates(horizontal, vertical)`. -/
def nodeBorderToContentAreaCoordinates (a : LGraphArena) (n : LNodeId) (horizontal vertical : Bool) : LGraphArena :=
  match a.nodeGraph n with
  | none => a
  | some g =>
    let gr := a.graph g
    a.modifyNode n fun nd =>
      let x := if horizontal then nd.position.x - (gr.padding.left + gr.offset.x) else nd.position.x
      let y := if vertical then nd.position.y - (gr.padding.top + gr.offset.y) else nd.position.y
      { nd with position := ⟨x, y⟩ }

/-- `LPort.getAbsoluteAnchor()`: owner position + port position + anchor. -/
def portAbsoluteAnchor (a : LGraphArena) (p : LPortId) : Option KVector :=
  let pt := a.port p
  pt.owner.map fun owner =>
    let nd := a.node owner
    ⟨nd.position.x + pt.position.x + pt.anchor.x, nd.position.y + pt.position.y + pt.anchor.y⟩

/-- `LPort.getName()`: text of the first label. -/
def portName (a : LGraphArena) (p : LPortId) : Option String :=
  ((a.port p).labels[0]?).map fun l => (a.label l).text

/-- `LPort.getPredecessorPorts()`. -/
def portPredecessorPorts (a : LGraphArena) (p : LPortId) : Array LPortId :=
  (a.port p).incomingEdges.filterMap fun e => (a.edge e).source

/-- `LPort.getSuccessorPorts()`. -/
def portSuccessorPorts (a : LGraphArena) (p : LPortId) : Array LPortId :=
  (a.port p).outgoingEdges.filterMap fun e => (a.edge e).target

/-- `LPort.getConnectedPorts()`: predecessors then successors. -/
def portConnectedPorts (a : LGraphArena) (p : LPortId) : Array LPortId :=
  a.portPredecessorPorts p ++ a.portSuccessorPorts p

/-- `LPort.getIndex()`: index in the owner's port list. -/
def portIndex (a : LGraphArena) (p : LPortId) : Option Nat :=
  (a.port p).owner.bind fun owner => (a.node owner).ports.findIdx? (· == p)

/-- `LPort.getDesignation()`. -/
def portDesignation (a : LGraphArena) (p : LPortId) : String :=
  let pt := a.port p
  match pt.labels[0]? with
  | some l =>
    let text := (a.label l).text
    if !text.isEmpty then text else (a.portIndex p).map toString |>.getD "-1"
  | none => (a.portIndex p).map toString |>.getD "-1"

/-- `LPort.toString()`. -/
def portToString (a : LGraphArena) (p : LPortId) : String := Id.run do
  let pt := a.port p
  let mut s := s!"p_{a.portDesignation p}"
  if let some owner := pt.owner then s := s ++ s!"[{a.nodeToString owner}]"
  if pt.incomingEdges.size == 1 && pt.outgoingEdges.isEmpty then
    if let some e := pt.incomingEdges[0]? then
      if let some source := (a.edge e).source then
        if source != p then
          s := s ++ s!" << {a.portDesignation source}"
          if let some so := (a.port source).owner then s := s ++ s!"[{a.nodeToString so}]"
  if pt.incomingEdges.isEmpty && pt.outgoingEdges.size == 1 then
    if let some e := pt.outgoingEdges[0]? then
      if let some target := (a.edge e).target then
        if target != p then
          s := s ++ s!" >> {a.portDesignation target}"
          if let some tgt := (a.port target).owner then s := s ++ s!"[{a.nodeToString tgt}]"
  return s

/-- `LEdge.isSelfLoop()`. -/
def edgeIsSelfLoop (a : LGraphArena) (e : LEdgeId) : Bool :=
  let ed := a.edge e
  match ed.source, ed.target with
  | some s, some t =>
    match (a.port s).owner, (a.port t).owner with
    | some sn, some tn => sn == tn
    | _, _ => false
  | _, _ => false

/-- `LEdge.isInLayerEdge()`: source and target nodes in the same layer (self loops excluded). -/
def edgeIsInLayerEdge (a : LGraphArena) (e : LEdgeId) : Bool :=
  if a.edgeIsSelfLoop e then false
  else
    let ed := a.edge e
    match ed.source, ed.target with
    | some s, some t =>
      match (a.port s).owner.bind (fun n => (a.node n).layer), (a.port t).owner.bind (fun n => (a.node n).layer) with
      | some sl, some tl => sl == tl
      | _, _ => false
    | _, _ => false

/-- `LEdge.getOther(port)`: `none` when `port` is neither end (Java throws). -/
def edgeOtherPort (a : LGraphArena) (e : LEdgeId) (p : LPortId) : Option LPortId :=
  let ed := a.edge e
  if ed.source == some p then ed.target
  else if ed.target == some p then ed.source
  else none

/-- `LEdge.getOther(node)`: `none` when `node` is neither end (Java throws). -/
def edgeOtherNode (a : LGraphArena) (e : LEdgeId) (n : LNodeId) : Option LNodeId :=
  let ed := a.edge e
  let source := ed.source.bind fun p => (a.port p).owner
  let target := ed.target.bind fun p => (a.port p).owner
  if source == some n then target
  else if target == some n then source
  else none

/-- `LEdge.getDesignation()`: text of the first label. -/
def edgeDesignation (a : LGraphArena) (e : LEdgeId) : Option String :=
  ((a.edge e).labels[0]?).bind fun l =>
    let text := (a.label l).text
    if text.isEmpty then none else some text

/-- `LEdge.toString()`. -/
def edgeToString (a : LGraphArena) (e : LEdgeId) : String := Id.run do
  let ed := a.edge e
  let mut s := "e_"
  if let some d := a.edgeDesignation e then s := s ++ d
  if let (some source, some target) := (ed.source, ed.target) then
    s := s ++ s!" {a.portDesignation source}"
    if let some sn := (a.port source).owner then s := s ++ s!"[{a.nodeToString sn}]"
    s := s ++ s!" -> {a.portDesignation target}"
    if let some tn := (a.port target).owner then s := s ++ s!"[{a.nodeToString tn}]"
  return s

/-- `Layer.getIndex()`: index in the owning graph. -/
def layerIndex (a : LGraphArena) (l : LayerId) : Option Nat :=
  (a.graph (a.layer l).owner).indexOfLayer l

/-- `Layer.toString()`: `L_<index>[nodes]`. -/
def layerToString (a : LGraphArena) (l : LayerId) : String :=
  let index := (a.layerIndex l).map toString |>.getD "-1"
  let nodes := ", ".intercalate ((a.layer l).nodes.toList.map (a.nodeToString ·))
  s!"L_{index}[{nodes}]"

/-- elk-rs `ArenaSync` pass 2 (`arena_sync.rs`): the incoming edges of every port of the graph
in *edge discovery order* — nodes of the layers then layerless nodes, their ports in order, each
port's outgoing edges (first occurrence only, both ends inside the graph). This is the order of
`ArenaSync::port_incoming_edges(p)`, which differs from `LPort.incomingEdges`; code ported from
Rust that reads the arena snapshot's incoming lists must use this (PORTING.md §15.1). -/
def arenaIncomingEdges (a : LGraphArena) (g : LGraphId) : Std.HashMap LPortId (Array LEdgeId) := Id.run do
  let gr := a.graph g
  let mut nodes : Array LNodeId := #[]
  for l in gr.layers do
    nodes := nodes ++ (a.layer l).nodes
  nodes := nodes ++ gr.layerlessNodes
  let mut inGraph : Std.HashSet LPortId := {}
  for n in nodes do
    for p in (a.node n).ports do
      inGraph := inGraph.insert p
  let mut seen : Std.HashSet LEdgeId := {}
  let mut incoming : Std.HashMap LPortId (Array LEdgeId) := {}
  for n in nodes do
    for p in (a.node n).ports do
      for e in (a.port p).outgoingEdges do
        if seen.contains e then
          continue
        let ed := a.edge e
        let some s := ed.source | continue
        let some t := ed.target | continue
        if !inGraph.contains s || !inGraph.contains t then
          continue
        seen := seen.insert e
        incoming := incoming.insert t ((incoming.getD t #[]).push e)
  return incoming

/-- `LGraph.toNodeArray()`: the nodes of each layer. -/
def graphToNodeArray (a : LGraphArena) (g : LGraphId) : Array (Array LNodeId) :=
  (a.graph g).layers.map fun l => (a.layer l).nodes

/-- `LGraph.toString()`. -/
def graphToString (a : LGraphArena) (g : LGraphId) : String :=
  let gr := a.graph g
  let layerless := ", ".intercalate (gr.layerlessNodes.toList.map (a.nodeToString ·))
  let layers := ", ".intercalate (gr.layers.toList.map (a.layerToString ·))
  if gr.layers.isEmpty then s!"G-unlayered[{layerless}]"
  else if gr.layerlessNodes.isEmpty then s!"G-layered[{layers}]"
  else s!"G[layerless[{layerless}], layers[{layers}]]"

end LGraphArena

end Elk.Alg.Layered.Graph
