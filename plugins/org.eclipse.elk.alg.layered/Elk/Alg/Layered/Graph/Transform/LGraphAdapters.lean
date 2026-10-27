import Std.Data.HashSet
import Elk.Core.Util.Adapters.GraphAdapters
import Elk.Core.Util.Sort
import Elk.Core.Util.Java
import Elk.Alg.Layered.Graph.Monad
import Elk.Alg.Layered.Graph.LGraphQueries
/-!
# `org.eclipse.elk.alg.layered.graph.LGraphAdapters`

Port of elk-rs `graph/transform/l_graph_adapters.rs` (Java `org.eclipse.elk.alg.layered.graph.LGraphAdapters`;
elk-rs moved it into the `transform` module, the Lean file follows elk-rs). It instantiates the
generic `GraphAdapters` record for the layered arena in `LayeredM`, so that `alg.common`'s node
spacing code (`NodeDimensionCalculation`, `NodeMarginCalculator`, `NodeLabelAndSizeCalculator`)
can work on `LGraph`s: `LAdapters := GraphAdapters LayeredM LGraphId LNodeId LPortId LLabelId LEdgeId`.

Reproduced elk-rs behaviour (the oracle):
* `adapt` snapshots the node list like the Rust constructor: the nodes of the layers (layerless
  nodes are ignored, Java: "We completely ignore layerless nodes here") that pass `nodeFilter`,
  each followed by its `TOP_COMMENTS` and then `BOTTOM_COMMENTS` when `transparentCommentNodes`.
* Comment nodes are adapted with `transparentNorthSouthEdges = false` and **without** a parent
  graph (`NodeAdapter.getGraph()` is `none`, Rust `LNodeAdapter::new`); Java gives them the graph
  adapter. Their ports inherit the `false` flag.
* The graph adapter's size and position are `(0, 0)` and cannot be set (Rust; Java returns the
  graph size and throws for the position).
* `getNodes` of the record always returns the snapshot (elk-rs returns an empty node list for the
  graph adapter obtained through `NodeAdapter.getGraph()`; no consumer iterates that one).
* `NodeAdapter.getIncomingEdges/getOutgoingEdges` are empty ("we have no directly connected edges").
* `PortAdapter.getIncomingEdges/getOutgoingEdges`: empty for ports of `NORTH_SOUTH_PORT` dummies when
  the edges are transparent; otherwise the port's edges, plus (transparent) all incoming/outgoing
  edges of the port's `PORT_DUMMY` node, plus the self-loop holder edges (see TODO below).
* `LabelAdapter.getSide()` reads the public `LabelSide.LABEL_SIDE` (`org.eclipse.elk.labelSide`)
  from the label's options, not the internal `labelSide` field (Java and Rust do the same).
* `sortPortList` sorts with the Rust `sort_by` comparator (side ordinal, then `PORT_INDEX` when both
  are set and differ, then the coordinate along the side, `partial_cmp` → `Float.comparePartial`),
  only when the node's `PORT_CONSTRAINTS` fix the order; stable like Rust's `sort_by`.
* Volatile ids are per adapter family (`IO.Ref` arrays indexed by element id, starting at `0`) and
  never touch the elements' `id` fields (Java writes `element.id`; Rust keeps them in `Cell`s).

Deviation: when a node is both a layer node passing the filter and a comment of another adapted
node, Rust has two adapters with different flags; the Lean record (keyed by node id) uses the
layer node's settings.

Self-loop edges (Rust step 3 of `get_incoming_edges`/`get_outgoing_edges`): the `SelfLoopEdge`s of
the port's `SelfLoopPort` in `LNodeInternals.selfLoopHolder` are appended after the dummy edges.
-/
namespace Elk.Alg.Layered.Graph.Transform

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Util.Adapters
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate.Loops LayeredM

/-- The adapters of a layered graph: graph = `LGraphId`, elements by typed arena id. -/
abbrev LAdapters := GraphAdapters LayeredM LGraphId LNodeId LPortId LLabelId LEdgeId

namespace LGraphAdapters

/-! ## Volatile ids -/

private def getVol (r : IO.Ref (Array Int)) (i : Nat) : LayeredM Int := do
  return (← r.get)[i]?.getD 0

private def setVol (r : IO.Ref (Array Int)) (i : Nat) (v : Int) : LayeredM Unit :=
  r.modify fun arr =>
    let arr := if arr.size > i then arr else arr ++ Array.replicate (i + 1 - arr.size) 0
    arr.set! i v

/-! ## Element operations -/

/-- `LGraphAdapter` as a `GraphElementAdapter`: size/position `(0, 0)` and not settable (Rust),
the graph's options, one volatile id. -/
private def graphOps (vol : IO.Ref Int) : ElementOps LayeredM LGraphId where
  getSize _ := return {}
  setSize _ _ := pure ()
  getPosition _ := return {}
  setPosition _ _ := pure ()
  getRaw g k := do return (← getGraph g).props.getRaw? k
  hasProperty g k := do return (← getGraph g).props.hasKey k
  getVolatileId _ := vol.get
  setVolatileId _ v := vol.set v

/-- `LNodeAdapter` element access (Rust `GraphElementAdapter<LNodeRef> for LNodeAdapter`). -/
private def nodeOps (vol : IO.Ref (Array Int)) : ElementOps LayeredM LNodeId where
  getSize n := do return (← getNode n).size
  setSize n s := modifyNode n fun nd => { nd with size := s }
  getPosition n := do return (← getNode n).position
  setPosition n p := modifyNode n fun nd => { nd with position := p }
  getRaw n k := do return (← getNode n).props.getRaw? k
  hasProperty n k := do return (← getNode n).props.hasKey k
  getVolatileId n := getVol vol n.idx
  setVolatileId n v := setVol vol n.idx v

/-- `LPortAdapter` element access. -/
private def portOps (vol : IO.Ref (Array Int)) : ElementOps LayeredM LPortId where
  getSize p := do return (← getPort p).size
  setSize p s := modifyPort p fun pt => { pt with size := s }
  getPosition p := do return (← getPort p).position
  setPosition p v := modifyPort p fun pt => { pt with position := v }
  getRaw p k := do return (← getPort p).props.getRaw? k
  hasProperty p k := do return (← getPort p).props.hasKey k
  getVolatileId p := getVol vol p.idx
  setVolatileId p v := setVol vol p.idx v

/-- `LLabelAdapter` element access. -/
private def labelOpsWith (vol : IO.Ref (Array Int)) : ElementOps LayeredM LLabelId where
  getSize l := do return (← getLabel l).size
  setSize l s := modifyLabel l fun lb => { lb with size := s }
  getPosition l := do return (← getLabel l).position
  setPosition l v := modifyLabel l fun lb => { lb with position := v }
  getRaw l k := do return (← getLabel l).props.getRaw? k
  hasProperty l k := do return (← getLabel l).props.hasKey k
  getVolatileId l := getVol vol l.idx
  setVolatileId l v := setVol vol l.idx v

/-! ## Ports -/

/-- The comparator of Rust `LNodeAdapter::sort_port_list` (Java `PortComparator`,
`DEFAULT_PORTLIST_SORTER`): by side ordinal; for equal sides by `PORT_INDEX` when both ports have
one and they differ; then NORTH by x, EAST by y, SOUTH by x reversed, WEST by y reversed
(`partial_cmp`, equal for an undefined side; Java throws there). -/
def portComparator (a : LGraphArena) (p1 p2 : LPortId) : Ordering :=
  let port1 := a.port p1
  let port2 := a.port p2
  let sideCmp := Ord.compare (ElkEnum.ordinal port1.side) (ElkEnum.ordinal port2.side)
  if sideCmp != .eq then sideCmp
  else
    let byIndex : Option Ordering :=
      match port1.props.get CoreOptions.PORT_INDEX, port2.props.get CoreOptions.PORT_INDEX with
      | some i1, some i2 =>
        let c := Ord.compare i1 i2
        if c != .eq then some c else none
      | _, _ => none
    match byIndex with
    | some o => o
    | none =>
      match port1.side with
      | .north => Float.comparePartial port1.position.x port2.position.x
      | .east => Float.comparePartial port1.position.y port2.position.y
      | .south => Float.comparePartial port2.position.x port1.position.x
      | .west => Float.comparePartial port2.position.y port1.position.y
      | .undefined => .eq

/-- `LNodeAdapter.sortPortList()`: sorts the node's ports with `portComparator` when its
`PORT_CONSTRAINTS` fix the port order (stable, like Rust `sort_by`). -/
def sortPortList (n : LNodeId) : LayeredM Unit := do
  let nd ← getNode n
  let constraints := nd.props.getD CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined
  if constraints.isOrderFixed then
    let a ← get
    let sorted := stableSort nd.ports (portComparator a)
    modifyNode n fun x => { x with ports := sorted }

/-- `LNodeAdapter.sortPortList(comparator)`: sorts with a custom comparator when the port order
is fixed. -/
def sortPortListBy (n : LNodeId) (cmp : LGraphArena → LPortId → LPortId → Ordering) : LayeredM Unit := do
  let nd ← getNode n
  let constraints := nd.props.getD CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined
  if constraints.isOrderFixed then
    let a ← get
    let sorted := stableSort nd.ports (cmp a)
    modifyNode n fun x => { x with ports := sorted }

/-- `LPortAdapter.getIncomingEdges()` (`incoming = true`) / `getOutgoingEdges()`: see module doc.
`transparent` is the adapter's `transparentNorthSouthEdges` flag. -/
def portEdges (incoming transparent : Bool) (p : LPortId) : LayeredM (Array LEdgeId) := do
  let pt ← getPort p
  -- transparent N/S edges: ports of north/south port dummies have no edges
  if transparent then
    if let some owner := pt.owner then
      if (← getNode owner).type == .northSouthPort then return #[]
  -- 1. the port's own edges
  let mut edges := if incoming then pt.incomingEdges else pt.outgoingEdges
  -- 2. transparent N/S edges: all edges of the PORT_DUMMY node (all of its ports)
  if transparent then
    if let some dummy := pt.internal.portDummy then
      let a ← get
      edges := edges ++ (if incoming then a.nodeIncomingEdges dummy else a.nodeOutgoingEdges dummy)
  -- 3. the self-loop edges of the port's `SelfLoopPort` (`SELF_LOOP_HOLDER` of the owner)
  if let some owner := pt.owner then
    if let some holder := (← getNode owner).internal.selfLoopHolder then
      if let some slPortId := holder.slPortOf? p then
        let slPort := holder.slPort slPortId
        for sle in (if incoming then slPort.incomingSLEdges else slPort.outgoingSLEdges) do
          edges := edges.push (holder.slEdge sle).lEdge
  return edges

/-! ## Factory -/

/-- The snapshot taken by `adapt`: the adapted nodes in Rust order, the layer nodes, and the
comment nodes added through `TOP_COMMENTS`/`BOTTOM_COMMENTS`. -/
structure NodeSnapshot where
  nodes : Array LNodeId := #[]
  layerNodes : Std.HashSet LNodeId := {}
  commentNodes : Std.HashSet LNodeId := {}

/-- The node list of Rust `LGraphAdapters::adapt`: per layer, per node passing `nodeFilter`, the
node, then (with `transparentCommentNodes`) its top comments, then its bottom comments. -/
def snapshotNodes (graph : LGraphId) (transparentCommentNodes : Bool) (nodeFilter : LNode → Bool) :
    LayeredM NodeSnapshot := do
  let mut snap : NodeSnapshot := {}
  for l in (← getGraph graph).layers do
    for n in (← getLayer l).nodes do
      let nd ← getNode n
      if nodeFilter nd then
        snap := { snap with nodes := snap.nodes.push n, layerNodes := snap.layerNodes.insert n }
        if transparentCommentNodes then
          for c in nd.internal.topComments do
            snap := { snap with nodes := snap.nodes.push c, commentNodes := snap.commentNodes.insert c }
          for c in nd.internal.bottomComments do
            snap := { snap with nodes := snap.nodes.push c, commentNodes := snap.commentNodes.insert c }
  return snap

/-- Whether `n` is adapted as a comment node only (no parent graph, opaque N/S edges). -/
@[inline] private def isCommentOnly (snap : NodeSnapshot) (n : LNodeId) : Bool :=
  snap.commentNodes.contains n && !snap.layerNodes.contains n

/-- The `transparentNorthSouthEdges` flag of the adapter of port `p` (its node's flag). -/
private def portTransparent (snap : NodeSnapshot) (transparentNorthSouthEdges : Bool) (p : LPortId) :
    LayeredM Bool := do
  match (← getPort p).owner with
  | some owner => return if isCommentOnly snap owner then false else transparentNorthSouthEdges
  | none => return transparentNorthSouthEdges

/-- `LGraphAdapters.adapt(graph, transparentNorthSouthEdges, transparentCommentNodes, nodeFilter)`
(Rust `adapt`): the adapter family of `graph` with the node snapshot described in the module doc.
Runs in `LayeredM` because the Rust constructor reads the layers. -/
def adapt (graph : LGraphId) (transparentNorthSouthEdges transparentCommentNodes : Bool)
    (nodeFilter : LNode → Bool) : LayeredM LAdapters := do
  let snap ← snapshotNodes graph transparentCommentNodes nodeFilter
  let graphVol ← IO.mkRef (0 : Int)
  let nodeVol ← IO.mkRef (#[] : Array Int)
  let portVol ← IO.mkRef (#[] : Array Int)
  let labelVol ← IO.mkRef (#[] : Array Int)
  let nodes := snap.nodes
  return {
    graph := graphOps graphVol
    getNodes := fun _ => return nodes
    node := nodeOps nodeVol
    getGraph := fun n => return if isCommentOnly snap n then none else some graph
    nodeLabels := fun n => do return (← getNode n).labels
    nodePorts := fun n => do return (← getNode n).ports
    nodeIncomingEdges := fun _ => return #[]
    nodeOutgoingEdges := fun _ => return #[]
    sortPortList := sortPortList
    isCompoundNode := fun n => do return (← getNode n).internal.compoundNode
    getPadding := fun n => do return (← getNode n).padding
    setPadding := fun n p => modifyNode n fun nd => { nd with padding := p }
    getNodeMargin := fun n => do return (← getNode n).margin
    setNodeMargin := fun n mg => modifyNode n fun nd => { nd with margin := mg }
    port := portOps portVol
    portSide := fun p => do return (← getPort p).side
    portLabels := fun p => do return (← getPort p).labels
    getPortMargin := fun p => do return (← getPort p).margin
    setPortMargin := fun p mg => modifyPort p fun pt => { pt with margin := mg }
    portIncomingEdges := fun p => do portEdges true (← portTransparent snap transparentNorthSouthEdges p) p
    portOutgoingEdges := fun p => do portEdges false (← portTransparent snap transparentNorthSouthEdges p) p
    hasCompoundConnections := fun p => do return (← getPort p).internal.insideConnections
    label := labelOpsWith labelVol
    labelSide := fun l => do return (← getLabel l).props.getD LabelSide.LABEL_SIDE LabelSide.unknown
    labelText := fun l => do return (← getLabel l).text
    edgeLabels := fun e => do return (← getEdge e).labels
  }

/-- Rust `LGraphAdapters::adapt_simple(graph)` (Java `adapt(graph)`): no transparent edges, no
comment nodes, all layer nodes. -/
def adaptSimple (graph : LGraphId) : LayeredM LAdapters :=
  adapt graph false false fun _ => true

/-- Rust `LGraphAdapters::adapt_label(label)` (Java `adapt(LLabel)`): the label element access
(fresh volatile ids) used by label cells (`LabelCell` takes the label handles plus these ops). -/
def adaptLabel : IO (ElementOps LayeredM LLabelId) := do
  return labelOpsWith (← IO.mkRef (#[] : Array Int))

end LGraphAdapters

end Elk.Alg.Layered.Graph.Transform
