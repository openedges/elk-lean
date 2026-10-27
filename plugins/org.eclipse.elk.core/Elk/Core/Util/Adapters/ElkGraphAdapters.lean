import Elk.Core.Util.Adapters.GraphAdapters
import Elk.Core.Util.Sort
import Elk.Core.Util.ElkTrace
/-!
# `org.eclipse.elk.core.util.adapters.ElkGraphAdapters`

`GraphAdapters` instance for `ElkGraph` in the `ElkM` monad. Unlike the Java/Rust
wrappers, nothing is cached: every call reads the arena. Volatile ids live in
per-adapter `IO.Ref` arrays indexed by element id, so each `adapt` starts from 0.
-/
namespace Elk.Core.Util.Adapters

open Elk.Graph Elk.Core.Math Elk.Core.Options

/-- `ElkGraphAdapters.PortComparator` (`DEFAULT_PORTLIST_SORTER`): by port side ordinal,
then `PORT_INDEX` (when both are set), then by the coordinate along the side. -/
def PortComparator.compare (g : ElkGraph) (p1 p2 : PortId) : Ordering :=
  let port1 := g.port p1
  let port2 := g.port p2
  let side1 := port1.props.getD CoreOptions.PORT_SIDE PortSide.undefined
  let side2 := port2.props.getD CoreOptions.PORT_SIDE PortSide.undefined
  let ordinalDifference : Int := (ElkEnum.ordinal side1 : Int) - (ElkEnum.ordinal side2 : Int)
  if ordinalDifference != 0 then Ord.compare ordinalDifference 0
  else
    let byIndex : Option Ordering := match port1.props.get CoreOptions.PORT_INDEX, port2.props.get CoreOptions.PORT_INDEX with
      | some i1, some i2 => if i1 - i2 != 0 then some (Ord.compare (i1 - i2) 0) else none
      | _, _ => none
    match byIndex with
    | some o => o
    | none =>
      match side1 with
      | .north => Float.comparePartial port1.x port2.x
      | .east => Float.comparePartial port1.y port2.y
      | .south => Float.comparePartial port2.x port1.x
      | .west => Float.comparePartial port2.y port1.y
      | .undefined => .eq

/-- The adapters of an `ElkGraph`: graph = parent node, elements by typed id. -/
abbrev ElkAdapters := GraphAdapters ElkM NodeId NodeId PortId LabelId EdgeId

namespace ElkGraphAdapters

private def getVol (r : IO.Ref (Array Int)) (i : Nat) : ElkM Int := do
  return (← r.get)[i]?.getD 0

private def setVol (r : IO.Ref (Array Int)) (i : Nat) (v : Int) : ElkM Unit :=
  r.modify fun arr =>
    let arr := if arr.size > i then arr else arr ++ Array.replicate (i + 1 - arr.size) 0
    arr.set! i v

/-- `PORT_BORDER_OFFSET` is read through a proxy property with default `0.0`. -/
private def offsetOverride (k : PropKey) : Option PropValue :=
  if k == CoreOptions.PORT_BORDER_OFFSET.key then some (.double 0.0) else none

private def nodeOps (vol : IO.Ref (Array Int)) : ElementOps ElkM NodeId where
  getSize n := do
    let nd ← ElkM.getNode n
    return ⟨nd.width, nd.height⟩
  setSize n s := ElkM.modifyNode n fun nd => { nd with width := s.x, height := s.y }
  getPosition n := do
    let nd ← ElkM.getNode n
    return ⟨nd.x, nd.y⟩
  setPosition n p := ElkM.modifyNode n fun nd => { nd with x := p.x, y := p.y }
  getRaw n k := do return (← ElkM.getNode n).props.getRaw? k
  hasProperty n k := do return (← ElkM.getNode n).props.hasKey k
  getVolatileId n := getVol vol n.idx
  setVolatileId n v := setVol vol n.idx v
  defaultOverride := offsetOverride

private def portOps (vol : IO.Ref (Array Int)) : ElementOps ElkM PortId where
  getSize p := do
    let pt ← ElkM.getPort p
    return ⟨pt.width, pt.height⟩
  setSize p s := ElkM.modifyPort p fun pt => { pt with width := s.x, height := s.y }
  getPosition p := do
    let pt ← ElkM.getPort p
    return ⟨pt.x, pt.y⟩
  setPosition p v := ElkM.modifyPort p fun pt => { pt with x := v.x, y := v.y }
  getRaw p k := do return (← ElkM.getPort p).props.getRaw? k
  hasProperty p k := do return (← ElkM.getPort p).props.hasKey k
  getVolatileId p := getVol vol p.idx
  setVolatileId p v := setVol vol p.idx v
  defaultOverride := offsetOverride

private def labelOps (vol : IO.Ref (Array Int)) : ElementOps ElkM LabelId where
  getSize l := do
    let lb ← ElkM.getLabel l
    return ⟨lb.width, lb.height⟩
  setSize l s := ElkM.modifyLabel l fun lb => { lb with width := s.x, height := s.y }
  getPosition l := do
    let lb ← ElkM.getLabel l
    return ⟨lb.x, lb.y⟩
  setPosition l v := ElkM.modifyLabel l fun lb => { lb with x := v.x, y := v.y }
  getRaw l k := do return (← ElkM.getLabel l).props.getRaw? k
  hasProperty l k := do return (← ElkM.getLabel l).props.hasKey k
  getVolatileId l := getVol vol l.idx
  setVolatileId l v := setVol vol l.idx v
  defaultOverride := offsetOverride

/-- `ElkNodeAdapter.sortPortList()`: sorts the node's ports with `PortComparator` when the
port constraints fix the order (stable sort, like Rust `sort_by`). -/
def sortPortList (n : NodeId) : ElkM Unit := do
  let nd ← ElkM.getNode n
  let constraints := nd.props.getD CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined
  if constraints.isOrderFixed then
    let g ← get
    let trace := ElkTrace.global.corePortSort
    let portIds (ps : Array PortId) : String :=
      ", ".intercalate (ps.toList.map fun p => (g.port p).identifier.getD "<no-port-id>")
    let before := if trace then portIds nd.ports else ""
    let sorted := stableSort nd.ports (fun a b => PortComparator.compare g a b)
    ElkM.modifyNode n fun x => { x with ports := sorted }
    if trace then
      IO.eprintln s!"rust-core-port-sort: node={nd.identifier.getD "<no-node-id>"} constraints={constraints} before=[{before}] after=[{portIds sorted}]"

/-- `ElkPortAdapter.hasCompoundConnections()`. -/
def hasCompoundConnections (p : PortId) : ElkM Bool := do
  let pt ← ElkM.getPort p
  let some node := pt.parent | return false
  let g ← get
  for e in pt.outgoingEdges do
    let edge := g.edge e
    for target in edge.targets do
      if let some targetNode := ElkGraphUtil.connectableShapeToNode g target then
        if ElkGraphUtil.isDescendant g targetNode node then return true
        if targetNode == node then
          if edge.props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false then return true
  for e in pt.incomingEdges do
    for source in (g.edge e).sources do
      if let some sourceNode := ElkGraphUtil.connectableShapeToNode g source then
        if ElkGraphUtil.isDescendant g sourceNode node then return true
  return false

/-- Creates a fresh adapter family (volatile ids start at 0). `ElkGraphAdapters.adapt(graph)`,
`adaptSingleNode(node)` and `adaptSinglePort(port)` all produce this record; the graph of a
node is its parent node. -/
def new : IO ElkAdapters := do
  let graphVol ← IO.mkRef (#[] : Array Int)
  let nodeVol ← IO.mkRef (#[] : Array Int)
  let portVol ← IO.mkRef (#[] : Array Int)
  let labelVol ← IO.mkRef (#[] : Array Int)
  return {
    graph := nodeOps graphVol
    getNodes := fun g => do return (← ElkM.getNode g).children
    node := nodeOps nodeVol
    getGraph := fun n => do return (← ElkM.getNode n).parent
    nodeLabels := fun n => do return (← ElkM.getNode n).labels
    nodePorts := fun n => do return (← ElkM.getNode n).ports
    nodeIncomingEdges := fun n => do return ElkGraphUtil.allIncomingEdges (← get) n
    nodeOutgoingEdges := fun n => do return ElkGraphUtil.allOutgoingEdges (← get) n
    sortPortList := sortPortList
    isCompoundNode := fun n => do
      let nd ← ElkM.getNode n
      return !nd.children.isEmpty || nd.props.getD CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false
    getPadding := fun n => do return (← ElkM.getNode n).props.getD CoreOptions.PADDING {}
    setPadding := fun n p => ElkM.modifyNode n fun nd => { nd with props := nd.props.set CoreOptions.PADDING p }
    getNodeMargin := fun n => do return (← ElkM.getNode n).props.getD CoreOptions.MARGINS {}
    setNodeMargin := fun n mg => ElkM.modifyNode n fun nd => { nd with props := nd.props.set CoreOptions.MARGINS mg }
    port := portOps portVol
    portSide := fun p => do return (← ElkM.getPort p).props.getD CoreOptions.PORT_SIDE PortSide.undefined
    portLabels := fun p => do return (← ElkM.getPort p).labels
    getPortMargin := fun p => do return (← ElkM.getPort p).props.getD CoreOptions.MARGINS {}
    setPortMargin := fun p mg => ElkM.modifyPort p fun pt => { pt with props := pt.props.set CoreOptions.MARGINS mg }
    portIncomingEdges := fun p => do return (← ElkM.getPort p).incomingEdges
    portOutgoingEdges := fun p => do return (← ElkM.getPort p).outgoingEdges
    hasCompoundConnections := hasCompoundConnections
    label := labelOps labelVol
    labelSide := fun l => do return (← ElkM.getLabel l).props.getD LabelSide.LABEL_SIDE LabelSide.unknown
    labelText := fun l => do return (← ElkM.getLabel l).text
    edgeLabels := fun e => do return (← ElkM.getEdge e).labels
  }

/-- `ElkGraphAdapters.adapt(graph)`: the adapters, with `graph` as the graph element. -/
def adapt (_graph : NodeId) : IO ElkAdapters := new

/-- `ElkGraphAdapters.adaptSingleNode(node)`. -/
def adaptSingleNode (_node : NodeId) : IO ElkAdapters := new

/-- `ElkGraphAdapters.adaptSinglePort(port)`. -/
def adaptSinglePort (_port : PortId) : IO ElkAdapters := new

end ElkGraphAdapters

end Elk.Core.Util.Adapters
