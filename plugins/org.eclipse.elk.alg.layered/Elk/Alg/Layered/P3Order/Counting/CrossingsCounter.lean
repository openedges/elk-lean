import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P3Order.Counting.BinaryIndexedTree
import Elk.Alg.Layered.P3Order.Counting.CrossMinUtil
import Elk.Core.Util.Sort
import Std.Data.HashSet
/-!
# `org.eclipse.elk.alg.layered.p3order.counting.CrossingsCounter`

Counts crossings with a binary indexed tree over port positions (elk-rs `crossings_counter.rs`).
Positions are indexed by the port's `id` (`LPort.id`, assigned by the `IInitializable`s), node
cardinalities by the node's `id` (its index in the layer), exactly like Java `port.id`/`node.id`
and the elk-rs `graph_element().id` path.

elk-rs additionally has a `CrossMinSnapshot` fast path (`set_snapshot`, used by the
`GraphInfoHolder`'s `AllCrossingsCounter`). It reads the same ids from the snapshot and filters
`node.ports` by side instead of `getPortSideView`; both coincide because ports are sorted by side
during crossing minimisation and ids/edges do not change after the snapshot is built, so the
plumbing is not ported (PORTING.md §15.1).

Rust semantics kept where they differ from Java:
- the in-layer/two-port port sets are de-duplicated by port identity and *stably* sorted by
  position (Java uses a `TreeSet` keyed by position, which also drops ports with equal positions);
- long-edge dummies are pushed onto the north/south stack once, not once per eastern port;
- out-of-range ids read position `0`, writes grow the position array (Java throws);
- the `ends` deque is a local stack (it is always drained before the next port).
-/
namespace Elk.Alg.Layered.P3Order.Counting

open Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options

/-- `CrossingsCounter`: mutable port positions, the index tree and the node cardinalities of the
last `initPortPositionsForInLayerCrossings`. -/
structure CrossingsCounter where
  /-- `portPositions` (indexed by `LPort.id`; may be shared with other counters). -/
  portPositions : IO.Ref (Array Int)
  /-- `indexTree`. -/
  indexTree : IO.Ref BinaryIndexedTree
  /-- `nodeCardinalities` (indexed by `LNode.id`). -/
  nodeCardinalities : IO.Ref (Array Int)

namespace CrossingsCounter

/-! ## Pure helpers over the arena -/

/-- Rust `port_id(port)`: `port.id as usize`. -/
@[inline] def portIdOf (a : LGraphArena) (p : LPortId) : Nat := asUsize (a.port p).id

/-- Rust `node_id(node)`: `node.id as usize`. -/
@[inline] def nodeIdOf (a : LGraphArena) (n : LNodeId) : Nat := asUsize (a.node n).id

/-- `positionOf(port)`: `0` for ports without a slot. -/
@[inline] def positionIn (positions : Array Int) (a : LGraphArena) (p : LPortId) : Int :=
  positions[portIdOf a p]?.getD 0

/-- Rust `set_port_position`: grows the array when `pid` is beyond its end. Ids that are not
valid `i32` values (negative ids wrapped by `as usize`) are ignored (Rust would abort). -/
def setPosition (positions : Array Int) (pid : Nat) (v : Int) : Array Int :=
  if pid >>> 32 != 0 then positions
  else
    let positions := if pid >= positions.size then positions ++ Array.replicate (pid + 1 - positions.size) 0 else positions
    positions.setIfInBounds pid v

/-- `otherEndOf(edge, fromPort)`: `none` when an end point is missing (Rust panics). -/
@[inline] def otherEndOf (a : LGraphArena) (e : LEdgeId) (fromPort : LPortId) : Option LPortId :=
  let ed := a.edge e
  match ed.source, ed.target with
  | some s, some t => some (if s == fromPort then t else s)
  | _, _ => none

/-- `isInLayer(edge)`: both end nodes lie in the same layer (self loops included). -/
def isInLayer (a : LGraphArena) (e : LEdgeId) : Bool :=
  let ed := a.edge e
  let layerOf (p : Option LPortId) : Option LayerId :=
    p.bind fun p => (a.port p).owner.bind fun n => (a.node n).layer
  match layerOf ed.source, layerOf ed.target with
  | some s, some t => s == t
  | _, _ => false

/-- `isPortSelfLoop(edge)`: source port equals target port. -/
@[inline] def isPortSelfLoop (a : LGraphArena) (e : LEdgeId) : Bool :=
  let ed := a.edge e
  match ed.source, ed.target with
  | some s, some t => s == t
  | _, _ => false

/-- `getPorts(node, side, topDown)`: `getPortSideView(side)`, reversed for `EAST` bottom-up and for
the other sides top-down (counter-clockwise numbering). -/
def getPorts (a : LGraphArena) (node : LNodeId) (side : PortSide) (topDown : Bool) : Array LPortId :=
  let ports := a.nodePortSideView node side
  let needReverse := if side == .east then !topDown else topDown
  if needReverse then ports.reverse else ports

/-- `initPositions(nodes, ports, side, topDown, getCardinalities)`: numbers the side's ports of
`nodes` (top-down or bottom-up) after the `ports` already collected; returns the updated
positions, cardinalities and port list. An empty `nodes` array changes nothing (Rust returns
before resetting the cardinalities). -/
def initPositions (a : LGraphArena) (positions cards : Array Int) (nodes : Array LNodeId) (ports : Array LPortId)
    (side : PortSide) (topDown getCardinalities : Bool) : Array Int × Array Int × Array LPortId := Id.run do
  if nodes.isEmpty then return (positions, cards, ports)
  let mut numPorts : Int := ports.size
  let mut positions := positions
  let mut cards := if getCardinalities then Array.replicate nodes.size 0 else cards
  let mut ports := ports
  for k in [0:nodes.size] do
    let i := if topDown then k else nodes.size - 1 - k
    let node := nodes[i]!
    let nodePorts := getPorts a node side topDown
    if getCardinalities then
      cards := cards.setIfInBounds (nodeIdOf a node) nodePorts.size
    for p in nodePorts do
      positions := setPosition positions (portIdOf a p) numPorts
      numPorts := numPorts + 1
    ports := ports ++ nodePorts
  return (positions, cards, ports)

/-- `emptyStack(stack, ports, side, startIndex)`: numbers the first `side` port of every stacked
dummy (LIFO). -/
def emptyStack (a : LGraphArena) (stack : Array LNodeId) (ports : Array LPortId) (side : PortSide) (index : Int)
    (positions : Array Int) : Array LNodeId × Array LPortId × Int × Array Int := Id.run do
  let mut stack := stack
  let mut ports := ports
  let mut index := index
  let mut positions := positions
  while !stack.isEmpty do
    let dummy := stack.back!
    stack := stack.pop
    if let some p := (a.nodePortSideView dummy side)[0]? then
      positions := setPosition positions (portIdOf a p) index
      index := index + 1
      ports := ports.push p
  return (stack, ports, index, positions)

/-- `isLayoutUnitChanged(lastUnit, node)` on the already read layout unit of `node`. -/
@[inline] def isLayoutUnitChanged (lastUnit : Option LNodeId) (node : LNodeId) (unit : Option LNodeId) : Bool :=
  match lastUnit with
  | none => false
  | some last => if last == node then false else match unit with
    | some u => u != last
    | none => false

/-- Ports of `node` on `side` that have a `PORT_DUMMY` (`getNorthSouthPortsWithIncidentEdges`). -/
@[inline] def northSouthPortsWithIncidentEdges (a : LGraphArena) (node : LNodeId) (side : PortSide) : Array LPortId :=
  (a.nodePortSideView node side).filter fun p => (a.port p).internal.portDummy.isSome

/-- `initPositionsForNorthSouthCounting(nodes)`: northern ports of a normal node, then the stacked
north/south and long-edge dummies, then its southern ports (`INDEXING_SIDE = WEST`,
`STACK_SIDE = EAST`). -/
def initPositionsForNorthSouthCounting (a : LGraphArena) (positions : Array Int) (nodes : Array LNodeId) :
    Array Int × Array LPortId := Id.run do
  let mut ports : Array LPortId := #[]
  let mut stack : Array LNodeId := #[]
  let mut lastLayoutUnit : Option LNodeId := none
  let mut index : Int := 0
  let mut positions := positions
  for current in nodes do
    let nd := a.node current
    let layoutUnit := nd.internal.inLayerLayoutUnit
    if isLayoutUnitChanged lastLayoutUnit current layoutUnit then
      (stack, ports, index, positions) := emptyStack a stack ports .east index positions
    if layoutUnit.isSome then lastLayoutUnit := layoutUnit
    match nd.type with
    | .normal =>
      for p in northSouthPortsWithIncidentEdges a current .north do
        positions := setPosition positions (portIdOf a p) index
        index := index + 1
        ports := ports.push p
      (stack, ports, index, positions) := emptyStack a stack ports .east index positions
      for p in northSouthPortsWithIncidentEdges a current .south do
        positions := setPosition positions (portIdOf a p) index
        index := index + 1
        ports := ports.push p
    | .northSouthPort =>
      if let some p := (a.nodePortSideView current .west)[0]? then
        positions := setPosition positions (portIdOf a p) index
        index := index + 1
        ports := ports.push p
      if !(a.nodePortSideView current .east).isEmpty then stack := stack.push current
    | .longEdge =>
      for p in a.nodePortSideView current .west do
        positions := setPosition positions (portIdOf a p) index
        index := index + 1
        ports := ports.push p
      if !(a.nodePortSideView current .east).isEmpty then stack := stack.push current
    | _ => pure ()
  (_, ports, _, positions) := emptyStack a stack ports .east index positions
  return (positions, ports)

/-- Adds the collected end positions to the tree (Rust drains the `ends` deque from the back). -/
@[inline] private def addEnds (tree : BinaryIndexedTree) (ends : Array Int) : BinaryIndexedTree := Id.run do
  let mut tree := tree
  for k in [0:ends.size] do
    tree := tree.add (asUsize ends[ends.size - 1 - k]!)
  return tree

/-- `countCrossingsOnPorts(ports)`. -/
def countCrossingsOnPorts (a : LGraphArena) (positions : Array Int) (tree : BinaryIndexedTree) (ports : Array LPortId) :
    Int × BinaryIndexedTree := Id.run do
  let mut crossings : Int := 0
  let mut tree := tree
  for port in ports do
    let currentPosition := positionIn positions a port
    tree := tree.removeAll (asUsize currentPosition)
    let mut ends : Array Int := #[]
    for e in (a.port port).connectedEdges do
      if let some other := otherEndOf a e port then
        let endPosition := positionIn positions a other
        if endPosition > currentPosition then
          crossings := crossings + tree.rank (asUsize endPosition)
          ends := ends.push endPosition
    tree := addEnds tree ends
  return (crossings, tree)

/-- `countInLayerCrossingsOnPorts(ports)`: in-layer edges by rank, every between-layer edge
crosses all open in-layer edges. -/
def countInLayerCrossingsOnPorts (a : LGraphArena) (positions : Array Int) (tree : BinaryIndexedTree) (ports : Array LPortId) :
    Int × BinaryIndexedTree := Id.run do
  let mut crossings : Int := 0
  let mut tree := tree
  for port in ports do
    let currentPosition := positionIn positions a port
    tree := tree.removeAll (asUsize currentPosition)
    let mut numBetweenLayerEdges : Int := 0
    let mut ends : Array Int := #[]
    for e in (a.port port).connectedEdges do
      if isInLayer a e then
        if let some other := otherEndOf a e port then
          let endPosition := positionIn positions a other
          if endPosition > currentPosition then
            crossings := crossings + tree.rank (asUsize endPosition)
            ends := ends.push endPosition
      else
        numBetweenLayerEdges := numBetweenLayerEdges + 1
    crossings := crossings + tree.size * numBetweenLayerEdges
    tree := addEnds tree ends
  return (crossings, tree)

/-- The "edges" of a port taking part in north/south counting (`countNorthSouthCrossingsOnPorts`):
for a normal node all ports of its `PORT_DUMMY`, for a long-edge dummy its other port, for a
north/south dummy the `ORIGIN` port; each with the degree to weight its crossings. -/
def northSouthTargetsAndDegrees (a : LGraphArena) (port : LPortId) : Array (LPortId × Int) :=
  let pt := a.port port
  let nodeType := match pt.owner with
    | some n => (a.node n).type
    | none => NodeType.normal
  match nodeType with
  | .normal =>
    match pt.internal.portDummy with
    | some dummy => (a.node dummy).ports.map fun dp => (dp, ((a.port dp).degree : Int))
    | none => #[]
  | .longEdge =>
    match pt.owner with
    | some n =>
      match (a.node n).ports.find? (· != port) with
      | some other => #[(other, ((a.port other).degree : Int))]
      | none => #[]
    | none => #[]
  | .northSouthPort =>
    match pt.internal.origin with
    | some (.lPort originPort) => #[(originPort, (pt.degree : Int))]
    | _ => #[]
  | _ => #[]

/-- `countNorthSouthCrossingsOnPorts(ports)`. -/
def countNorthSouthCrossingsOnPorts (a : LGraphArena) (positions : Array Int) (tree : BinaryIndexedTree) (ports : Array LPortId) :
    Int × BinaryIndexedTree := Id.run do
  let mut crossings : Int := 0
  let mut tree := tree
  for port in ports do
    let currentPosition := positionIn positions a port
    tree := tree.removeAll (asUsize currentPosition)
    let mut ends : Array Int := #[]
    for (targetPort, degree) in northSouthTargetsAndDegrees a port do
      let endPosition := positionIn positions a targetPort
      if endPosition > currentPosition then
        crossings := crossings + tree.rank (asUsize endPosition) * degree
        ends := ends.push endPosition
    tree := addEnds tree ends
  return (crossings, tree)

/-- `connectedInLayerPortsSortedByPosition(upperNode, lowerNode, side)`: the side's ports of both
nodes with non-self-loop edges plus the far ends of their in-layer edges, de-duplicated in
discovery order and stably sorted by position. -/
def connectedInLayerPortsSortedByPosition (a : LGraphArena) (positions : Array Int) (upperNode lowerNode : LNodeId)
    (side : PortSide) : Array LPortId := Id.run do
  let mut ports : Array LPortId := #[]
  let mut seen : Std.HashSet LPortId := {}
  for node in #[upperNode, lowerNode] do
    for port in CrossMinUtil.inNorthSouthEastWestOrder a node side do
      for e in (a.port port).connectedEdges do
        if a.edgeIsSelfLoop e then continue
        if !seen.contains port then
          seen := seen.insert port
          ports := ports.push port
        if isInLayer a e then
          if let some other := otherEndOf a e port then
            if !seen.contains other then
              seen := seen.insert other
              ports := ports.push other
  return stableSortByKey ports (positionIn positions a ·)

/-- `connectedPortsSortedByPosition(upperPort, lowerPort)`: both ports and the far ends of their
edges (port self loops skipped), de-duplicated and stably sorted by position. -/
def connectedPortsSortedByPosition (a : LGraphArena) (positions : Array Int) (upperPort lowerPort : LPortId) :
    Array LPortId := Id.run do
  let mut ports : Array LPortId := #[]
  let mut seen : Std.HashSet LPortId := {}
  for port in #[upperPort, lowerPort] do
    if !seen.contains port then
      seen := seen.insert port
      ports := ports.push port
    for e in (a.port port).connectedEdges do
      if isPortSelfLoop a e then continue
      if let some other := otherEndOf a e port then
        if !seen.contains other then
          seen := seen.insert other
          ports := ports.push other
  return stableSortByKey ports (positionIn positions a ·)

/-! ## Construction -/

/-- `new CrossingsCounter(portPositions)` sharing the given position array. -/
def new (portPositions : IO.Ref (Array Int)) : BaseIO CrossingsCounter := do
  return { portPositions, indexTree := ← IO.mkRef (BinaryIndexedTree.new 0), nodeCardinalities := ← IO.mkRef #[] }

/-- elk-rs `CrossingsCounter::new(port_positions)`: a counter owning a copy of the positions. -/
def ofPositions (portPositions : Array Int) : BaseIO CrossingsCounter := do
  new (← IO.mkRef portPositions)

/-- Resets the counter to the state of a fresh `CrossingsCounter::new(portPositions)`. -/
def resetTo (c : CrossingsCounter) (portPositions : Array Int) : BaseIO Unit := do
  c.portPositions.set portPositions
  c.indexTree.set (BinaryIndexedTree.new 0)
  c.nodeCardinalities.set #[]

/-! ## Internal monadic steps -/

/-- `initPositions` on the counter's state. -/
private def initPositionsM (c : CrossingsCounter) (nodes : Array LNodeId) (ports : Array LPortId) (side : PortSide)
    (topDown getCardinalities : Bool) : LayeredM (Array LPortId) := do
  let a ← get
  let positions ← c.portPositions.swap #[]
  let cards ← c.nodeCardinalities.swap #[]
  let (positions, cards, ports) := initPositions a positions cards nodes ports side topDown getCardinalities
  c.portPositions.set positions
  c.nodeCardinalities.set cards
  return ports

/-- `initPortPositionsCounterClockwise(leftLayer, rightLayer)`: eastern ports of the left layer
top-down, then western ports of the right layer bottom-up. -/
private def initPortPositionsCounterClockwise (c : CrossingsCounter) (leftLayer rightLayer : Array LNodeId) :
    LayeredM (Array LPortId) := do
  let ports ← c.initPositionsM leftLayer #[] .east true false
  c.initPositionsM rightLayer ports .west false false

/-- Runs one of the pure counting loops on the counter's tree. -/
@[inline] private def withTree (c : CrossingsCounter)
    (count : LGraphArena → Array Int → BinaryIndexedTree → Array LPortId → Int × BinaryIndexedTree)
    (ports : Array LPortId) : LayeredM Int := do
  let a ← get
  let positions ← c.portPositions.get
  let tree ← c.indexTree.swap {}
  let (crossings, tree) := count a positions tree ports
  c.indexTree.set tree
  return crossings

/-! ## Public API -/

/-- `initPortPositionsForInLayerCrossings(nodes, side)`: numbers the side's ports top-down,
records the node cardinalities and resets the tree; returns the ports. -/
def initPortPositionsForInLayerCrossings (c : CrossingsCounter) (nodes : Array LNodeId) (side : PortSide) :
    LayeredM (Array LPortId) := do
  let ports ← c.initPositionsM nodes #[] side true true
  c.indexTree.set (BinaryIndexedTree.new ports.size)
  return ports

/-- `initForCountingBetween(leftLayerNodes, rightLayerNodes)`. -/
def initForCountingBetween (c : CrossingsCounter) (leftLayer rightLayer : Array LNodeId) : LayeredM Unit := do
  let ports ← c.initPortPositionsCounterClockwise leftLayer rightLayer
  c.indexTree.set (BinaryIndexedTree.new ports.size)

/-- `countCrossingsBetweenLayers(leftLayerNodes, rightLayerNodes)`. -/
def countCrossingsBetweenLayers (c : CrossingsCounter) (leftLayer rightLayer : Array LNodeId) : LayeredM Int := do
  let ports ← c.initPortPositionsCounterClockwise leftLayer rightLayer
  c.indexTree.set (BinaryIndexedTree.new ports.size)
  c.withTree countCrossingsOnPorts ports

/-- `countInLayerCrossingsOnSide(nodes, side)`. -/
def countInLayerCrossingsOnSide (c : CrossingsCounter) (nodes : Array LNodeId) (side : PortSide) : LayeredM Int := do
  let ports ← c.initPortPositionsForInLayerCrossings nodes side
  c.withTree countInLayerCrossingsOnPorts ports

/-- `countNorthSouthPortCrossingsInLayer(layer)`. -/
def countNorthSouthPortCrossingsInLayer (c : CrossingsCounter) (layer : Array LNodeId) : LayeredM Int := do
  let a ← get
  let positions ← c.portPositions.swap #[]
  let (positions, ports) := initPositionsForNorthSouthCounting a positions layer
  c.portPositions.set positions
  c.indexTree.set (BinaryIndexedTree.new ports.size)
  c.withTree countNorthSouthCrossingsOnPorts ports

/-- `switchPorts(topPort, bottomPort)`: swaps the two positions (no-op when a port has no slot). -/
def switchPorts (c : CrossingsCounter) (topPort bottomPort : LPortId) : LayeredM Unit := do
  let a ← get
  let topIndex := portIdOf a topPort
  let bottomIndex := portIdOf a bottomPort
  c.portPositions.modify fun pos =>
    if topIndex >= pos.size || bottomIndex >= pos.size then pos else pos.swapIfInBounds topIndex bottomIndex

/-- `switchNodes(wasUpperNode, wasLowerNode, side)`: shifts the side's ports of the former upper
node down by the lower node's cardinality and vice versa. -/
def switchNodes (c : CrossingsCounter) (wasUpper wasLower : LNodeId) (side : PortSide) : LayeredM Unit := do
  let a ← get
  let cards ← c.nodeCardinalities.get
  let upperShift := cards[nodeIdOf a wasLower]?.getD 0
  let lowerShift := cards[nodeIdOf a wasUpper]?.getD 0
  let upperPorts := CrossMinUtil.inNorthSouthEastWestOrder a wasUpper side
  let lowerPorts := CrossMinUtil.inNorthSouthEastWestOrder a wasLower side
  c.portPositions.modify fun pos => Id.run do
    let mut pos := pos
    for p in upperPorts do
      pos := pos.modify (portIdOf a p) (· + upperShift)
    for p in lowerPorts do
      pos := pos.modify (portIdOf a p) (· - lowerShift)
    return pos

/-- `countCrossingsBetweenPortsInBothOrders(upperPort, lowerPort)`: crossings of the edges at the
two ports in the current and in the switched order. Initialise with `initForCountingBetween`
(or `initPortPositionsForInLayerCrossings` at the graph border) first. -/
def countCrossingsBetweenPortsInBothOrders (c : CrossingsCounter) (upperPort lowerPort : LPortId) :
    LayeredM (Int × Int) := do
  let a ← get
  let ports := connectedPortsSortedByPosition a (← c.portPositions.get) upperPort lowerPort
  let upperLowerCrossings ← c.withTree countCrossingsOnPorts ports
  c.indexTree.modify (·.clear)
  c.switchPorts upperPort lowerPort
  let ports := stableSortByKey ports (positionIn (← c.portPositions.get) a ·)
  let lowerUpperCrossings ← c.withTree countCrossingsOnPorts ports
  c.indexTree.modify (·.clear)
  c.switchPorts lowerPort upperPort
  return (upperLowerCrossings, lowerUpperCrossings)

/-- `countInLayerCrossingsBetweenNodesInBothOrders(upperNode, lowerNode, side)`: in-layer
crossings at the two nodes in the current and in the switched order. Initialise with
`initPortPositionsForInLayerCrossings` first. -/
def countInLayerCrossingsBetweenNodesInBothOrders (c : CrossingsCounter) (upperNode lowerNode : LNodeId)
    (side : PortSide) : LayeredM (Int × Int) := do
  let a ← get
  let ports := connectedInLayerPortsSortedByPosition a (← c.portPositions.get) upperNode lowerNode side
  let upperLowerCrossings ← c.withTree countInLayerCrossingsOnPorts ports
  c.switchNodes upperNode lowerNode side
  c.indexTree.modify (·.clear)
  let ports := stableSortByKey ports (positionIn (← c.portPositions.get) a ·)
  let lowerUpperCrossings ← c.withTree countInLayerCrossingsOnPorts ports
  c.switchNodes lowerNode upperNode side
  c.indexTree.modify (·.clear)
  return (upperLowerCrossings, lowerUpperCrossings)

/-- Current port positions (testing/debugging). -/
def currentPositions (c : CrossingsCounter) : BaseIO (Array Int) := c.portPositions.get

end CrossingsCounter

end Elk.Alg.Layered.P3Order.Counting
