import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P3Order.Counting.CrossMinUtil
import Std.Data.HashMap
/-!
# `org.eclipse.elk.alg.layered.intermediate.greedyswitch.NorthSouthEdgeNeighbouringNodeCrossingsCounter`

Crossings caused by north/south port edges between two neighbouring nodes of one layer, in both
orders (elk-rs `north_south_edge_neighbouring_node_crossings_counter.rs`). The northern and
southern ports of every node of the layer are numbered per node and side in
`inNorthSouthEastWestOrder`.
-/
namespace Elk.Alg.Layered.Intermediate.GreedySwitch

open Elk.Core.Options Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.P3Order.Counting

/-- `NorthSouthEdgeNeighbouringNodeCrossingsCounter`. -/
structure NorthSouthEdgeNeighbouringNodeCrossingsCounter where
  /-- `upperLowerCrossings`. -/
  upperLowerRef : IO.Ref Int
  /-- `lowerUpperCrossings`. -/
  lowerUpperRef : IO.Ref Int
  /-- `portPositions`. -/
  portPositions : Std.HashMap LPortId Int
  /-- `layer`. -/
  layer : Array LNodeId

namespace NorthSouthEdgeNeighbouringNodeCrossingsCounter

/-- `new NorthSouthEdgeNeighbouringNodeCrossingsCounter(nodes)`: numbers the southern, then the
northern ports of each node. -/
def new (nodes : Array LNodeId) : LayeredM NorthSouthEdgeNeighbouringNodeCrossingsCounter := do
  let a ← get
  let mut positions : Std.HashMap LPortId Int := {}
  for node in nodes do
    for side in #[PortSide.south, PortSide.north] do
      let ports := CrossMinUtil.inNorthSouthEastWestOrder a node side
      for h : portId in [0:ports.size] do
        positions := positions.insert ports[portId] portId
  return { upperLowerRef := ← IO.mkRef 0, lowerUpperRef := ← IO.mkRef 0, portPositions := positions, layer := nodes }

/-- `upperLowerCrossings` of the last count. -/
def upperLowerCrossings (c : NorthSouthEdgeNeighbouringNodeCrossingsCounter) : BaseIO Int := c.upperLowerRef.get

/-- `lowerUpperCrossings` of the last count. -/
def lowerUpperCrossings (c : NorthSouthEdgeNeighbouringNodeCrossingsCounter) : BaseIO Int := c.lowerUpperRef.get

/-- `isNorthSouth`/`isLongEdgeDummy`/`isNormal`: the node has type `t`. -/
@[inline] private def isType (a : LGraphArena) (n : LNodeId) (t : NodeType) : Bool := (a.node n).type == t

/-- `originPortOf(node)`: `ORIGIN` of the node's first port when it is a port. -/
private def originPortOf (a : LGraphArena) (node : LNodeId) : Option LPortId := do
  let port ← (a.node node).ports[0]?
  match (a.port port).internal.origin with
  | some (.lPort originPort) => some originPort
  | _ => none

/-- `originOf(node)`: the node's `ORIGIN` when it is a node. -/
private def originOf (a : LGraphArena) (node : LNodeId) : Option LNodeId :=
  match (a.node node).internal.origin with
  | some (.lNode n) => some n
  | _ => none

/-- `haveDifferentOrigins(upperNode, lowerNode)`: also `true` when an origin is missing. -/
private def haveDifferentOrigins (a : LGraphArena) (upperNode lowerNode : LNodeId) : Bool :=
  match originOf a upperNode, originOf a lowerNode with
  | some u, some l => u != l
  | _, _ => true

/-- `isNorthOfNormalNode(node)`: the dummy's origin port is a northern port. -/
private def isNorthOfNormalNode (a : LGraphArena) (node : LNodeId) : Bool :=
  match originPortOf a node with
  | some p => (a.port p).side == .north
  | none => false

/-- Degree of the first port of `node` on `side` (`0` without one). -/
@[inline] private def firstPortDegree (a : LGraphArena) (node : LNodeId) (side : PortSide) : Int :=
  match (a.nodePortSideView node side)[0]? with
  | some p => ((a.port p).degree : Int)
  | none => 0

/-- `numberOfNorthSouthEdges(node, side)`: ports on `side` with a `PORT_DUMMY`. -/
private def numberOfNorthSouthEdges (a : LGraphArena) (node : LNodeId) (side : PortSide) : Int :=
  ((a.nodePortSideView node side).filter fun p => (a.port p).internal.portDummy.isSome).size

/-- Pure core of `countCrossings(upperNode, lowerNode)`: `(upperLower, lowerUpper)`. -/
def countCrossingsPure (a : LGraphArena) (portPositions : Std.HashMap LPortId Int) (upperNode lowerNode : LNodeId) :
    Int × Int := Id.run do
  let mut upperLower : Int := 0
  let mut lowerUpper : Int := 0
  let originPortPosition (n : LNodeId) : Int := ((originPortOf a n).bind (portPositions[·]?)).getD 0
  -- processIfTwoNorthSouthNodes
  if isType a upperNode .northSouthPort && isType a lowerNode .northSouthPort && !haveDifferentOrigins a upperNode lowerNode then
    let (furtherFromNormal, closerToNormal) :=
      if isNorthOfNormalNode a upperNode then (upperNode, lowerNode) else (lowerNode, upperNode)
    -- countCrossingsOfTwoNorthSouthDummies
    if originPortPosition furtherFromNormal > originPortPosition closerToNormal then
      upperLower := firstPortDegree a closerToNormal .east
      lowerUpper := firstPortDegree a furtherFromNormal .west
    else
      upperLower := firstPortDegree a closerToNormal .west
      lowerUpper := firstPortDegree a furtherFromNormal .east
  -- processIfNorthSouthLongEdgeDummyCrossing
  if isType a upperNode .northSouthPort && isType a lowerNode .longEdge then
    if isNorthOfNormalNode a upperNode then upperLower := 1 else lowerUpper := 1
  else if isType a lowerNode .northSouthPort && isType a upperNode .longEdge then
    if isNorthOfNormalNode a lowerNode then lowerUpper := 1 else upperLower := 1
  -- processIfNormalNodeWithNSPortsAndLongEdgeDummy
  if isType a upperNode .normal && isType a lowerNode .longEdge then
    upperLower := numberOfNorthSouthEdges a upperNode .south
    lowerUpper := numberOfNorthSouthEdges a upperNode .north
  if isType a lowerNode .normal && isType a upperNode .longEdge then
    upperLower := numberOfNorthSouthEdges a lowerNode .north
    lowerUpper := numberOfNorthSouthEdges a lowerNode .south
  return (upperLower, lowerUpper)

/-- `countCrossings(upperNode, lowerNode)`: stores both counts. -/
def countCrossings (c : NorthSouthEdgeNeighbouringNodeCrossingsCounter) (upperNode lowerNode : LNodeId) : LayeredM Unit := do
  let (upperLower, lowerUpper) := countCrossingsPure (← get) c.portPositions upperNode lowerNode
  c.upperLowerRef.set upperLower
  c.lowerUpperRef.set lowerUpper

end NorthSouthEdgeNeighbouringNodeCrossingsCounter

end Elk.Alg.Layered.Intermediate.GreedySwitch
