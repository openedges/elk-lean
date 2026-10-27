import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P3Order.Counting.CrossingsCounter
import Elk.Alg.Layered.Intermediate.GreedySwitch.CrossingMatrixFiller
import Elk.Alg.Layered.Intermediate.GreedySwitch.NorthSouthEdgeNeighbouringNodeCrossingsCounter
/-!
# `org.eclipse.elk.alg.layered.intermediate.greedyswitch.SwitchDecider`

Decides whether switching two neighbouring nodes of the free layer reduces crossings (elk-rs
`switch_decider.rs`): between-layer crossings from the `CrossingMatrixFiller`, in-layer crossings
on both sides, north/south crossings of neighbouring nodes and, for external port dummies of a
nested graph, the crossings their switch causes in the parent graph.

elk-rs passes the free layer's nodes instead of indices (Java `doesSwitchReduceCrossings(int,
int)`) and the parent data as an explicit `ParentCrossingContext` instead of reading the parent
`GraphInfoHolder`; every counter gets its own copy of the port positions (Java shares the array).
-/
namespace Elk.Alg.Layered.Intermediate.GreedySwitch

open Elk.Core.Options Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.P3Order.Counting

/-- elk-rs `ParentCrossingContext`: the parent graph's node order and port positions, the layer
index of the parent node and whether the free layer is the rightmost one. -/
structure ParentCrossingContext where
  parentNodeOrder : Array (Array LNodeId)
  parentPortPositions : Array Int
  parentLayerIndex : Nat
  rightMostLayer : Bool
  deriving Inhabited

/-- `SwitchDecider`. -/
structure SwitchDecider where
  /-- `leftInLayerCounter` (western in-layer crossings). -/
  leftInLayerCounter : CrossingsCounter
  /-- `rightInLayerCounter` (eastern in-layer crossings). -/
  rightInLayerCounter : CrossingsCounter
  /-- `northSouthCounter`. -/
  northSouthCounter : NorthSouthEdgeNeighbouringNodeCrossingsCounter
  /-- `crossingMatrixFiller`. -/
  crossingMatrixFiller : CrossingMatrixFiller
  /-- `parentCrossCounter`. -/
  parentCrossCounter : Option CrossingsCounter
  /-- `countCrossingsCausedByPortSwitch`. -/
  countCrossingsCausedByPortSwitch : Bool

namespace SwitchDecider

/-- `initParentCrossingsCounters`: a counter over the parent's layers next to the parent node
(the parent node's layer and its right neighbour for the rightmost free layer, else the left
neighbour and the parent node's layer). -/
private def initParentCrossCounter (context : ParentCrossingContext) : LayeredM CrossingsCounter := do
  let counter ← CrossingsCounter.ofPositions context.parentPortPositions
  let layers := context.parentNodeOrder
  let i := context.parentLayerIndex
  let leftLayer := if i > 0 then (layers[i - 1]?).getD #[] else #[]
  let middleLayer := (layers[i]?).getD #[]
  let rightLayer := if i + 1 < layers.size then (layers[i + 1]?).getD #[] else #[]
  if context.rightMostLayer then
    counter.initForCountingBetween middleLayer rightLayer
  else
    counter.initForCountingBetween leftLayer middleLayer
  return counter

/-- `new SwitchDecider(freeLayer, crossingMatrixFiller, portPositions, parentContext,
countCrossingsCausedByPortSwitch)` (elk-rs signature). -/
def new (freeLayer : Array LNodeId) (crossingMatrixFiller : CrossingMatrixFiller) (portPositions : Array Int)
    (parentContext : Option ParentCrossingContext) (countCrossingsCausedByPortSwitch : Bool) : LayeredM SwitchDecider := do
  let leftInLayerCounter ← CrossingsCounter.ofPositions portPositions
  let _ ← leftInLayerCounter.initPortPositionsForInLayerCrossings freeLayer .west
  let rightInLayerCounter ← CrossingsCounter.ofPositions portPositions
  let _ ← rightInLayerCounter.initPortPositionsForInLayerCrossings freeLayer .east
  let northSouthCounter ← NorthSouthEdgeNeighbouringNodeCrossingsCounter.new freeLayer
  let parentCrossCounter ← if countCrossingsCausedByPortSwitch then
      match parentContext with
      | some context => pure (some (← initParentCrossCounter context))
      | none => pure none
    else pure none
  return { leftInLayerCounter, rightInLayerCounter, northSouthCounter, crossingMatrixFiller, parentCrossCounter,
           countCrossingsCausedByPortSwitch }

/-- The `ORIGIN` of a node when it is a port (external port dummies). -/
private def originPortOf (node : LNodeId) : LayeredM (Option LPortId) := do
  match (← LayeredM.getNode node).internal.origin with
  | some (.lPort p) => return some p
  | _ => return none

/-- `notifyOfSwitch(upperNode, lowerNode)`: keeps the in-layer (and parent) counters in sync. -/
def notifyOfSwitch (d : SwitchDecider) (upperNode lowerNode : LNodeId) : LayeredM Unit := do
  d.leftInLayerCounter.switchNodes upperNode lowerNode .west
  d.rightInLayerCounter.switchNodes upperNode lowerNode .east
  if d.countCrossingsCausedByPortSwitch then
    if let (some upperPort, some lowerPort) := (← originPortOf upperNode, ← originPortOf lowerNode) then
      if let some counter := d.parentCrossCounter then
        counter.switchPorts upperPort lowerPort

/-- `haveSuccessorConstraints(upperNode, lowerNode)`. -/
private def haveSuccessorConstraints (a : LGraphArena) (upperNode lowerNode : LNodeId) : Bool :=
  let constraints := (a.node upperNode).internal.inLayerSuccessorConstraints
  !constraints.isEmpty && constraints.contains lowerNode

/-- `hasEdgesOnSide(node, side)`: a port on `side` has a `PORT_DUMMY` or edges. -/
private def hasEdgesOnSide (a : LGraphArena) (node : LNodeId) (side : PortSide) : Bool :=
  (a.nodePortSideView node side).any fun p =>
    let pt := a.port p
    pt.internal.portDummy.isSome || !pt.connectedEdges.isEmpty

/-- `partOfMultiNodeLayoutUnit(node, layoutUnit)`. -/
@[inline] private def partOfMultiNodeLayoutUnit (node : LNodeId) (layoutUnit : Option LNodeId) : Bool :=
  match layoutUnit with
  | some unit => unit != node
  | none => false

/-- `haveLayoutUnitConstraints(upperNode, lowerNode)`. -/
private def haveLayoutUnitConstraints (a : LGraphArena) (upperNode lowerNode : LNodeId) : Bool :=
  let upper := a.node upperNode
  let lower := a.node lowerNode
  let neitherLongEdge := upper.type != .longEdge && lower.type != .longEdge
  let upperLayoutUnit := upper.internal.inLayerLayoutUnit
  let lowerLayoutUnit := lower.internal.inLayerLayoutUnit
  let areInDifferentLayoutUnits : Bool := match upperLayoutUnit, lowerLayoutUnit with
    | some u, some l => u != l
    | none, none => false
    | _, _ => true
  let nodesHaveLayoutUnits := partOfMultiNodeLayoutUnit upperNode upperLayoutUnit
    || partOfMultiNodeLayoutUnit lowerNode lowerLayoutUnit
  let upperHasNorthernEdges := hasEdgesOnSide a upperNode .north
  let lowerHasSouthernEdges := hasEdgesOnSide a lowerNode .south
  let nodesHaveLayoutUnits := nodesHaveLayoutUnits || hasEdgesOnSide a upperNode .south
    || hasEdgesOnSide a lowerNode .north
  let hasLayoutUnitConstraint := (nodesHaveLayoutUnits && areInDifferentLayoutUnits)
    || upperHasNorthernEdges || lowerHasSouthernEdges
  neitherLongEdge && hasLayoutUnitConstraint

/-- `areNormalAndNorthSouthPortDummy(upperNode, lowerNode)`. -/
private def areNormalAndNorthSouthPortDummy (a : LGraphArena) (upperNode lowerNode : LNodeId) : Bool :=
  let ut := (a.node upperNode).type
  let lt := (a.node lowerNode).type
  (ut == .northSouthPort && lt == .normal) || (lt == .northSouthPort && ut == .normal)

/-- `constraintsPreventSwitch(upperNode, lowerNode)`. -/
def constraintsPreventSwitch (a : LGraphArena) (upperNode lowerNode : LNodeId) : Bool :=
  haveSuccessorConstraints a upperNode lowerNode || haveLayoutUnitConstraints a upperNode lowerNode
    || areNormalAndNorthSouthPortDummy a upperNode lowerNode

/-- `doesSwitchReduceCrossings(upperNode, lowerNode)`. -/
def doesSwitchReduceCrossings (d : SwitchDecider) (upperNode lowerNode : LNodeId) : LayeredM Bool := do
  if constraintsPreventSwitch (← get) upperNode lowerNode then return false
  let leftInLayer ← d.leftInLayerCounter.countInLayerCrossingsBetweenNodesInBothOrders upperNode lowerNode .west
  let rightInLayer ← d.rightInLayerCounter.countInLayerCrossingsBetweenNodesInBothOrders upperNode lowerNode .east
  d.northSouthCounter.countCrossings upperNode lowerNode
  let mut upperLowerCrossings := (← d.crossingMatrixFiller.crossingMatrixEntry upperNode lowerNode)
    + leftInLayer.1 + rightInLayer.1 + (← d.northSouthCounter.upperLowerCrossings)
  let mut lowerUpperCrossings := (← d.crossingMatrixFiller.crossingMatrixEntry lowerNode upperNode)
    + leftInLayer.2 + rightInLayer.2 + (← d.northSouthCounter.lowerUpperCrossings)
  if d.countCrossingsCausedByPortSwitch then
    if let (some upperPort, some lowerPort) := (← originPortOf upperNode, ← originPortOf lowerNode) then
      if let some counter := d.parentCrossCounter then
        let crossingNumbers ← counter.countCrossingsBetweenPortsInBothOrders upperPort lowerPort
        upperLowerCrossings := upperLowerCrossings + crossingNumbers.1
        lowerUpperCrossings := lowerUpperCrossings + crossingNumbers.2
  return upperLowerCrossings > lowerUpperCrossings

end SwitchDecider

end Elk.Alg.Layered.Intermediate.GreedySwitch
