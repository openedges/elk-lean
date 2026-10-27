import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.P3Order.CrossMinType
import Elk.Alg.Layered.P3Order.Counting.BinaryIndexedTree
import Elk.Alg.Layered.Intermediate.GreedySwitch.BetweenLayerEdgeTwoNodeCrossingsCounter
/-!
# `org.eclipse.elk.alg.layered.intermediate.greedyswitch.CrossingMatrixFiller`

Lazily filled matrix of the between-layer crossings of every node pair of the free layer
(elk-rs `crossing_matrix_filler.rs`), indexed by `LNode.id` (the node's index in its layer).
Also declares `SwitchDecider.CrossingCountSide`, which this module needs and `SwitchDecider`
imports.
-/
namespace Elk.Alg.Layered.Intermediate.GreedySwitch

open Elk.Alg.Layered.Graph Elk.Alg.Layered.P3Order Elk.Alg.Layered.P3Order.Counting

/-- `SwitchDecider.CrossingCountSide`: the side whose between-layer edges a one-sided greedy
switch counts. -/
elk_enum CrossingCountSide := west east

/-- `CrossingMatrixFiller`. -/
structure CrossingMatrixFiller where
  /-- `isCrossingMatrixFilled`. -/
  isCrossingMatrixFilled : IO.Ref (Array (Array Bool))
  /-- `crossingMatrix`. -/
  crossingMatrix : IO.Ref (Array (Array Int))
  /-- `inBetweenLayerCrossingCounter`. -/
  inBetweenLayerCrossingCounter : BetweenLayerEdgeTwoNodeCrossingsCounter
  /-- `direction`. -/
  direction : CrossingCountSide
  /-- `oneSided`. -/
  oneSided : Bool

namespace CrossingMatrixFiller

/-- `new CrossingMatrixFiller(greedySwitchType, graph, freeLayerIndex, direction)`. -/
def new (greedySwitchType : CrossMinType) (graph : Array (Array LNodeId)) (freeLayerIndex : Nat)
    (direction : CrossingCountSide) : LayeredM CrossingMatrixFiller := do
  let freeLayerLen := ((graph[freeLayerIndex]?).map (·.size)).getD 0
  return {
    isCrossingMatrixFilled := ← IO.mkRef (Array.replicate freeLayerLen (Array.replicate freeLayerLen false))
    crossingMatrix := ← IO.mkRef (Array.replicate freeLayerLen (Array.replicate freeLayerLen 0))
    inBetweenLayerCrossingCounter := ← BetweenLayerEdgeTwoNodeCrossingsCounter.new graph freeLayerIndex
    direction
    oneSided := greedySwitchType == .oneSidedGreedySwitch }

/-- Rust `node_id(node)`: `node.id as usize`. -/
@[inline] private def nodeIdOf (n : LNodeId) : LayeredM Nat := do return asUsize (← LayeredM.getNode n).id

/-- `fillCrossingMatrix(upperNode, lowerNode)`. -/
private def fillCrossingMatrix (f : CrossingMatrixFiller) (upperNode lowerNode : LNodeId) : LayeredM Unit := do
  let counter := f.inBetweenLayerCrossingCounter
  if f.oneSided then
    match f.direction with
    | .east => counter.countEasternEdgeCrossings upperNode lowerNode
    | .west => counter.countWesternEdgeCrossings upperNode lowerNode
  else
    counter.countBothSideCrossings upperNode lowerNode
  let upperId ← nodeIdOf upperNode
  let lowerId ← nodeIdOf lowerNode
  let n := (← f.crossingMatrix.get).size
  if upperId >= n || lowerId >= n then return
  let upperLower ← counter.upperLowerCrossings
  let lowerUpper ← counter.lowerUpperCrossings
  f.crossingMatrix.modify fun m =>
    (m.modify upperId (·.setIfInBounds lowerId upperLower)).modify lowerId (·.setIfInBounds upperId lowerUpper)

/-- `getCrossingMatrixEntry(upperNode, lowerNode)`: fills the pair on first access. -/
def crossingMatrixEntry (f : CrossingMatrixFiller) (upperNode lowerNode : LNodeId) : LayeredM Int := do
  let upperId ← nodeIdOf upperNode
  let lowerId ← nodeIdOf lowerNode
  let filled ← f.isCrossingMatrixFilled.get
  if upperId >= filled.size || lowerId >= filled.size then return 0
  if !((filled[upperId]!)[lowerId]?.getD false) then
    f.fillCrossingMatrix upperNode lowerNode
    f.isCrossingMatrixFilled.modify fun m =>
      (m.modify upperId (·.setIfInBounds lowerId true)).modify lowerId (·.setIfInBounds upperId true)
  return ((← f.crossingMatrix.get)[upperId]!)[lowerId]?.getD 0

end CrossingMatrixFiller

end Elk.Alg.Layered.Intermediate.GreedySwitch
