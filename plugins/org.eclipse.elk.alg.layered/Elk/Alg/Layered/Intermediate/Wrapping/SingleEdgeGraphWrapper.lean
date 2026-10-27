import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Intermediate.Wrapping.MSDCutIndexHeuristic
import Elk.Alg.Layered.Intermediate.Wrapping.CuttingUtils
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping.SingleEdgeGraphWrapper`

Port of elk-rs `intermediate/single_edge_graph_wrapper.rs`. Splits path-like graphs into several
rows ("chunks") to approach the desired aspect ratio: after crossing minimization the cut indexes
are computed (`WRAPPING_CUTTING_STRATEGY`: `MANUAL`, `ARD`, default `MSD`), made valid
(`WRAPPING_VALIDIFY_STRATEGY`: `LOOK_BACK`, `GREEDY` (default), `NO`), and the layers after each
cut are moved back to the first layers. Edges entering the first layer of a new row are reversed
(the graph becomes `CYCLIC`) and get in-layer/long edge dummies (`CuttingUtils.insertDummies`).

Rust deviations from Java (followed):
* the early exit computes `currentAR = 0` for `maxWidth == 0` (Java `NaN`, never exits);
* `validifyIndexesGreedily` treats negative indexes as forbidden (Java throws);
* `validifyIndexesLookingBack` uses saturating `i32` distances (Java's `current - MIN_VALUE`
  overflows) and bounds checks; the running offset is an unbounded `Int` here (Rust `i32`, only
  different for cuts next to the `±inf` sentinels);
* `performCuts` stops when an index leaves the layer list.

Slots: before phase 4.
-/
namespace Elk.Alg.Layered.Intermediate.Wrapping

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

/-- `ICutIndexCalculator` for a `CuttingStrategy` (the `match` of both Rust processors). -/
def cutIndexCalculatorFor : CuttingStrategy → ICutIndexCalculator
  | .manual => ICutIndexCalculator.manual
  | .ard => ARDCutIndexHeuristic.calculator
  | .msd => MSDCutIndexHeuristic.calculator

namespace SingleEdgeGraphWrapper

/-- `i32::MIN`. -/
def I32_MIN : Int := -2147483648
/-- `i32::MAX`. -/
def I32_MAX : Int := 2147483647

/-- Rust `i32::saturating_sub`. -/
def saturatingSubI32 (a b : Int) : Int := max I32_MIN (min I32_MAX (a - b))

/-- `validifyIndexesGreedily(graphStats, cuts)`: shifts every forbidden cut (and with it all
following cuts) to the next allowed index; cuts that fall off the end are dropped. -/
def validifyIndexesGreedily (gs : GraphStats) (cuts : Array Int) : Array Int := Id.run do
  let mut validCuts : Array Int := #[]
  let mut offset : Int := 0
  let lp : Int := gs.longestPath
  for cut in cuts do
    let mut shifted := cut + offset
    while shifted < lp && !gs.isCutAllowed shifted do
      shifted := shifted + 1
      offset := offset + 1
    if shifted >= lp then break
    validCuts := validCuts.push shifted
  return validCuts

/-- `validifyIndexesLookingBack(desiredCuts, validCuts)`: `validCuts` starts with `-inf`
(`i32::MIN`) and ends with `+inf` (`i32::MAX`); every desired cut (shifted by the accumulated
offset) snaps to the nearer of the enclosing valid cuts (the lower one on ties). -/
def validifyIndexesLookingBackWithValids (desiredCuts validCuts : Array Int) : Array Int := Id.run do
  if desiredCuts.isEmpty || validCuts.size < 2 then return #[]
  let mut finalCuts : Array Int := #[]
  let mut iIdx : Nat := 0
  let mut cIdx : Nat := 0
  let mut offset : Int := 0
  while iIdx < validCuts.size - 1 && cIdx < desiredCuts.size do
    let current := desiredCuts[cIdx]! + offset
    while iIdx + 1 < validCuts.size && validCuts[iIdx + 1]! < current do
      iIdx := iIdx + 1
    if iIdx + 1 >= validCuts.size then break
    let mut select : Nat := 0
    let distLower := saturatingSubI32 current validCuts[iIdx]!
    let distHigher := saturatingSubI32 validCuts[iIdx + 1]! current
    if distLower > distHigher then select := 1
    let selected := validCuts[iIdx + select]!
    finalCuts := finalCuts.push selected
    offset := offset + (selected - current)
    cIdx := cIdx + 1
    while cIdx < desiredCuts.size && desiredCuts[cIdx]! + offset <= selected do
      cIdx := cIdx + 1
    iIdx := iIdx + 1 + select
  return finalCuts

/-- `validifyIndexesLookingBack(graphStats, desiredCuts)`: the allowed indexes `1 ≤ i <
longestPath` framed by the sentinels; no cuts if there is no allowed index. -/
def validifyIndexesLookingBack (gs : GraphStats) (desiredCuts : Array Int) : Array Int := Id.run do
  if desiredCuts.isEmpty then return #[]
  let mut validCuts : Array Int := #[I32_MIN]
  for idx in [1:gs.longestPath] do
    if gs.isCutAllowed idx then validCuts := validCuts.push idx
  if validCuts.size == 1 then return #[]
  validCuts := validCuts.push I32_MAX
  return validifyIndexesLookingBackWithValids desiredCuts validCuts

/-- Moves the nodes of one old layer to the end of `newLayer`; at the start of a row
(`newIndex == 0`) the incoming edges of each moved node are reversed and get dummies. -/
private def moveLayer (graph : LGraphId) (oldLayer newLayer : LayerId) (startOfRow : Bool) : LayeredM Unit := do
  let nodesToMove := (← getLayer oldLayer).nodes
  for node in nodesToMove do
    let insertIndex := (← getLayer newLayer).nodes.size
    setNodeLayerAtIndex node insertIndex (some newLayer)
    if startOfRow then
      let incomingEdges ← withArena (·.nodeIncomingEdges node)
      for edge in incomingEdges do
        LGraphUtil.reverseEdge edge graph true
        modifyGraph graph fun g => { g with internal := { g.internal with cyclic := true } }
        let _ ← CuttingUtils.insertDummies graph edge 1

/-- `performCuts(graph, graphStats, cuts)`: rebuilds the layering row by row and removes the
emptied layers. Preconditions (Java): all cuts allowed, increasing, below the layer count. -/
def performCuts (graph : LGraphId) (gs : GraphStats) (cuts : Array Int) : LayeredM Unit := do
  if cuts.isEmpty then return
  let mut index : Nat := 0
  let mut newIndex : Nat := 0
  let mut cutPos : Nat := 1
  let noCut : Int := (gs.longestPath : Int) + 1
  let mut nextCut : Int := cuts[0]!
  while index < gs.longestPath do
    if (index : Int) == nextCut then
      newIndex := 0
      nextCut := cuts.getD cutPos noCut
      cutPos := cutPos + 1
    if index != newIndex then
      let layers := (← getGraph graph).layers
      if index >= layers.size || newIndex >= layers.size then break
      moveLayer graph layers[index]! layers[newIndex]! (newIndex == 0)
    newIndex := newIndex + 1
    index := index + 1
  let layers := (← getGraph graph).layers
  let mut kept : Array LayerId := #[]
  for l in layers do
    if !(← getLayer l).nodes.isEmpty then kept := kept.push l
  modifyGraph graph fun g => { g with layers := kept }

/-- `process(graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Path-Like Graph Wrapping" 1.0
  if (← getGraph graph).layers.isEmpty then
    monitor.done
    return
  let gs ← GraphStats.new graph
  -- Keep Java behavior: this simplifies to longestPath and is used as-is there.
  let sumWidth := gs.maxWidth * gs.longestPath.toFloat
  let currentAR := if gs.maxWidth == 0.0 then 0.0 else sumWidth / gs.maxWidth
  if gs.dar > currentAR then
    monitor.done
    return
  let gr ← getGraph graph
  let cuttingStrategy := (gr.props.get LayeredOptions.WRAPPING_CUTTING_STRATEGY).getD .msd
  let calculator := cutIndexCalculatorFor cuttingStrategy
  let mut cuts ← calculator.getCutIndexes graph gs
  if !calculator.guaranteeValid then
    match (gr.props.get LayeredOptions.WRAPPING_VALIDIFY_STRATEGY).getD .greedy with
    | .lookBack => cuts := validifyIndexesLookingBack gs cuts
    | .greedy => cuts := validifyIndexesGreedily gs cuts
    | .no => pure ()
  performCuts graph gs cuts
  monitor.done

/-- The `SingleEdgeGraphWrapper` processor. -/
def processor : LayeredProcessor := { name := "SingleEdgeGraphWrapper", process := process }

end SingleEdgeGraphWrapper

builtin_initialize registerSingleEdgeGraphWrapper : Unit ←
  IntermediateProcessorStrategy.register .singleEdgeGraphWrapper SingleEdgeGraphWrapper.processor

end Elk.Alg.Layered.Intermediate.Wrapping
