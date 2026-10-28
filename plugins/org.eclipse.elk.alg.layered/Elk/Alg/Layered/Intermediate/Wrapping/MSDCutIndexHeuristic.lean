import Elk.Alg.Layered.Intermediate.Wrapping.ARDCutIndexHeuristic
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping.MSDCutIndexHeuristic`

Port of the elk-rs `MSDCutIndexHeuristic` (private struct in `breaking_point_inserter.rs` and
`single_edge_graph_wrapper.rs`, identical in both). For every cut count `m` within
`WRAPPING_CUTTING_MSD_FREEDOM` of the ARD estimate the cuts that balance the row widths are
computed greedily; the set with the largest max scale `min(1 / width, (1 / dar) / height)` wins
(first one on ties).

Rust deviations from Java (followed): empty width arrays yield no cuts; `1 / 0` is spelled out as
`INFINITY` (same value as Java).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0

namespace Elk.Alg.Layered.Intermediate.Wrapping

open Elk.Graph Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace MSDCutIndexHeuristic

/-- The greedy cuts for `m` cuts and the resulting `(width, height)` of the drawing. -/
def cutsFor (gs : GraphStats) (widthAtIndex heights : Array Float) (total : Float) (m : Int) :
    Array Int × Float × Float := Id.run do
  let rowSum := total / (Float.ofInt m + 1.0)
  let mut sumSoFar : Float := 0.0
  let mut index : Nat := 1
  let mut cuts : Array Int := #[]
  let mut width : Float := Float.negInf
  let mut lastCutWidth : Float := 0.0
  let mut height : Float := 0.0
  let mut rowHeightMax : Float := heights[0]!
  if m == 0 then
    width := total
    height := gs.maxHeight
  else
    while index < gs.longestPath do
      if widthAtIndex[index - 1]! - sumSoFar >= rowSum then
        cuts := cuts.push (index : Int)
        width := fmax width (widthAtIndex[index - 1]! - lastCutWidth)
        height := height + rowHeightMax
        sumSoFar := sumSoFar + (widthAtIndex[index - 1]! - sumSoFar)
        lastCutWidth := widthAtIndex[index - 1]!
        rowHeightMax := heights[index]!
      rowHeightMax := fmax rowHeightMax heights[index]!
      index := index + 1
    height := height + rowHeightMax
  return (cuts, width, height)

/-- `getCutIndexes(graph, graphStats)`. -/
def cutIndexes (graph : LGraphId) (gs : GraphStats) : LayeredM (Array Int) := do
  let widths := gs.widths
  let heights := gs.heights
  if widths.isEmpty then return #[]
  let mut widthAtIndex : Array Float := Array.replicate widths.size fl0p0
  widthAtIndex := widthAtIndex.set! 0 widths[0]!
  let mut total := widths[0]!
  for i in [1:widths.size] do
    widthAtIndex := widthAtIndex.set! i (widthAtIndex[i - 1]! + widths[i]!)
    total := total + widths[i]!
  let cutCount := ARDCutIndexHeuristic.getChunkCount gs - 1
  let freedom := ((← getGraph graph).props.get LayeredOptions.WRAPPING_CUTTING_MSD_FREEDOM).getD 1
  let mut bestMaxScale := Float.negInf
  let mut bestCuts : Array Int := #[]
  let minM := max (cutCount - freedom) 0
  let maxM := min (cutCount + freedom) ((gs.longestPath : Int) - 1)
  let mut m := minM
  while m <= maxM do
    let (cuts, width, height) := cutsFor gs widthAtIndex heights total m
    let widthScale := if width == fl0p0 then Float.posInf else fl1p0 / width
    let heightScale := if height == fl0p0 then Float.posInf else (fl1p0 / gs.dar) / height
    let maxScale := fmin widthScale heightScale
    if maxScale > bestMaxScale then
      bestMaxScale := maxScale
      bestCuts := cuts
    m := m + 1
  return bestCuts

/-- The `MSDCutIndexHeuristic` calculator (not guaranteed to be valid). -/
def calculator : ICutIndexCalculator where
  getCutIndexes graph gs := cutIndexes graph gs
  guaranteeValid := false

end MSDCutIndexHeuristic

end Elk.Alg.Layered.Intermediate.Wrapping
