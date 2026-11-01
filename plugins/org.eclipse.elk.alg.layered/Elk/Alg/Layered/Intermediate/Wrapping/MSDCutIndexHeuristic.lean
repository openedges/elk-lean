import Elk.Alg.Layered.Intermediate.Wrapping.ARDCutIndexHeuristic
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping.MSDCutIndexHeuristic`

Port of the elk-rs `MSDCutIndexHeuristic` (private struct in `breaking_point_inserter.rs` and
`single_edge_graph_wrapper.rs`, identical in both). For every cut count `m` within
`WRAPPING_CUTTING_MSD_FREEDOM` of the ARD estimate the cuts that balance the row widths are
computed greedily; the set with the largest max scale `min(1 / width, (1 / dar) / height)` wins
(first one on ties).

Follows Java (agent COV): the scales are the IEEE quotients `1d / width` and `(1d / dar) / height`
(elk-rs spelled `1 / 0` out as `+INFINITY`, which differs from Java for `-0.0` and for
`(1 / dar) / 0` with `dar < 0`), `Math.max`/`Math.min` with Java's `NaN` semantics, and the guess
of `ARDCutIndexHeuristic.getChunkCount` with Java's rounding. Empty width arrays (no layers) yield no
cuts; this cannot happen in the layered pipeline (Java would throw an
`ArrayIndexOutOfBoundsException` on `widths[0]`).
-/

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
        width := javaMax width (widthAtIndex[index - 1]! - lastCutWidth)
        height := height + rowHeightMax
        sumSoFar := sumSoFar + (widthAtIndex[index - 1]! - sumSoFar)
        lastCutWidth := widthAtIndex[index - 1]!
        rowHeightMax := heights[index]!
      rowHeightMax := javaMax rowHeightMax heights[index]!
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
  -- Java `int` arithmetic (wraps on overflow)
  let cutCount := Int.wrap32 (ARDCutIndexHeuristic.getChunkCount gs - 1)
  let freedom := ((← getGraph graph).props.get LayeredOptions.WRAPPING_CUTTING_MSD_FREEDOM).getD 1
  let mut bestMaxScale := Float.negInf
  let mut bestCuts : Array Int := #[]
  let minM := max 0 (Int.wrap32 (cutCount - freedom))
  let maxM := min ((gs.longestPath : Int) - 1) (Int.wrap32 (cutCount + freedom))
  let mut m := minM
  while m <= maxM do
    let (cuts, width, height) := cutsFor gs widthAtIndex heights total m
    let maxScale := javaMin (fl1p0 / width) ((fl1p0 / gs.dar) / height)
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
