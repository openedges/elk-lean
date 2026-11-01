import Elk.Alg.Layered.Intermediate.Wrapping.ICutIndexCalculator
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping.ARDCutIndexHeuristic`

Port of the elk-rs `ARDCutIndexHeuristic` (private struct in `breaking_point_inserter.rs` and
`single_edge_graph_wrapper.rs`, identical in both). From the desired aspect ratio the number of
chunks is derived, then equidistant cut indexes are chosen.

Follows Java (agent COV): `getChunkCount` is `(int) Math.round(Math.sqrt(sumWidth / (dar *
maxHeight)))` with Java's semantics — `x / 0` is `±Infinity` (or `NaN`), `Math.round` maps `NaN` to
`0` and saturates to `long`, and the `(int)` cast keeps the low 32 bits, so a zero denominator
yields `-1` rows (`Long.MAX_VALUE` → `-1`) and no cuts; elk-rs returned `longestPath` there and
saturated the cast to `i32`.
-/
namespace Elk.Alg.Layered.Intermediate.Wrapping

open Elk.Graph Elk.Core.Util Elk.Alg.Layered.Graph LayeredM

/-- Java `(int) Math.round(x)`: `Math.round` (`floor(x + 0.5)`, `NaN` → `0`, saturating to `long`)
followed by the narrowing `long → int` cast (low 32 bits). -/
def javaRoundToInt (x : Float) : Int := Int.wrap32 x.javaRound

namespace ARDCutIndexHeuristic

/-- `getChunkCount(graphStats)`: `(int) Math.round(Math.sqrt(sumWidth / (dar * maxHeight)))`, at most
`longestPath`. -/
def getChunkCount (gs : GraphStats) : Int :=
  let rows := javaRoundToInt (Float.sqrt (gs.sumWidth / (gs.dar * gs.maxHeight)))
  min rows (gs.longestPath : Int)

/-- `getCutIndexes(graph, graphStats)`: `(int) Math.round(idx * step)` with
`step = longestPath / (double) rows` for `idx ∈ [1, rows)`. -/
def cutIndexes (gs : GraphStats) : Array Int := Id.run do
  let rows := getChunkCount gs
  let mut cuts : Array Int := #[]
  let step := gs.longestPath.toFloat / Float.ofInt rows
  for idx in [1:rows.toNat] do
    cuts := cuts.push (javaRoundToInt (idx.toFloat * step))
  return cuts

/-- The `ARDCutIndexHeuristic` calculator (not guaranteed to be valid). -/
def calculator : ICutIndexCalculator where
  getCutIndexes _ gs := return cutIndexes gs
  guaranteeValid := false

end ARDCutIndexHeuristic

end Elk.Alg.Layered.Intermediate.Wrapping
