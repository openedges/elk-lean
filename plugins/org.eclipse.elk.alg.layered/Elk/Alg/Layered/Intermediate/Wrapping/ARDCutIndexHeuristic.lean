import Elk.Alg.Layered.Intermediate.Wrapping.ICutIndexCalculator
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping.ARDCutIndexHeuristic`

Port of the elk-rs `ARDCutIndexHeuristic` (private struct in `breaking_point_inserter.rs` and
`single_edge_graph_wrapper.rs`, identical in both). From the desired aspect ratio the number of
chunks is derived, then equidistant cut indexes are chosen.

Rust deviations from Java (followed): `getChunkCount` returns `longestPath` when
`dar * maxHeight == 0` (Java divides by zero); `as i32` saturates (`NaN` → `0`).
-/
namespace Elk.Alg.Layered.Intermediate.Wrapping

open Elk.Graph Elk.Alg.Layered.Graph LayeredM

/-- Rust `f64 as i32`: saturating, `NaN` → `0`. -/
def floatToI32Sat (x : Float) : Int :=
  if x != x then 0
  else if x >= 2147483647.0 then 2147483647
  else if x <= -2147483648.0 then -2147483648
  else x.toInt64.toInt

namespace ARDCutIndexHeuristic

/-- `getChunkCount(graphStats)`: `round(sqrt(sumWidth / (dar * maxHeight)))`, at most
`longestPath`. -/
def getChunkCount (gs : GraphStats) : Int :=
  let denominator := gs.dar * gs.maxHeight
  if denominator == 0.0 then (gs.longestPath : Int)
  else
    let rows := floatToI32Sat (Float.sqrt (gs.sumWidth / denominator)).round
    min rows (gs.longestPath : Int)

/-- `getCutIndexes(graph, graphStats)`: `round(i * longestPath / rows)` for `i ∈ [1, rows)`. -/
def cutIndexes (gs : GraphStats) : Array Int := Id.run do
  let rows := getChunkCount gs
  if rows <= 1 then return #[]
  let mut cuts : Array Int := #[]
  let step := gs.longestPath.toFloat / Float.ofInt rows
  for idx in [1:rows.toNat] do
    cuts := cuts.push (floatToI32Sat (idx.toFloat * step).round)
  return cuts

/-- The `ARDCutIndexHeuristic` calculator (not guaranteed to be valid). -/
def calculator : ICutIndexCalculator where
  getCutIndexes _ gs := return cutIndexes gs
  guaranteeValid := false

end ARDCutIndexHeuristic

end Elk.Alg.Layered.Intermediate.Wrapping
