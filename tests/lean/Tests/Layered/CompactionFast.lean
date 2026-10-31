import Tests.Framework
import Tests.AlgCommon.CompactionFast
import Elk.Alg.Layered
import Elk.Alg.Layered.Components
/-! Differential tests of the layered compaction fast paths (round 13, CMP) against the kept
reference implementations:

* `layered.intermediate.compaction.edgeAwareSweepFast`: `EdgeAwareScanlineConstraintCalculation.sweep`
  (precomputed keys, pure kernel without the invalid hitbox check) against `sweepReference`, with
  filters selecting subsets;
* `layered.components.packFastPath`: `OneDimensionalComponentsCompaction.pack` with the fast path
  (moved projection members, skipped repeated constraint calculation) against `fastPath := false`
  on random components (hulls, external sides with extensions), offsets and size by bit pattern
  and exception text. -/
namespace Tests.Layered.CompactionFast

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Alg.Common.Compaction.OneD
open Elk.Alg.Layered.Intermediate.Compaction Elk.Alg.Layered.Components.Compaction
open Tests.AlgCommon.CompactionFast

def edgeAwareSweepFast : Suite := suite "layered.intermediate.compaction.edgeAwareSweepFast" do
  let mut same := 0
  let mut total := 0
  let mut changed := 0
  for seed in [1:301] do
    let n := seed % 23 + 1
    let g := randomGraph (seed.toUInt64 * 65537) n (seed % 5 + 1) (seed % 7 == 0)
    let st : CompactorState := { cGraph := g }
    for k in [0:4] do
      let filter : CNodeId → Bool := fun c => match k with
        | 0 => true
        | 1 => c.idx % 2 == 0
        | 2 => (c.idx + seed) % 3 != 0
        | _ => false
      let a ← outcome (EdgeAwareScanlineConstraintCalculation.sweep filter) st
      let b ← outcome (EdgeAwareScanlineConstraintCalculation.sweepReference filter) st
      total := total + 1
      if a.length != (graphKey g).length then changed := changed + 1
      if a == b then same := same + 1 else IO.println s!"edge-aware sweep mismatch seed {seed} filter {k}"
  checkEq "sweep = sweepReference" same total
  report "edge-aware sweeps add constraints" (changed * 2 >= total) s!"{changed}/{total}"

/-- Random components in the shape `ComponentsCompactor.transform` produces: hull rectangles in the
cells of one row of a `1000 × 1000` frame, and per external side an extension from the hull bound
to the frame border with a placeholder of width 2 at the border (west only for the first, east
only for the last component, so that no extension crosses another component: crossing hitboxes
form constraint cycles, which leave groups unplaced and end in the non-finite size exception). -/
def randomComponents (seed : UInt64) (count : Nat) : Array Component := Id.run do
  let mut s := seed
  let mut out : Array Component := #[]
  for i in [0:count] do
    let ox := 100.0 + 300.0 * (i % 3).toFloat
    let oy := 300.0
    let (s1, rects) := below s 4
    s := s1
    let mut hull : Array ElkRectangle := #[]
    let mut minX := 1.0e9
    let mut minY := 1.0e9
    let mut maxX := -1.0e9
    let mut maxY := -1.0e9
    for _ in [0:rects + 1] do
      let (s2, dx) := below s 60
      let (s3, dy) := below s2 60
      let (s4, w) := below s3 40
      let (s5, h) := below s4 40
      s := s5
      let r := ElkRectangle.ofValues (ox + dx.toFloat) (oy + dy.toFloat) (w.toFloat + 1.0) (h.toFloat + 1.0)
      minX := min minX r.x
      minY := min minY r.y
      maxX := max maxX (r.x + r.width)
      maxY := max maxY (r.y + r.height)
      hull := hull.push r
    let (s6, mask) := below s 16
    s := s6
    let mut sides : EnumSet PortSide := EnumSet.noneOf
    if mask % 2 == 1 then sides := sides.insert .north
    if (mask / 2) % 2 == 1 && i + 1 == count then sides := sides.insert .east
    if (mask / 4) % 2 == 1 then sides := sides.insert .south
    if (mask / 8) % 2 == 1 && i == 0 then sides := sides.insert .west
    let mut extensions : Array ComponentExtension := #[]
    for side in sides.toArray do
      let (s7, t) := below s 50
      let (s8, len) := below s7 15
      s := s8
      let len := len.toFloat + 1.0
      let (rect, ph) : ElkRectangle × ElkRectangle := match side with
        | .north => let lo := minX + t.toFloat; (⟨lo, 0.0, len, minY⟩, ⟨lo, 0.0, len, 2.0⟩)
        | .south => let lo := minX + t.toFloat; (⟨lo, maxY, len, 1000.0 - maxY⟩, ⟨lo, 998.0, len, 2.0⟩)
        | .west => let lo := minY + t.toFloat; (⟨0.0, lo, minX, len⟩, ⟨0.0, lo, 2.0, len⟩)
        | _ => let lo := minY + t.toFloat; (⟨maxX, lo, 1000.0 - maxX, len⟩, ⟨998.0, lo, 2.0, len⟩)
      extensions := extensions.push { rectangle := rect, placeholder := ph, side }
    out := out.push { hull, sides, extensions, externalEdges := #[] }
  return out

def packOutcome (cs : Array Component) (spacing : Float) (fast : Bool) : IO String := do
  try
    let (offsets, size) ← OneDimensionalComponentsCompaction.pack cs spacing fast
    return s!"{offsets.toList.map fun v => (fb v.x, fb v.y)} {fb size.x} {fb size.y}"
  catch e => return s!"error: {e}"

def packFastPath : Suite := suite "layered.components.packFastPath" do
  let mut same := 0
  let mut total := 0
  let mut ok := 0
  for seed in [1:151] do
    let cs := randomComponents (seed.toUInt64 * 2654435761) (seed % 2 + 2)
    let spacing := (seed % 4).toFloat * 5.0
    let a ← packOutcome cs spacing true
    let b ← packOutcome cs spacing false
    total := total + 1
    if !a.startsWith "error" then ok := ok + 1
    if a == b then same := same + 1 else IO.println s!"pack mismatch seed {seed}"
  checkEq "pack fast = reference" same total
  report "pack: most random inputs compact without exception" (ok * 4 >= total * 3) s!"{ok}/{total}"

def suites : Array Tests.Suite := #[edgeAwareSweepFast, packFastPath]

end Tests.Layered.CompactionFast
