import Elk.Core.Util.Sort
import Elk.Alg.Common.Spore.IOverlapHandler
import Elk.Alg.Common.Utils.SVGImage
/-!
# `org.eclipse.elk.alg.common.spore.ScanlineOverlapCheck`

Finds all pairs of overlapping nodes with a vertical scanline and reports them
to an `IOverlapHandler` (elk-rs `spore/scanline_overlap_check.rs`).

The Rust `Scanline::execute` (stable sort with the timestamp comparator, then
one handler call per timestamp) is inlined. The active set (`intervals`) is a
list of node indices kept sorted by `compareNodes` (insertion before the first
strictly greater element). SVG debug output is not ported (TODO(debug)).
-/
namespace Elk.Alg.Common.Spore

open Elk.Core.Util Elk.Core.Math Elk.Alg.Common.Utils

/-- `org.eclipse.elk.alg.common.spore.ScanlineOverlapCheck` (Rust
`ScanlineOverlapCheck<H>`). -/
structure ScanlineOverlapCheck (σ : Type) where
  /-- The handler receiving the overlapping pairs. -/
  overlapHandler : IOverlapHandler σ
  /-- Debug output (no-op, TODO(debug)). -/
  svg : SVGImage := {}

namespace ScanlineOverlapCheck

variable {σ : Type}

/-- `ScanlineOverlapCheck::new(handler, svg)`. -/
def new (overlapHandler : IOverlapHandler σ) (svg : SVGImage := {}) : ScanlineOverlapCheck σ :=
  { overlapHandler, svg := svg.addGroups #["n", "o", "e"] }

/-- Rust `Timestamp`: the lower (`low = true`, top border) or upper end of a node. -/
structure Timestamp where
  /-- Node index. -/
  index : Nat
  /-- `true` for the top border `rect.y`, `false` for `rect.y + rect.height`. -/
  low : Bool
  deriving Repr, Inhabited, BEq

/-- Rust `overlaps_scanline_comparator`: by y; at equal y upper ends come before lower ends. -/
def timestampCmp (nodes : Array Node) (p1 p2 : Timestamp) : Ordering :=
  let yOf (p : Timestamp) : Float :=
    match nodes[p.index]? with
    | some n => if p.low then n.rect.y else n.rect.y + n.rect.height
    | none => 0.0
  let c := Float.comparePartial (yOf p1) (yOf p2)
  if c == .eq then
    if !p1.low && p2.low then .lt
    else if !p2.low && p1.low then .gt
    else c
  else c

/-- Rust `compare_nodes`: `rect.x`, then `originalVertex.x`, then `originalVertex.y`
(`partial_cmp().unwrap_or(Equal)`). -/
def compareNodes (n1 n2 : Node) : Ordering :=
  match Float.comparePartial n1.rect.x n2.rect.x with
  | .eq =>
    match Float.comparePartial n1.originalVertex.x n2.originalVertex.x with
    | .eq => Float.comparePartial n1.originalVertex.y n2.originalVertex.y
    | o => o
  | o => o

/-- Rust `overlap(n1, n2)`: horizontal overlap (fuzzy, strict). The Rust pointer identity
test (`std::ptr::eq`) is an index comparison here. -/
def overlap (i1 : Nat) (n1 : Node) (i2 : Nat) (n2 : Node) : Bool :=
  if i1 == i2 then false
  else
    let f := InternalProperties.FUZZINESS
    InternalProperties.fuzzyCompare n1.rect.x (n2.rect.x + n2.rect.width) f < 0
      && InternalProperties.fuzzyCompare n2.rect.x (n1.rect.x + n1.rect.width) f < 0

/-- Rust `OverlapsScanlineHandler::insert`: inserts `index` into the sorted active list and
reports the overlapping active nodes, stopping at the first non-overlapping node after an
overlap was found. -/
private def insert (handler : IOverlapHandler σ) (nodes : Array Node) (intervals : Array Nat)
    (index : Nat) (state : σ) : Array Nat × σ := Id.run do
  let some node := nodes[index]? | return (intervals, state)
  let insertPos := (intervals.findIdx? fun other =>
      match nodes[other]? with
      | some o => compareNodes node o == .lt
      | none => false).getD intervals.size
  let intervals := intervals.insertIdxIfInBounds insertPos index
  let mut state := state
  let mut overlapsFound := false
  for otherIdx in intervals do
    let some other := nodes[otherIdx]? | continue
    if overlap index node otherIdx other then
      state := handler.handle node other state
      overlapsFound := true
    else if overlapsFound then
      break
  return (intervals, state)

/-- `sweep(nodes)`: reports every overlapping pair `(inserted node, active node)` to the
handler, threading the handler state from `init`. -/
def sweep (s : ScanlineOverlapCheck σ) (nodes : Array Node) (init : σ) : σ := Id.run do
  let mut points : Array Timestamp := #[]
  for idx in [0:nodes.size] do
    points := points.push { index := idx, low := true }
    points := points.push { index := idx, low := false }
  let mut intervals : Array Nat := #[]
  let mut state := init
  for point in stableSort points (timestampCmp nodes) do
    if point.low then
      let (iv, st) := insert s.overlapHandler nodes intervals point.index state
      intervals := iv
      state := st
    else
      match intervals.findIdx? (· == point.index) with
      | some pos => intervals := intervals.eraseIdxIfInBounds pos
      | none => pure ()
  return state

end ScanlineOverlapCheck

end Elk.Alg.Common.Spore
