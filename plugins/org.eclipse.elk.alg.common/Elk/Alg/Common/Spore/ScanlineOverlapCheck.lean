import Elk.Core.Util.Sort
import Elk.Alg.Common.Spore.IOverlapHandler
import Elk.Alg.Common.Utils.SVGImage
/-!
# `org.eclipse.elk.alg.common.spore.ScanlineOverlapCheck`

Finds all pairs of overlapping nodes with a vertical scanline and reports them
to an `IOverlapHandler` (`ScanlineOverlapCheck.java`, elk-rs `spore/scanline_overlap_check.rs`).

`Scanline.execute` (`Collections.sort` with the timestamp comparator, then one handler call per
timestamp) is inlined; both comparators use `Double.compare` (a total order, so any stable sort
agrees with TimSort). The active set (`intervals`) is Java's `TreeSet<Node>` with the comparator
`compareNodes`, kept as a sorted list of node indices: adding a node that compares equal to an
active one fails, and Java then throws `IllegalStateException: Invalid hitboxes for scanline overlap
calculation.` (elk-rs inserted it anyway). SVG debug output is not ported (TODO(debug)).
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

/-- `overlapsScanlineComparator`: by y (`Double.compare`); at equal y upper ends come before lower
ends. -/
def timestampCmp (nodes : Array Node) (p1 p2 : Timestamp) : Ordering :=
  let yOf (p : Timestamp) : Float :=
    match nodes[p.index]? with
    | some n => if p.low then n.rect.y else n.rect.y + n.rect.height
    | none => 0.0
  let c := Float.compareJava (yOf p1) (yOf p2)
  if c == .eq then
    if !p1.low && p2.low then .lt
    else if !p2.low && p1.low then .gt
    else c
  else c

/-- The comparator of `intervalsSortLeft`: `rect.x`, then `originalVertex.x`, then
`originalVertex.y` (`Double.compare`). -/
def compareNodes (n1 n2 : Node) : Ordering :=
  match Float.compareJava n1.rect.x n2.rect.x with
  | .eq =>
    match Float.compareJava n1.originalVertex.x n2.originalVertex.x with
    | .eq => Float.compareJava n1.originalVertex.y n2.originalVertex.y
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

/-- The message of the `IllegalStateException` when a node cannot be added to the active set. -/
def INVALID_HITBOXES : String :=
  "java.lang.IllegalStateException: Invalid hitboxes for scanline overlap calculation."

/-- `OverlapsScanlineHandler.insert`: adds `index` to the sorted active set (`none` if a node that
compares equal is active: `TreeSet.add` fails) and reports the overlapping active nodes, stopping
at the first non-overlapping node after an overlap was found. -/
private def insert (handler : IOverlapHandler σ) (nodes : Array Node) (intervals : Array Nat)
    (index : Nat) (state : σ) : Option (Array Nat × σ) := Id.run do
  let some node := nodes[index]? | return some (intervals, state)
  let cmp (other : Nat) : Ordering :=
    match nodes[other]? with
    | some o => compareNodes node o
    | none => .gt
  if intervals.any (cmp · == .eq) then return none
  let insertPos := (intervals.findIdx? (cmp · == .lt)).getD intervals.size
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
  return some (intervals, state)

/-- `sweep(nodes)`: reports every overlapping pair `(inserted node, active node)` to the
handler, threading the handler state from `init`; `.error` with Java's exception text if a node
cannot be added to the active set (`INVALID_HITBOXES`). -/
def sweep (s : ScanlineOverlapCheck σ) (nodes : Array Node) (init : σ) : Except String σ := Id.run do
  let mut points : Array Timestamp := #[]
  for idx in [0:nodes.size] do
    points := points.push { index := idx, low := true }
    points := points.push { index := idx, low := false }
  let mut intervals : Array Nat := #[]
  let mut state := init
  for point in stableSort points (timestampCmp nodes) do
    if point.low then
      let some (iv, st) := insert s.overlapHandler nodes intervals point.index state
        | return .error INVALID_HITBOXES
      intervals := iv
      state := st
    else
      -- `TreeSet.remove`: the active node comparing equal (the node itself, see `insert`)
      let node := nodes[point.index]?
      match intervals.findIdx? fun i => match node, nodes[i]? with
          | some n, some o => compareNodes n o == .eq
          | _, _ => i == point.index with
      | some pos => intervals := intervals.eraseIdxIfInBounds pos
      | none => pure ()
  return .ok state

end ScanlineOverlapCheck

end Elk.Alg.Common.Spore
