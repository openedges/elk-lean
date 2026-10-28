import Elk.Graph
/-!
# `org.eclipse.elk.alg.radial.intermediate.compaction.AbstractRadiusExtensionCompaction`

Port of `abstract_radius_extension_compaction.rs` (elk-rs): the base of the radial compactions
and of the overlap removal. The base class is a plain value (`compactionStep`, `spacing`);
the Lean subclasses hold it in their context.

Java semantics (agent OPT; elk-rs differs in all three points, which elk-lean followed before):
* `compactionStep` is the Java field initialiser `1`. The compactions overwrite it with
  `COMPACTION_STEP_SIZE`, the overlap removal does not, so it expands layers by 1 per pass (the Rust
  subclasses are created with a derived `Default`, step `0`, which makes the overlap removal a no-op).
* `contractLayer` scales the edge vector by `x *= compactionStep / length` (the quotient first;
  Rust computes `dx * step / length`).
* `overlap` is Java's four corner cases with strict inequalities on both sides, so two bounds with
  the same left (or top) coordinate never overlap (Rust tests interval intersection).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Radial.Intermediate.Compaction

open Elk.Graph

/-- `AbstractRadiusExtensionCompaction`. -/
structure AbstractRadiusExtensionCompaction where
  /-- `compactionStep` (Java field initialiser `1`). -/
  compactionStep : Int := 1
  /-- `spacing`. -/
  spacing : Float := fl0p0
  deriving Inhabited

namespace AbstractRadiusExtensionCompaction

/-- `node_center(node)`. -/
def nodeCenter (node : NodeId) : ElkM (Float × Float) := do
  let n ← ElkM.getNode node
  return (n.x + n.width / 2.0, n.y + n.height / 2.0)

/-- `node_bounds(node, spacing)`: the bounds enlarged by half the spacing on every side. -/
def nodeBounds (n : ElkNode) (spacing : Float) : Float × Float × Float × Float :=
  (n.x - spacing / 2.0, n.y - spacing / 2.0, n.width + spacing, n.height + spacing)

/-- `contract_layer(root, layer_nodes, is_contracting)`: moves every node of the layer along the
line from the root center by `compaction_step` (towards the root when contracting). -/
def contractLayer (self : AbstractRadiusExtensionCompaction) (root : NodeId) (layerNodes : Array NodeId)
    (isContracting : Bool) : ElkM Unit := do
  let (parentX, parentY) ← nodeCenter root
  let step := Float.ofInt self.compactionStep
  for node in layerNodes do
    let n ← ElkM.getNode node
    let halfW := n.width / fl2p0
    let halfH := n.height / fl2p0
    let xPos := n.x + halfW
    let yPos := n.y + halfH
    let dx := xPos - parentX
    let dy := yPos - parentY
    let length := Float.sqrt (dx * dx + dy * dy)
    -- Java `x *= compactionStep / length`
    let f := step / length
    let ux := dx * f
    let uy := dy * f
    if isContracting then
      ElkM.modifyNode node fun m => { m with x := xPos - ux - halfW, y := yPos - uy - halfH }
    else
      ElkM.modifyNode node fun m => { m with x := xPos + ux - halfW, y := yPos + uy - halfH }

/-- Java `overlap(node1, node2)` on the bounds enlarged by the spacing (`x1, y1, width1, height1` and
`x2, ..`): the four corner cases "left upper / right lower / left lower / right upper corner
overlap", each with strict inequalities, so equal left or equal top coordinates never overlap. -/
@[inline] def overlapBounds (x1 y1 width1 height1 x2 y2 width2 height2 : Float) : Bool :=
  if (x1 < x2 + width2 && x2 < x1) && (y1 < y2 + height2 && y2 < y1) then true
  else if (x2 < x1 + width1 && x1 < x2) && (y2 < y1 + height1 && y1 < y2) then true
  else if (x1 < x2 + width2 && x2 < x1) && (y1 < y2 && y2 < y1 + height1) then true
  else if (x2 < x1 + width1 && x1 < x2) && (y1 < y2 + height2 && y2 < y1) then true
  else false

/-- `overlap_layer_soa(x, y, w, h, spacing)`: whether two cyclically neighbouring nodes overlap.
The coordinate arrays are unboxed `FloatArray`s (the Rust `&[f64]` slices). -/
def overlapLayerSoa (x y w h : FloatArray) (spacing : Float) : Bool := Id.run do
  let n := x.size
  if n < 2 then return false
  let halfS := spacing / 2.0
  for i in [0:n] do
    let j := if i < n - 1 then i + 1 else 0
    let x1 := x.get! i - halfS
    let y1 := y.get! i - halfS
    let w1 := w.get! i + spacing
    let h1 := h.get! i + spacing
    let x2 := x.get! j - halfS
    let y2 := y.get! j - halfS
    let w2 := w.get! j + spacing
    let h2 := h.get! j + spacing
    if overlapBounds x1 y1 w1 h1 x2 y2 w2 h2 then return true
  return false

/-- `contract_layer_soa(parent_x, parent_y, x, y, w, h, step, is_contracting)`: returns the new
`x` and `y` arrays and whether any coordinate changed (bitwise; `NaN` results compare equal
to themselves). The Rust function updates the slices in place. -/
def contractLayerSoa (parentX parentY : Float) (x y w h : FloatArray) (step : Float)
    (isContracting : Bool) : FloatArray × FloatArray × Bool := Id.run do
  let mut x := x
  let mut y := y
  let mut changed := false
  for i in [0:x.size] do
    let halfW := w.get! i / fl2p0
    let halfH := h.get! i / fl2p0
    let oldX := x.get! i
    let oldY := y.get! i
    let cx := oldX + halfW
    let cy := oldY + halfH
    let dx := cx - parentX
    let dy := cy - parentY
    let length := Float.sqrt (dx * dx + dy * dy)
    -- Java `x *= compactionStep / length`
    let f := step / length
    let ux := dx * f
    let uy := dy * f
    let newX := if isContracting then cx - ux - halfW else cx + ux - halfW
    let newY := if isContracting then cy - uy - halfH else cy + uy - halfH
    if newX.toBits != oldX.toBits || newY.toBits != oldY.toBits then changed := true
    x := x.set! i newX
    y := y.set! i newY
  return (x, y, changed)

/-! ### The unboxed layer loop of the overlap removal

`RadiusExtensionOverlapRemoval` repeats "is any neighbour pair overlapping? then expand the layer by
one step" until no pair overlaps — one pass per pixel of radius extension (Java's step 1), so a
layer of a few hundred nodes takes thousands of passes. The functions below compute exactly the
values of `overlapLayerSoa`/`contractLayerSoa` (same float operations in the same order) with
`USize` loops on unboxed `Float`s and in-place arrays (PLAN 7.1 items 3, 15):

* the per-node constants of the two functions (`width / 2`, `height / 2`, `width + spacing`,
  `height + spacing`) are computed once per layer instead of once per pass;
* the overlap test is a disjunction over the pairs without side effects, so it may scan the pairs
  in any order: the scan starts at the pair that overlapped in the previous pass (which usually
  still does) and stops at the first overlap, instead of scanning from pair 0;
* the bitwise "changed" test compares floats and only reads the bit patterns for `±0` and `NaN`. -/

/-- `a[i]` with a `USize` index (`0.0` out of bounds, like `FloatArray.get!`). -/
@[inline] private def fget (a : FloatArray) (i : USize) : Float :=
  if h : i < a.usize then
    have h1 : i.toNat < a.usize.toNat := (USize.lt_iff_toNat_lt).mp h
    have h2 : a.usize.toNat ≤ a.size := by
      simp only [FloatArray.usize, Nat.toUSize]
      exact Nat.mod_le _ _
    a.uget i (by omega)
  else fl0p0

/-- `a.set! i v` with a `USize` index (unchanged out of bounds). -/
@[inline] private def fset (a : FloatArray) (i : USize) (v : Float) : FloatArray :=
  if h : i < a.usize then
    have h1 : i.toNat < a.usize.toNat := (USize.lt_iff_toNat_lt).mp h
    have h2 : a.usize.toNat ≤ a.size := by
      simp only [FloatArray.usize, Nat.toUSize]
      exact Nat.mod_le _ _
    a.uset i v (by omega)
  else a

/-- `a.toBits == b.toBits` without reading the bit patterns unless `a == b == ±0` or both are
`NaN` (equal non-zero floats have equal bits, unequal non-`NaN` floats different ones). -/
@[inline] def sameBits (a b : Float) : Bool :=
  if a == b then a != fl0p0 || a.toBits == b.toBits
  else a != a && b != b && a.toBits == b.toBits

/-- The layer of the overlap removal loop: top-left corners `x`/`y`; `hw`/`hh` = `width / 2`,
`height / 2` (as `contractLayerSoa`); `bw`/`bh` = `width + spacing`, `height + spacing` (as
`overlapLayerSoa`); `halfS = spacing / 2`. -/
structure LayerSoa where
  x : FloatArray
  y : FloatArray
  hw : FloatArray
  hh : FloatArray
  bw : FloatArray
  bh : FloatArray
  halfS : Float

/-- The layer of the nodes with top-left corners `x`/`y` and sizes `w`/`h`. -/
def LayerSoa.mk' (x y w h : FloatArray) (spacing : Float) : LayerSoa :=
  { x, y
    hw := ⟨w.data.map (· / fl2p0)⟩, hh := ⟨h.data.map (· / fl2p0)⟩
    bw := ⟨w.data.map (· + spacing)⟩, bh := ⟨h.data.map (· + spacing)⟩
    halfS := spacing / 2.0 }

/-- `overlapBounds` regrouped: with `a = x1 < x2 + width2 ∧ x2 < x1`, `b = x2 < x1 + width1 ∧
x1 < x2`, `c = y1 < y2 + height2 ∧ y2 < y1` and `d = y2 < y1 + height1 ∧ y1 < y2` the four corner
cases are `a ∧ c`, `b ∧ d`, `a ∧ d` (the third case lists `d`'s comparisons in the other order) and
`b ∧ c`, so the test is `(a ∨ b) ∧ (c ∨ d)`. Every operand is a side-effect-free comparison, so the
grouping gives the same result for all inputs (`NaN` included); the four-case form makes the
compiler share sub-conditions through closures. -/
@[inline] def overlapBoundsGrouped (x1 y1 width1 height1 x2 y2 width2 height2 : Float) : Bool :=
  let a := x1 < x2 + width2 && x2 < x1
  let b := x2 < x1 + width1 && x1 < x2
  let c := y1 < y2 + height2 && y2 < y1
  let d := y2 < y1 + height1 && y1 < y2
  (a || b) && (c || d)

/-- The pair test of `overlapLayerSoa` for the neighbours `i` and `j`. -/
@[inline] private def pairOverlaps (l : LayerSoa) (i j : USize) : Bool :=
  let halfS := l.halfS
  overlapBoundsGrouped (fget l.x i - halfS) (fget l.y i - halfS) (fget l.bw i) (fget l.bh i)
    (fget l.x j - halfS) (fget l.y j - halfS) (fget l.bw j) (fget l.bh j)

/-- The first overlapping neighbour pair `(i, i + 1)` (`(n - 1, 0)` for the last node) with
`i` in `from ..< to`, or `n`. -/
private partial def scanPairs (l : LayerSoa) (n i to : USize) : USize :=
  if i >= to then n
  else if pairOverlaps l i (if i + 1 < n then i + 1 else 0) then i
  else scanPairs l n (i + 1) to

/-- `overlapLayerSoa` of the layer (`n` nodes) as the index of an overlapping neighbour pair, `n`
when none overlaps: the pairs `start ..< n`, then `0 ..< start`. -/
def overlapPairFrom (l : LayerSoa) (n start : USize) : USize :=
  if n < 2 then n
  else
    let i := scanPairs l n start n
    if i < n then i else scanPairs l n 0 start

/-- One `contractLayerSoa` pass on the layer in place (`isContracting = false`, `n` nodes):
`(cx + ux) - width / 2` with `ux = dx * (step / length)`; returns whether some coordinate changed
bitwise (`changed` = accumulated so far). -/
private partial def expandPass (px py step : Float) (hw hh : FloatArray) (n : USize) (x y : FloatArray)
    (i : USize) (changed : Bool) : FloatArray × FloatArray × Bool :=
  if i >= n then (x, y, changed)
  else
    let halfW := fget hw i
    let halfH := fget hh i
    let oldX := fget x i
    let oldY := fget y i
    let cx := oldX + halfW
    let cy := oldY + halfH
    let dx := cx - px
    let dy := cy - py
    let length := Float.sqrt (dx * dx + dy * dy)
    let f := step / length
    let ux := dx * f
    let uy := dy * f
    let newX := cx + ux - halfW
    let newY := cy + uy - halfH
    let changed := changed || !sameBits newX oldX || !sameBits newY oldY
    expandPass px py step hw hh n (fset x i newX) (fset y i newY) (i + 1) changed

/-- The overlap removal loop of a layer, `while overlapLayerSoa: contractLayerSoa(…, step, false)`
with the Lean guards of `RadiusExtensionOverlapRemoval.extend`: no pass once `iterations` reaches
`maxIterations`, stop after a pass that changes no coordinate. `hint` is the pair that overlapped
in the previous pass. Returns the final corners. -/
partial def expandLoop (px py step : Float) (maxIterations : Nat) (l : LayerSoa) (n : USize)
    (iterations : Nat) (hint : USize) : FloatArray × FloatArray :=
  let i := overlapPairFrom l n hint
  if i >= n || iterations >= maxIterations then (l.x, l.y)
  else
    let ⟨x, y, hw, hh, bw, bh, halfS⟩ := l
    let (x, y, changed) := expandPass px py step hw hh n x y 0 false
    let l : LayerSoa := ⟨x, y, hw, hh, bw, bh, halfS⟩
    if !changed then (l.x, l.y) else expandLoop px py step maxIterations l n (iterations + 1) i

/-- `move_node_with_center(root_cx, root_cy, node, distance)`. -/
def moveNodeWithCenter (_self : AbstractRadiusExtensionCompaction) (rootCx rootCy : Float) (node : NodeId)
    (distance : Float) : ElkM Unit := do
  let (nodeX, nodeY) ← nodeCenter node
  let dx := nodeX - rootCx
  let dy := nodeY - rootCy
  let length := Float.sqrt (dx * dx + dy * dy)
  let ux := dx / length
  let uy := dy / length
  ElkM.modifyNode node fun n => { n with x := n.x + ux * distance, y := n.y + uy * distance }

/-- `move_node(root, node, distance)`. -/
def moveNode (_self : AbstractRadiusExtensionCompaction) (root node : NodeId) (distance : Float) :
    ElkM Unit := do
  let (rootX, rootY) ← nodeCenter root
  let (nodeX, nodeY) ← nodeCenter node
  let differenceX := nodeX - rootX
  let differenceY := nodeY - rootY
  let length := Float.sqrt (differenceX * differenceX + differenceY * differenceY)
  let unitX := differenceX / length
  let unitY := differenceY / length
  ElkM.modifyNode node fun n => { n with x := n.x + unitX * distance, y := n.y + unitY * distance }

/-- `overlap(node1, node2)` on the arena (Java corner cases, `overlapBounds`). -/
def overlapPure (self : AbstractRadiusExtensionCompaction) (g : ElkGraph) (node1 node2 : NodeId) : Bool :=
  let (x1, y1, width1, height1) := nodeBounds (g.node node1) self.spacing
  let (x2, y2, width2, height2) := nodeBounds (g.node node2) self.spacing
  overlapBounds x1 y1 width1 height1 x2 y2 width2 height2

/-- `overlap(node1, node2)`. -/
def overlap (self : AbstractRadiusExtensionCompaction) (node1 node2 : NodeId) : ElkM Bool :=
  ElkM.withGraph fun g => self.overlapPure g node1 node2

/-- `overlap_layer(nodes)`: whether two cyclically neighbouring nodes overlap. -/
def overlapLayer (self : AbstractRadiusExtensionCompaction) (nodes : Array NodeId) : ElkM Bool := do
  if nodes.size < 2 then return false
  let g ← get
  let bounds := nodes.map fun n => nodeBounds (g.node n) self.spacing
  let mut overlapping := false
  for i in [0:bounds.size] do
    let j := if i < bounds.size - 1 then i + 1 else 0
    let (x1, y1, w1, h1) := bounds[i]!
    let (x2, y2, w2, h2) := bounds[j]!
    if overlapBounds x1 y1 w1 h1 x2 y2 w2 h2 then overlapping := true
  return overlapping

end AbstractRadiusExtensionCompaction

end Elk.Alg.Radial.Intermediate.Compaction
