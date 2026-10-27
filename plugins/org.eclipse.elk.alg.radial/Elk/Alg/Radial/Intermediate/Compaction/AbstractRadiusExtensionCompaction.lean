import Elk.Graph
/-!
# `org.eclipse.elk.alg.radial.intermediate.compaction.AbstractRadiusExtensionCompaction`

Port of `abstract_radius_extension_compaction.rs` (elk-rs): the base of the radial compactions
and of the overlap removal. The base class is a plain value (`compactionStep`, `spacing`);
the Lean subclasses hold it in their context.

Parity note: the Rust subclasses are created with `::default()`, a derived `Default` that sets
`compaction_step` to `0` (Java and `AbstractRadiusExtensionCompaction::new()` use `1`).
The compactions overwrite the step with `COMPACTION_STEP_SIZE` before use, the overlap removal
does not, so its layer expansion is a no-op (up to floating point rounding of `cx + 0 - half_w`).
`compactionStep` therefore defaults to `0` here.
-/
namespace Elk.Alg.Radial.Intermediate.Compaction

open Elk.Graph

/-- `AbstractRadiusExtensionCompaction`. -/
structure AbstractRadiusExtensionCompaction where
  /-- `compaction_step` (`i32`; `0` for `::default()`). -/
  compactionStep : Int := 0
  /-- `spacing`. -/
  spacing : Float := 0.0
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
    let halfW := n.width / 2.0
    let halfH := n.height / 2.0
    let xPos := n.x + halfW
    let yPos := n.y + halfH
    let dx := xPos - parentX
    let dy := yPos - parentY
    let length := Float.sqrt (dx * dx + dy * dy)
    let ux := dx * step / length
    let uy := dy * step / length
    if isContracting then
      ElkM.modifyNode node fun m => { m with x := xPos - ux - halfW, y := yPos - uy - halfH }
    else
      ElkM.modifyNode node fun m => { m with x := xPos + ux - halfW, y := yPos + uy - halfH }

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
    if x1 < x2 + w2 && x2 < x1 + w1 && y1 < y2 + h2 && y2 < y1 + h1 then return true
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
    let halfW := w.get! i / 2.0
    let halfH := h.get! i / 2.0
    let oldX := x.get! i
    let oldY := y.get! i
    let cx := oldX + halfW
    let cy := oldY + halfH
    let dx := cx - parentX
    let dy := cy - parentY
    let length := Float.sqrt (dx * dx + dy * dy)
    let ux := dx * step / length
    let uy := dy * step / length
    let newX := if isContracting then cx - ux - halfW else cx + ux - halfW
    let newY := if isContracting then cy - uy - halfH else cy + uy - halfH
    if newX.toBits != oldX.toBits || newY.toBits != oldY.toBits then changed := true
    x := x.set! i newX
    y := y.set! i newY
  return (x, y, changed)

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

/-- `overlap(node1, node2)` on the arena: whether the bounds (with spacing) intersect. -/
def overlapPure (self : AbstractRadiusExtensionCompaction) (g : ElkGraph) (node1 node2 : NodeId) : Bool :=
  let (x1, y1, width1, height1) := nodeBounds (g.node node1) self.spacing
  let (x2, y2, width2, height2) := nodeBounds (g.node node2) self.spacing
  let xOverlap := x1 < x2 + width2 && x2 < x1 + width1
  let yOverlap := y1 < y2 + height2 && y2 < y1 + height1
  xOverlap && yOverlap

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
    if x1 < x2 + w2 && x2 < x1 + w1 && y1 < y2 + h2 && y2 < y1 + h1 then overlapping := true
  return overlapping

end AbstractRadiusExtensionCompaction

end Elk.Alg.Radial.Intermediate.Compaction
