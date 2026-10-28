import Elk.Alg.Layered.Components.Compaction.ComponentsCompactor
/-!
# `org.eclipse.elk.alg.layered.components.SimpleRowGraphPlacer`

Port of `combine_simple_row`, `sort_components_by_priority`, `component_priority_and_area` and
`place_components_in_rows` of `components/components_processor.rs` (elk-rs; Java
`SimpleRowGraphPlacer`): places the components (without external ports) in rows, ordered by
priority (or by model order), breaking rows at
`max(widest component, sqrt(total area) * aspect ratio)`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p6 : Float := 1.6
private def fl20p0 : Float := 20.0

namespace Elk.Alg.Layered.Components

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open LayeredM AbstractGraphPlacer Elk.Alg.Layered.Components.Compaction

namespace SimpleRowGraphPlacer

/-- Rust `component_priority_and_area(graph)`: the sum of the nodes' `PRIORITY` values (nodes
without one are skipped) and the area of the graph. -/
def componentPriorityAndArea (graph : LGraphId) : LayeredM (Int × Float) := do
  let mut priority : Int := 0
  for n in ← collectComponentNodes graph do
    if let some p := (← getNode n).props.get CoreOptions.PRIORITY then
      priority := priority + p
  let size := (← getGraph graph).size
  return (priority, size.x * size.y)

/-- Rust `sort_components_by_priority(components, target)`: with model order components by
ascending minimal model order, otherwise by descending priority, then ascending area (NaN
equal), then input index. -/
def sortComponentsByPriority (components : Array LGraphId) (target : LGraphId) : LayeredM (Array LGraphId) := do
  let considerModelOrder := (← getGraph target).props.getD LayeredOptions.CONSIDER_MODEL_ORDER_COMPONENTS
    ComponentOrderingStrategy.none
  if considerModelOrder != .none then
    let mut keyed : Array (Nat × Int × LGraphId) := #[]
    for i in [0:components.size] do
      let c := components[i]!
      keyed := keyed.push (i, ← LGraphUtil.getMinimalModelOrder c, c)
    let sorted := stableSort keyed fun (li, lo, _) (ri, ro, _) =>
      match compare lo ro with
      | .eq => compare li ri
      | o => o
    return sorted.map (·.2.2)
  let mut keyed : Array (Nat × Int × Float × LGraphId) := #[]
  for i in [0:components.size] do
    let c := components[i]!
    let (priority, area) ← componentPriorityAndArea c
    keyed := keyed.push (i, priority, area, c)
  let sorted := stableSort keyed fun (li, lp, la, _) (ri, rp, ra, _) =>
    match compare rp lp with
    | .eq =>
      match Float.comparePartial la ra with
      | .eq => compare li ri
      | o => o
    | o => o
  return sorted.map (·.2.2.2)

/-- Rust `place_components_in_rows(components, target, max_row_width, component_spacing)`:
offsets every component (plus its own offset, which is reset) and sets the target size. -/
def placeComponentsInRows (components : Array LGraphId) (target : LGraphId) (maxRowWidth componentSpacing : Float) :
    LayeredM Unit := do
  let mut xpos := fl0p0
  let mut ypos := fl0p0
  let mut highestBox := fl0p0
  let mut broadestRow := componentSpacing
  for component in components do
    let g ← getGraph component
    let sizeX := g.size.x
    let sizeY := g.size.y
    if xpos + sizeX > maxRowWidth then
      xpos := fl0p0
      ypos := ypos + (highestBox + componentSpacing)
      highestBox := fl0p0
    offsetGraph component (xpos + g.offset.x) (ypos + g.offset.y)
    modifyGraph component fun x => { x with offset := ⟨fl0p0, fl0p0⟩ }
    broadestRow := fmax broadestRow (xpos + sizeX)
    highestBox := fmax highestBox sizeY
    xpos := xpos + (sizeX + componentSpacing)
  let finalSize : KVector := ⟨broadestRow, ypos + highestBox⟩
  modifyGraph target fun x => { x with size := finalSize }

/-- Rust `combine_simple_row(components, target)` (Java `SimpleRowGraphPlacer.combine`). -/
def combine (components : Array LGraphId) (target : LGraphId) : LayeredM Unit := do
  -- Java parity: single-component optimization
  if components.size == 1 then
    let source := components[0]!
    if source == target then return
    adoptSingleComponent target source
    return
  let ordered ← sortComponentsByPriority components target
  clearLayerlessNodes target
  if let some first := ordered[0]? then
    copyProperties target first
  let tg ← getGraph target
  let aspectRatio := tg.props.getD LayeredOptions.ASPECT_RATIO fl1p6
  let componentSpacing := tg.props.getD LayeredOptions.SPACING_COMPONENT_COMPONENT fl20p0
  let mut maxRowWidth := fl0p0
  let mut totalArea := fl0p0
  for component in ordered do
    let size := (← getGraph component).size
    maxRowWidth := fmax maxRowWidth size.x
    totalArea := totalArea + size.x * size.y
  -- Java: Math.max(maxRowWidth, (float) Math.sqrt(totalArea) * aspectRatio)
  maxRowWidth := fmax maxRowWidth (Float.toF32 (Float.sqrt totalArea) * aspectRatio)
  placeComponentsInRows ordered target maxRowWidth componentSpacing
  maybeCompactComponents ordered target false
  for component in ordered do
    moveGraph target component fl0p0 fl0p0

end SimpleRowGraphPlacer

end Elk.Alg.Layered.Components
