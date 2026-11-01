import Elk.Alg.Layered.Components.Compaction.ComponentsCompactor
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.components.ModelOrderRowGraphPlacer`

Port of `combine_model_order_row` and `place_components_in_rows_model_order` of
`components/components_processor.rs` (elk-rs; Java `ModelOrderRowGraphPlacer`): places the
components in model order in rows; components connected to `WEST` (or following one connected
to `EAST`) start a new row, `NORTH` components are appended to the right of the broadest row and
`SOUTH` components push the start of the following rows to the right.
-/

namespace Elk.Alg.Layered.Components

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open LayeredM AbstractGraphPlacer Elk.Alg.Layered.Components.Compaction

namespace ModelOrderRowGraphPlacer

/-- Rust `place_components_in_rows_model_order(components, target, max_row_width,
component_spacing)`. -/
def placeComponentsInRowsModelOrder (components : Array LGraphId) (target : LGraphId)
    (maxRowWidth componentSpacing : Float) : LayeredM Unit := do
  let mut xpos := fl0p0
  let mut ypos := fl0p0
  let mut highestBox := fl0p0
  let mut broadestRow := componentSpacing
  let mut lastComponent : Option LGraphId := none
  let mut startXOfRow := fl0p0
  for component in components do
    let g ← getGraph component
    let sizeX := g.size.x
    let sizeY := g.size.y
    let extPorts := g.internal.extPortConnections
    let lastHasEast ← match lastComponent with
      | some last => pure ((← getGraph last).internal.extPortConnections.contains .east)
      | none => pure false
    if (xpos + sizeX > maxRowWidth && !extPorts.contains .north) || lastHasEast || extPorts.contains .west then
      xpos := startXOfRow
      ypos := ypos + (highestBox + componentSpacing)
      highestBox := fl0p0
    if extPorts.contains .north then
      xpos := broadestRow + componentSpacing
    offsetGraph component (xpos + g.offset.x) (ypos + g.offset.y)
    modifyGraph component fun x => { x with offset := ⟨fl0p0, fl0p0⟩ }
    broadestRow := fmax broadestRow (xpos + sizeX)
    if extPorts.contains .south then
      startXOfRow := fmax startXOfRow (xpos + sizeX + componentSpacing)
    highestBox := fmax highestBox sizeY
    xpos := xpos + (sizeX + componentSpacing)
    lastComponent := some component
  let finalSize : KVector := ⟨broadestRow, ypos + highestBox⟩
  modifyGraph target fun x => { x with size := finalSize }

/-- Rust `combine_model_order_row(components, target)` (Java `ModelOrderRowGraphPlacer.combine`). -/
def combine (components : Array LGraphId) (target : LGraphId) : LayeredM Unit := do
  clearLayerlessNodes target
  if let some first := components[0]? then
    copyProperties target first
  let tg ← getGraph target
  let aspectRatio := tg.props.getD LayeredOptions.ASPECT_RATIO LayeredOptions.ASPECT_RATIO_DEFAULT
  let componentSpacing := tg.props.getD LayeredOptions.SPACING_COMPONENT_COMPONENT fl20p0
  let mut maxRowWidth := fl0p0
  let mut totalArea := fl0p0
  for component in components do
    let size := (← getGraph component).size
    maxRowWidth := fmax maxRowWidth size.x
    totalArea := totalArea + size.x * size.y
  -- Java: Math.max(maxRowWidth, (float) Math.sqrt(totalArea) * aspectRatio)
  maxRowWidth := fmax maxRowWidth (Float.toF32 (Float.sqrt totalArea) * aspectRatio)
  placeComponentsInRowsModelOrder components target maxRowWidth componentSpacing
  maybeCompactComponents components target false
  for component in components do
    moveGraph target component fl0p0 fl0p0

end ModelOrderRowGraphPlacer

end Elk.Alg.Layered.Components
