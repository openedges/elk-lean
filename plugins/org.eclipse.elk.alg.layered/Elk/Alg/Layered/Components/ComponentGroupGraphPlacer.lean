import Elk.Alg.Layered.Components.ComponentGroup
import Elk.Alg.Layered.Components.Compaction.ComponentsCompactor
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.components.ComponentGroupGraphPlacer`

Port of `combine_component_group`, `add_component_to_groups`, `place_component_group`,
`place_components_horizontally`, `place_components_vertically` and
`place_components_in_rows_group` of `components/components_processor.rs` (elk-rs; Java
`ComponentGroupGraphPlacer`): components with external port connections are collected into
`ComponentGroup`s (first group that accepts a component, else a new one); each group is laid
out sector by sector and the groups are placed diagonally one after the other.

`placeComponentGroup` takes the group's `getComponents(sides)` lookup as a function so that it
serves `ComponentGroup` and `ModelOrderComponentGroup` (Rust trait `ComponentGroupLike`).
-/

namespace Elk.Alg.Layered.Components

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open LayeredM AbstractGraphPlacer Elk.Alg.Layered.Components.Compaction PortSide

namespace ComponentGroupGraphPlacer

/-- Rust `place_components_horizontally(components, spacing)`: places the components next to
each other; returns the occupied size (spacing included where something was placed). -/
def placeComponentsHorizontally (components : Array LGraphId) (spacing : Float) : LayeredM KVector := do
  let mut size : KVector := ⟨fl0p0, fl0p0⟩
  for component in components do
    offsetGraph component size.x fl0p0
    let cs := (← getGraph component).size
    size := ⟨size.x + (cs.x + spacing), fmax size.y cs.y⟩
  if size.y > fl0p0 then size := { size with y := size.y + spacing }
  return size

/-- Rust `place_components_vertically(components, spacing)`: places the components below each
other. -/
def placeComponentsVertically (components : Array LGraphId) (spacing : Float) : LayeredM KVector := do
  let mut size : KVector := ⟨fl0p0, fl0p0⟩
  for component in components do
    offsetGraph component fl0p0 size.y
    let cs := (← getGraph component).size
    size := ⟨fmax size.x cs.x, size.y + (cs.y + spacing)⟩
  if size.x > fl0p0 then size := { size with x := size.x + spacing }
  return size

/-- Rust `place_components_in_rows_group(components, spacing)`: the row placement of the
unconnected (`c` sector) components, using the first component's `ASPECT_RATIO`. -/
def placeComponentsInRowsGroup (components : Array LGraphId) (spacing : Float) : LayeredM KVector := do
  let some first := components[0]? | return ⟨fl0p0, fl0p0⟩
  let mut maxRowWidth := fl0p0
  let mut totalArea := fl0p0
  for component in components do
    let size := (← getGraph component).size
    maxRowWidth := fmax maxRowWidth size.x
    totalArea := totalArea + size.x * size.y
  let aspectRatio := (← getGraph first).props.getD LayeredOptions.ASPECT_RATIO LayeredOptions.ASPECT_RATIO_DEFAULT
  -- Java: Math.max(maxRowWidth, (float) Math.sqrt(totalArea) * aspectRatio)
  maxRowWidth := fmax maxRowWidth (Float.toF32 (Float.sqrt totalArea) * aspectRatio)
  let mut xpos := fl0p0
  let mut ypos := fl0p0
  let mut highestBox := fl0p0
  let mut broadestRow := spacing
  for component in components do
    let size := (← getGraph component).size
    if xpos + size.x > maxRowWidth then
      xpos := fl0p0
      ypos := ypos + (highestBox + spacing)
      highestBox := fl0p0
    offsetGraph component xpos ypos
    broadestRow := fmax broadestRow (xpos + size.x)
    highestBox := fmax highestBox size.y
    xpos := xpos + (size.x + spacing)
  return ⟨broadestRow + spacing, ypos + highestBox + spacing⟩

/-- Rust `place_component_group(group, spacing)` (Java `placeComponentGroup`): places the
components of every sector and offsets the sectors; returns the group size. -/
def placeComponentGroup (componentsFor : EnumSet PortSide → Array LGraphId) (spacing : Float) :
    LayeredM KVector := do
  let sizeC ← placeComponentsInRowsGroup (componentsFor SIDES_NONE) spacing
  let sizeN ← placeComponentsHorizontally (componentsFor SIDES_NORTH) spacing
  let sizeS ← placeComponentsHorizontally (componentsFor SIDES_SOUTH) spacing
  let sizeW ← placeComponentsVertically (componentsFor SIDES_WEST) spacing
  let sizeE ← placeComponentsVertically (componentsFor SIDES_EAST) spacing
  let sizeNW ← placeComponentsHorizontally (componentsFor SIDES_NORTH_WEST) spacing
  let sizeNE ← placeComponentsHorizontally (componentsFor SIDES_NORTH_EAST) spacing
  let sizeSW ← placeComponentsHorizontally (componentsFor SIDES_SOUTH_WEST) spacing
  let sizeSE ← placeComponentsHorizontally (componentsFor SIDES_EAST_SOUTH) spacing
  let sizeWE ← placeComponentsVertically (componentsFor SIDES_EAST_WEST) spacing
  let sizeNS ← placeComponentsHorizontally (componentsFor SIDES_NORTH_SOUTH) spacing
  let sizeNWE ← placeComponentsHorizontally (componentsFor SIDES_NORTH_EAST_WEST) spacing
  let sizeSWE ← placeComponentsHorizontally (componentsFor SIDES_EAST_SOUTH_WEST) spacing
  let sizeWNS ← placeComponentsVertically (componentsFor SIDES_NORTH_SOUTH_WEST) spacing
  let sizeENS ← placeComponentsVertically (componentsFor SIDES_NORTH_EAST_SOUTH) spacing
  let sizeNESW ← placeComponentsHorizontally (componentsFor SIDES_NORTH_EAST_SOUTH_WEST) spacing
  let colLeftWidth := maxOf #[sizeNW.x, sizeW.x, sizeSW.x, sizeWNS.x]
  let colMidWidth := maxOf #[sizeN.x, sizeC.x, sizeS.x, sizeNESW.x]
  let colNsWidth := sizeNS.x
  let colRightWidth := maxOf #[sizeNE.x, sizeE.x, sizeSE.x, sizeENS.x]
  let rowTopHeight := maxOf #[sizeNW.y, sizeN.y, sizeNE.y, sizeNWE.y]
  let rowMidHeight := maxOf #[sizeW.y, sizeC.y, sizeE.y, sizeNESW.y]
  let rowWeHeight := sizeWE.y
  let rowBottomHeight := maxOf #[sizeSW.y, sizeS.y, sizeSE.y, sizeSWE.y]
  offsetGraphs (componentsFor SIDES_NONE) (colLeftWidth + colNsWidth) (rowTopHeight + rowWeHeight)
  offsetGraphs (componentsFor SIDES_NORTH_EAST_SOUTH_WEST) (colLeftWidth + colNsWidth) (rowTopHeight + rowWeHeight)
  offsetGraphs (componentsFor SIDES_NORTH) (colLeftWidth + colNsWidth) 0.0
  offsetGraphs (componentsFor SIDES_SOUTH) (colLeftWidth + colNsWidth) (rowTopHeight + rowWeHeight + rowMidHeight)
  offsetGraphs (componentsFor SIDES_WEST) 0.0 (rowTopHeight + rowWeHeight)
  offsetGraphs (componentsFor SIDES_EAST) (colLeftWidth + colNsWidth + colMidWidth) (rowTopHeight + rowWeHeight)
  offsetGraphs (componentsFor SIDES_NORTH_EAST) (colLeftWidth + colNsWidth + colMidWidth) 0.0
  offsetGraphs (componentsFor SIDES_SOUTH_WEST) 0.0 (rowTopHeight + rowWeHeight + rowMidHeight)
  offsetGraphs (componentsFor SIDES_EAST_SOUTH) (colLeftWidth + colNsWidth + colMidWidth)
    (rowTopHeight + rowWeHeight + rowMidHeight)
  offsetGraphs (componentsFor SIDES_EAST_WEST) 0.0 rowTopHeight
  offsetGraphs (componentsFor SIDES_EAST_SOUTH_WEST) 0.0 (rowTopHeight + rowWeHeight + rowMidHeight)
  offsetGraphs (componentsFor SIDES_NORTH_SOUTH) colLeftWidth 0.0
  offsetGraphs (componentsFor SIDES_NORTH_EAST_SOUTH) (colLeftWidth + colNsWidth + colMidWidth) 0.0
  return ⟨maxOf #[colLeftWidth + colMidWidth + colNsWidth + colRightWidth, sizeWE.x, sizeNWE.x, sizeSWE.x],
    maxOf #[rowTopHeight + rowMidHeight + rowWeHeight + rowBottomHeight, sizeNS.y, sizeWNS.y, sizeENS.y]⟩

/-- Rust `add_component_to_groups(groups, component)`: the first group accepting the component,
else a new group. -/
def addComponentToGroups (groups : Array ComponentGroup) (component : LGraphId) : LayeredM (Array ComponentGroup) := do
  for i in [0:groups.size] do
    let (added, group) ← groups[i]!.add component
    if added then return groups.set! i group
  return groups.push (← ComponentGroup.withComponent component)

/-- Rust `combine_component_group(components, target)` (Java
`ComponentGroupGraphPlacer.combine`). -/
def combine (components : Array LGraphId) (target : LGraphId) : LayeredM Unit := do
  clearLayerlessNodes target
  let some first := components[0]? | do
    modifyGraph target fun g => { g with size := ⟨fl0p0, fl0p0⟩ }
  copyProperties target first
  let mut groups : Array ComponentGroup := #[]
  for component in components do
    groups ← addComponentToGroups groups component
  let componentSpacing := (← getGraph first).props.getD LayeredOptions.SPACING_COMPONENT_COMPONENT fl20p0
  let mut offset : KVector := ⟨fl0p0, fl0p0⟩
  for group in groups do
    let groupSize ← placeComponentGroup group.componentsFor componentSpacing
    offsetGraphs group.components offset.x offset.y
    offset := ⟨offset.x + groupSize.x, offset.y + groupSize.y⟩
  let finalSize : KVector := ⟨offset.x - componentSpacing, offset.y - componentSpacing⟩
  modifyGraph target fun g => { g with size := finalSize }
  maybeCompactComponents components target true
  for group in groups do
    moveGraphs target group.components fl0p0 fl0p0

end ComponentGroupGraphPlacer

end Elk.Alg.Layered.Components
