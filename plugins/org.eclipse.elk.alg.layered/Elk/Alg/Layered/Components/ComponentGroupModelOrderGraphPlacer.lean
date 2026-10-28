import Elk.Alg.Layered.Components.ModelOrderComponentGroup
import Elk.Alg.Layered.Components.ComponentGroupGraphPlacer
/-!
# `org.eclipse.elk.alg.layered.components.ComponentGroupModelOrderGraphPlacer`

Port of `combine_component_group_model_order` and `add_component_to_model_order_groups` of
`components/components_processor.rs` (elk-rs; Java `ComponentGroupModelOrderGraphPlacer`):
like `ComponentGroupGraphPlacer` but with `ModelOrderComponentGroup`s (a component only joins
the **last** group) and the groups are placed in rows along the layout direction, keeping the
space blocked by components with southern (horizontal layouts) / eastern (vertical layouts)
connections.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl20p0 : Float := 20.0

namespace Elk.Alg.Layered.Components

open Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open LayeredM AbstractGraphPlacer Elk.Alg.Layered.Components.Compaction ComponentGroupGraphPlacer

namespace ComponentGroupModelOrderGraphPlacer

/-- Rust `add_component_to_model_order_groups(groups, component)`: only the last group is
tried. -/
def addComponentToModelOrderGroups (groups : Array ModelOrderComponentGroup) (component : LGraphId) :
    LayeredM (Array ModelOrderComponentGroup) := do
  if let some last := groups.back? then
    let (added, group) ← last.add component
    if added then return groups.set! (groups.size - 1) group
  return groups.push (← ModelOrderComponentGroup.withComponent component)

/-- Rust `combine_component_group_model_order(components, target)` (Java
`ComponentGroupModelOrderGraphPlacer.combine`). -/
def combine (components : Array LGraphId) (target : LGraphId) : LayeredM Unit := do
  clearLayerlessNodes target
  let some first := components[0]? | do
    modifyGraph target fun g => { g with size := ⟨fl0p0, fl0p0⟩ }
  copyProperties target first
  let mut groups : Array ModelOrderComponentGroup := #[]
  for component in components do
    groups ← addComponentToModelOrderGroups groups component
  let componentSpacing := (← getGraph first).props.getD LayeredOptions.SPACING_COMPONENT_COMPONENT fl20p0
  let direction := (← getGraph target).props.getD CoreOptions.DIRECTION Direction.right
  let mut spaceBlockedBySouthEdges : KVector := ⟨fl0p0, fl0p0⟩
  let mut spaceBlockedByComponents : KVector := ⟨fl0p0, fl0p0⟩
  let mut offset : KVector := ⟨fl0p0, fl0p0⟩
  let mut maxSize : KVector := ⟨fl0p0, fl0p0⟩
  for group in groups do
    let sides := group.portSides
    if direction.isHorizontal then
      offset := { offset with x := spaceBlockedBySouthEdges.x }
      if sides.any (·.contains .north) then
        offset := { offset with x := spaceBlockedByComponents.x }
    else if direction.isVertical then
      offset := { offset with y := spaceBlockedBySouthEdges.y }
      if sides.any (·.contains .west) then
        offset := { offset with y := spaceBlockedByComponents.y }
    let groupSize ← placeComponentGroup group.componentsFor componentSpacing
    offsetGraphs group.components offset.x offset.y
    if direction.isHorizontal then
      spaceBlockedByComponents := { spaceBlockedByComponents with x := offset.x + groupSize.x }
      maxSize := { maxSize with x := fmax maxSize.x spaceBlockedByComponents.x }
      if sides.any (·.contains .south) then
        spaceBlockedBySouthEdges := { spaceBlockedBySouthEdges with x := offset.x + groupSize.x }
      spaceBlockedByComponents := { spaceBlockedByComponents with y := offset.y + groupSize.y }
      offset := { offset with y := spaceBlockedByComponents.y }
      maxSize := { maxSize with y := fmax maxSize.y offset.y }
    else if direction.isVertical then
      spaceBlockedByComponents := { spaceBlockedByComponents with y := offset.y + groupSize.y }
      maxSize := { maxSize with y := fmax maxSize.y spaceBlockedByComponents.y }
      if sides.any (·.contains .east) then
        spaceBlockedBySouthEdges := { spaceBlockedBySouthEdges with y := offset.y + groupSize.y }
      spaceBlockedByComponents := { spaceBlockedByComponents with x := offset.x + groupSize.x }
      offset := { offset with x := spaceBlockedByComponents.x }
      maxSize := { maxSize with x := fmax maxSize.x offset.x }
  let finalSize : KVector := ⟨maxSize.x - componentSpacing, maxSize.y - componentSpacing⟩
  modifyGraph target fun g => { g with size := finalSize }
  maybeCompactComponents components target true
  for group in groups do
    moveGraphs target group.components fl0p0 fl0p0

end ComponentGroupModelOrderGraphPlacer

end Elk.Alg.Layered.Components
