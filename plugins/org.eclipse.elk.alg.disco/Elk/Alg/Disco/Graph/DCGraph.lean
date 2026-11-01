import Elk.Graph.Properties
import Elk.Graph.ArrayModify
import Elk.Alg.Disco.Graph.DCComponent
/-!
# `org.eclipse.elk.alg.disco.graph.DCGraph`

The graph that DisCo compacts: a set of connected components built from `DCElement`s (elk-rs
`graph/dc_graph.rs`). The graph is the arena of all elements and components; Rust's
`Arc<Mutex<DCComponent>>` and `Weak` back references are `DCComponentId`/`DCElementId`.

Accessors that Rust implements on the component or element but that need the other arena
(`getDimensionsOfBoundingRectangle`, `getMinCorner`, `DCElement.getOffset`, `DCPolyomino.getId`)
are functions of `DCGraph` taking the id.
-/
namespace Elk.Alg.Disco.Graph

open Elk.Graph Elk.Core.Math

/-- `DCGraph`. -/
structure DCGraph where
  /-- Copy of the layout options of the ElkGraph (`properties`). -/
  properties : PropertyMap := {}
  /-- All elements of all components. -/
  elements : Array DCElement := #[]
  /-- `getComponents()`: components in creation order. -/
  components : Array DCComponent := #[]
  /-- `getDimensions()`: the dimensions of the compacted graph. -/
  dimensions : KVector := {}
  /-- `getInset()`. -/
  inset : Float := 0
  deriving Inhabited

namespace DCGraph

/-- `new DCGraph(components, inset)`: `elements` is the arena the id lists refer to. Every
component receives its elements in list order (`add_element`) and every element learns its
component (`set_component`). -/
def new (elements : Array DCElement) (components : Array (Array DCElementId)) (inset : Float) :
    DCGraph := Id.run do
  let mut elems := elements
  let mut comps : Array DCComponent := Array.mkEmpty components.size
  for ids in components do
    let cid : DCComponentId := ⟨comps.size⟩
    let mut comp : DCComponent := {}
    for e in ids do
      elems := elems.modifyIn e.idx fun el => { el with component := some cid }
      comp := comp.addElement e
    comps := comps.push comp
  return { elements := elems, components := comps, inset }

/-- `copyProperties(other)`. -/
def copyProperties (g : DCGraph) (other : PropertyMap) : DCGraph :=
  { g with properties := g.properties.copyFrom other }

/-- `DCComponent.getDimensionsOfBoundingRectangle()`. -/
def componentDimensions (g : DCGraph) (c : DCComponentId) : KVector :=
  g.components[c.idx]!.dimensionsOfBoundingRectangle g.elements

/-- `DCComponent.getMinCorner()`. -/
def componentMinCorner (g : DCGraph) (c : DCComponentId) : KVector :=
  g.components[c.idx]!.minCorner g.elements

/-- `DCComponent.intersects(rect)`. -/
def componentIntersects (g : DCGraph) (c : DCComponentId) (rect : ElkRectangle) : Bool :=
  g.components[c.idx]!.intersects g.elements rect

/-- `DCComponent.getOffset()`. -/
def componentOffset (g : DCGraph) (c : DCComponentId) : KVector :=
  g.components[c.idx]!.offset

/-- `DCComponent.setOffset(offset)`. -/
def setComponentOffset (g : DCGraph) (c : DCComponentId) (offset : KVector) : DCGraph :=
  { g with components := g.components.modify c.idx (·.setOffset offset) }

/-- `DCComponent.getId()`. -/
def componentId (g : DCGraph) (c : DCComponentId) : Int :=
  g.components[c.idx]!.id

/-- `DCComponent.setId(id)`. -/
def setComponentId (g : DCGraph) (c : DCComponentId) (id : Int) : DCGraph :=
  { g with components := g.components.modify c.idx (·.setId id) }

/-- `DCElement.getOffset()`: the offset of the component that owns the element (Rust panics with
"DCElement without component" if there is none; the zero vector is returned then, which cannot
happen for elements created by `DCGraph.new`). -/
def elementOffset (g : DCGraph) (e : DCElementId) : KVector :=
  match g.elements[e.idx]!.component with
  | some c => g.componentOffset c
  | none => {}

end DCGraph

end Elk.Alg.Disco.Graph
