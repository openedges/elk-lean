import Elk.Graph.Properties
import Elk.Core.Util.Java
import Elk.Core.Math.ElkMath
import Elk.Core.Math.ElkRectangle
import Elk.Alg.Disco.Graph.Ids
import Elk.Alg.Disco.Graph.DCExtension
/-!
# `org.eclipse.elk.alg.disco.graph.DCElement`

A shape (polygon) of a connected component (elk-rs `graph/dc_element.rs`). Elements live in the
arena `DCGraph.elements`; `component` is the id of the owning `DCComponent` (Rust: `Weak`).

`getOffset()` (the offset of the owning component) needs the component arena and is
`DCGraph.elementOffset`. The `getCoords()` cache of Rust is the pure function `coords`.
-/
namespace Elk.Alg.Disco.Graph

open Elk.Graph Elk.Core.Math Elk.Core.Util

/-- `DCElement`. -/
structure DCElement where
  /-- The polygon `shape`. -/
  shape : KVectorChain
  /-- `getBounds()`: bounding box of the polygon. -/
  bounds : ElkRectangle
  /-- The owning component (set by `DCGraph.new`). -/
  component : Option DCComponentId := none
  /-- `getParentCoords()`. -/
  parentCoords : Option KVector := none
  /-- `getExtensions()`. -/
  extensions : Array DCExtension := #[]
  /-- `properties`. -/
  properties : PropertyMap := {}
  deriving Inhabited

namespace DCElement

/-- `new DCElement(polyPath)`: the bounds are the bounding box of the points (`f64::min/max`,
so an empty path yields `(inf, inf, -inf, -inf)` like Rust). -/
def new (polyPath : KVectorChain) : DCElement := Id.run do
  let mut minX := Float.posInf
  let mut minY := Float.posInf
  let mut maxX := Float.negInf
  let mut maxY := Float.negInf
  for v in polyPath do
    minX := fmin minX v.x
    minY := fmin minY v.y
    maxX := fmax maxX v.x
    maxY := fmax maxY v.y
  return { shape := polyPath, bounds := ElkRectangle.ofValues minX minY (maxX - minX) (maxY - minY) }

/-- `getCoords()`: the flattened `x, y` coordinates of the polygon. -/
def coords (e : DCElement) : Array Float :=
  e.shape.foldl (fun acc c => (acc.push c.x).push c.y) (Array.mkEmpty (e.shape.size * 2))

/-- `addExtension(extension)`. -/
def addExtension (e : DCElement) (ext : DCExtension) : DCElement :=
  { e with extensions := e.extensions.push ext }

/-- `intersects(rect)`: the polygon crosses the border of the rectangle or lies inside it
(`ElkMath.intersects(rect, shape) || ElkMath.contains(rect, shape)`). -/
def intersects (e : DCElement) (rect : ElkRectangle) : Bool :=
  ElkMath.intersectsRectPath rect e.shape || ElkMath.containsRectPath rect e.shape

end DCElement

end Elk.Alg.Disco.Graph
