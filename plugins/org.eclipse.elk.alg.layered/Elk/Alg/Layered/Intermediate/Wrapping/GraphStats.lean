import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Core.Util.Java
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping.GraphStats`

Port of the `GraphStats` struct of elk-rs `intermediate/single_edge_graph_wrapper.rs`. Java
computes the widths, heights and allowed cuts lazily; elk-rs (and this port) computes everything
eagerly in the constructor, before any processor modifies the graph, which yields the same values.
The Java `getApproximate*` methods were not ported by elk-rs and are omitted.

Option reads: the stored value, else the property default; `ASPECT_RATIO` falls back to Java's
`LayeredOptions.ASPECT_RATIO` default `1.6f` (`ASPECT_RATIO_DEFAULT`; elk-rs used `1.0`). The widths
and heights use Java's addition order and `Math.max` (agent COV).
-/

namespace Elk.Alg.Layered.Intermediate.Wrapping

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

/-- `GraphStats`: statistics about a layered graph used by the cut index calculators. -/
structure GraphStats where
  /-- `dar`: the desired aspect ratio, adjusted to the layout direction. -/
  dar : Float
  /-- `longestPath`: the number of layers. -/
  longestPath : Nat
  /-- `getMaxWidth()`. -/
  maxWidth : Float
  /-- `getMaxHeight()`. -/
  maxHeight : Float
  /-- `getSumWidth()`. -/
  sumWidth : Float
  /-- `getWidths()`: per layer the widest node (plus margins and layer spacing). -/
  widths : Array Float
  /-- `getHeights()`: per layer the summed node heights (plus margins and in-layer spacing). -/
  heights : Array Float
  /-- `getCutsAllowed()`: whether a cut *before* layer `i` is allowed. -/
  cutsAllowed : Array Bool
  deriving Inhabited, Repr

namespace GraphStats

/-- `determineLayerWidth(layer)`: the maximum (`Math.max`) of `size.x + margin.right + margin.left +
spacing` (Java's addition order; elk-rs added `left` first) over the layer's nodes, `0` if empty. -/
def determineLayerWidth (layer : LayerId) (spacing : Float) : LayeredM Float := do
  let mut maxWidth : Float := 0.0
  for node in (← getLayer layer).nodes do
    let nd ← getNode node
    let nodeWidth := nd.size.x + nd.margin.right + nd.margin.left + spacing
    maxWidth := javaMax maxWidth nodeWidth
  return maxWidth

/-- `determineLayerHeight(layer)`: the sum of `size.y + margin.bottom + margin.top +
inLayerSpacing` over the layer's nodes, plus for every incoming edge from a `NORTH_SOUTH_PORT`
dummy the height (with margins) of that dummy's `ORIGIN` node. -/
def determineLayerHeight (layer : LayerId) (inLayerSpacing : Float) : LayeredM Float := do
  let mut layerHeight : Float := 0.0
  for node in (← getLayer layer).nodes do
    let incomingEdges ← withArena (·.nodeIncomingEdges node)
    let nd ← getNode node
    layerHeight := layerHeight + (nd.size.y + nd.margin.bottom + nd.margin.top + inLayerSpacing)
    for incomingEdge in incomingEdges do
      let some sourcePort := (← getEdge incomingEdge).source | continue
      let some sourceNode := (← getPort sourcePort).owner | continue
      let src ← getNode sourceNode
      if src.type != .northSouthPort then continue
      if let some (.lNode originNode) := src.internal.origin then
        let origin ← getNode originNode
        layerHeight := layerHeight + (origin.size.y + origin.margin.bottom + origin.margin.top)
  return layerHeight

/-- `isCutAllowed(layer)`: a cut before the layer is allowed if all its incoming edges connect
the same pair of nodes. -/
def isCutAllowedLayer (layer : LayerId) : LayeredM Bool := do
  let mut targetNode : Option LNodeId := none
  let mut sourceNode : Option LNodeId := none
  for target in (← getLayer layer).nodes do
    for edge in (← withArena (·.nodeIncomingEdges target)) do
      match targetNode with
      | some existing => if existing != target then return false
      | none => targetNode := some target
      let some sp := (← getEdge edge).source | continue
      let some source := (← getPort sp).owner | continue
      match sourceNode with
      | some existing => if existing != source then return false
      | none => sourceNode := some source
  return true

/-- `initCutAllowed()`: with `WRAPPING_VALIDIFY_FORBIDDEN_INDICES` set every entry stays `false`
(Java/Rust only ever write `false`); otherwise entry `i ≥ 1` is `isCutAllowed(layers[i])`. -/
def initCutAllowed (graph : LGraphId) (layers : Array LayerId) : LayeredM (Array Bool) := do
  let mut cutsAllowed := Array.replicate layers.size false
  let gr ← getGraph graph
  if gr.props.has LayeredOptions.WRAPPING_VALIDIFY_FORBIDDEN_INDICES then
    let forbidden := (gr.props.get LayeredOptions.WRAPPING_VALIDIFY_FORBIDDEN_INDICES).getD #[]
    for f in forbidden do
      if f > 0 && f < (cutsAllowed.size : Int) then
        cutsAllowed := cutsAllowed.set! f.toNat false
    return cutsAllowed
  for idx in [1:layers.size] do
    cutsAllowed := cutsAllowed.set! idx (← isCutAllowedLayer layers[idx]!)
  return cutsAllowed

/-- `GraphStats(graph)` (Rust `GraphStats::new`). -/
def new (graph : LGraphId) : LayeredM GraphStats := do
  let gr ← getGraph graph
  let direction := (gr.props.get LayeredOptions.DIRECTION).getD .undefined
  let aspectRatio := (gr.props.get LayeredOptions.ASPECT_RATIO).getD LayeredOptions.ASPECT_RATIO_DEFAULT
  let correction := (gr.props.get LayeredOptions.WRAPPING_CORRECTION_FACTOR).getD fl1p0
  let dar := match direction with
    | .left | .right | .undefined => aspectRatio * correction
    | _ => fl1p0 / (aspectRatio * correction)
  let spacing := (gr.props.get LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS).getD fl0p0
  let inLayerSpacing := (gr.props.get LayeredOptions.SPACING_NODE_NODE).getD fl0p0
  let layers := gr.layers
  let mut widths : Array Float := #[]
  let mut heights : Array Float := #[]
  for layer in layers do
    widths := widths.push (← determineLayerWidth layer spacing)
    heights := heights.push (← determineLayerHeight layer inLayerSpacing)
  -- Java `stream().reduce(Math::max).get()` / `reduce((a, b) -> a + b).get()`: a left fold from the
  -- first layer (the processors return before for an empty layering)
  let maxWidth := if widths.isEmpty then fl0p0 else (widths.extract 1 widths.size).foldl javaMax widths[0]!
  let maxHeight := if heights.isEmpty then fl0p0 else (heights.extract 1 heights.size).foldl javaMax heights[0]!
  let sumWidth := if widths.isEmpty then fl0p0 else (widths.extract 1 widths.size).foldl (· + ·) widths[0]!
  let cutsAllowed ← initCutAllowed graph layers
  return { dar, longestPath := layers.size, maxWidth, maxHeight, sumWidth, widths, heights, cutsAllowed }

/-- `isCutAllowed(layerIndex)`: `false` outside the layer range (Rust `get(..)` → `false`). -/
def isCutAllowed (gs : GraphStats) (layerIndex : Int) : Bool :=
  if layerIndex < 0 then false else gs.cutsAllowed.getD layerIndex.toNat false

end GraphStats

end Elk.Alg.Layered.Intermediate.Wrapping
