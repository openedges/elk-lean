import Elk.Alg.Common.Geometry.RectilinearConvexHull
import Elk.Alg.Layered.Components.AbstractGraphPlacer
import Elk.Alg.Layered.Components.Compaction.OneDimensionalComponentsCompaction
/-!
# `org.eclipse.elk.alg.layered.components.ComponentsCompactor`

Port of `components/compaction/mod.rs` (elk-rs; Java `ComponentsCompactor`): turns every
component into its rectilinear convex hull (node bounds with margins, inner bend points, the
inner segments of external edges) plus one extension per external side, compacts them with
`OneDimensionalComponentsCompaction.pack` and moves the components (and their external port
dummies to the border of the common frame).

The elk-rs compactor works on the shared absolute coordinate system of the components: the
`frame` is the bounding box of all component nodes (with margins). `maybeCompactComponents` is
Rust `maybe_compact_components` of `components_processor.rs`, the shared compaction step of
the placers (Java repeats it in each placer).

Rust `unreachable!`/`expect` cases (external edges at external ports without side, missing
edge ends or owners) throw `java.lang.IllegalStateException`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl0p0001 : Float := 0.0001
private def fl1p0 : Float := 1.0
private def fl20p0 : Float := 20.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Layered.Components.Compaction

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Common
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Components LayeredM AbstractGraphPlacer

namespace ComponentsCompactor

/-- Rust `Bounds`: an axis-aligned bounding box, initially empty (`±∞`). -/
structure Bounds where
  min : KVector := ⟨Float.posInf, Float.posInf⟩
  max : KVector := ⟨Float.negInf, Float.negInf⟩
  deriving Inhabited

namespace Bounds

/-- Rust `include(point)` (`f64::min` / `f64::max`; `include` is a Lean keyword). -/
def includePoint (b : Bounds) (p : KVector) : Bounds :=
  { min := ⟨fmin b.min.x p.x, fmin b.min.y p.y⟩, max := ⟨fmax b.max.x p.x, fmax b.max.y p.y⟩ }

/-- `external_position(point, side)`: moves a point onto the frame border of `side`. -/
def externalPosition (b : Bounds) (p : KVector) (side : PortSide) : KVector :=
  match side with
  | .north => { p with y := fmin p.y b.min.y }
  | .east => { p with x := fmax p.x b.max.x }
  | .south => { p with y := fmax p.y b.max.y }
  | .west => { p with x := fmin p.x b.min.x }
  | .undefined => p

end Bounds

/-- Rust `HullPoints`: the hull points with their bounds. -/
structure HullPoints where
  points : Array Point := #[]
  bounds : Bounds := {}
  deriving Inhabited

namespace HullPoints

/-- `add(point)`. -/
def add (h : HullPoints) (p : KVector) : HullPoints :=
  { points := h.points.push (Point.new p.x p.y), bounds := h.bounds.includePoint p }

/-- `rectangle(rect)`: top-left, bottom-left, top-right, bottom-right. -/
def rectangle (h : HullPoints) (r : ElkRectangle) : HullPoints :=
  ((h.add r.topLeft).add r.bottomLeft |>.add r.topRight).add r.bottomRight

end HullPoints

private def illegalState {α : Type} (msg : String) : LayeredM α :=
  throw (IO.userError s!"java.lang.IllegalStateException: {msg}")

/-- Rust `side_index(side)` (`unreachable!` for `UNDEFINED`). -/
def sideIndex (side : PortSide) : LayeredM Nat :=
  match side with
  | .north => pure 0
  | .east => pure 1
  | .south => pure 2
  | .west => pure 3
  | .undefined => illegalState "external port has a side"

/-- Rust `node_bounds(node)`: the node's bounds including its margins. -/
def nodeBounds (node : LNodeId) : LayeredM ElkRectangle := do
  let nd ← getNode node
  let pos := nd.position
  let size := nd.size
  let margin := nd.margin
  return ⟨pos.x - margin.left, pos.y - margin.top, size.x + margin.left + margin.right,
    size.y + margin.top + margin.bottom⟩

/-- The owner of a port (Rust `port.lock().node().unwrap()`). -/
private def portOwner (port : LPortId) : LayeredM LNodeId := do
  match (← getPort port).owner with
  | some n => return n
  | none => illegalState "component port belongs to a node"

/-- `port.absolute_anchor().expect(..)`. -/
private def absoluteAnchor (port : LPortId) : LayeredM KVector := do
  match ← withArena (·.portAbsoluteAnchor port) with
  | some v => return v
  | none => illegalState "component port belongs to a node"

/-- Rust `edge_path(edge)`: source, target and a copy of the bend points. -/
def edgePath (edge : LEdgeId) : LayeredM (LPortId × LPortId × KVectorChain) := do
  let ed ← getEdge edge
  match ed.source, ed.target with
  | some s, some t => return (s, t, ed.bendPoints)
  | _, _ => illegalState "component edge has a source and a target"

/-- Rust `external(edge)`: whether one end of the edge is an external port dummy. -/
def isExternal (edge : LEdgeId) : LayeredM Bool := do
  let (source, target, _) ← edgePath edge
  let sourceNode ← portOwner source
  let targetNode ← portOwner target
  return (← getNode sourceNode).type == .externalPort || (← getNode targetNode).type == .externalPort

/-- Rust `margin_anchor(port)`: the absolute anchor moved onto the owner's margin border. -/
def marginAnchor (port : LPortId) : LayeredM KVector := do
  let position ← absoluteAnchor port
  let side := (← getPort port).side
  let margin := (← getNode (← portOwner port)).margin
  return match side with
    | .north => { position with y := position.y - margin.top }
    | .east => { position with x := position.x + margin.right }
    | .south => { position with y := position.y + margin.bottom }
    | .west => { position with x := position.x - margin.left }
    | .undefined => position

/-- Rust `create_dummy(graph, external)`: a component consisting only of external port dummies
gets a small normal dummy node (connected to the first dummy's port) so it has a hull. -/
def createDummy (graph : LGraphId) (external : LNodeId) : LayeredM Unit := do
  let ext ← getNode external
  let mut position := ext.position
  let size := ext.size
  let side := ext.internal.extPortSide
  let some port := ext.ports[0]? | illegalState "external port dummy has a port"
  match side with
  | .west => position := { position with x := position.x + fl2p0 }
  | .east => position := { position with x := position.x - fl2p0 }
  | .north => position := { position with y := position.y + fl2p0 }
  | .south => position := { position with y := position.y - fl2p0 }
  | .undefined => pure ()
  let dummy ← createNode graph { position := position, size := ⟨fmax size.x fl1p0, fmax size.y fl1p0⟩ }
  modifyGraph graph fun g => { g with layerlessNodes := g.layerlessNodes.push dummy }
  let dummyPort ← LayeredM.createPort
  setPortNode dummyPort (some dummy)
  let edge ← createEdge
  setEdgeSource edge (some port)
  setEdgeTarget edge (some dummyPort)
  let pt ← getPort port
  modifyPort dummyPort fun dp => { dp with position := pt.position, anchor := pt.anchor }

/-- Per-side accumulators of `transform` (index = `sideIndex`). -/
private structure SideAcc where
  min : Array Float := Array.replicate 4 Float.posInf
  max : Array Float := Array.replicate 4 Float.negInf
  extent : Array Float := Array.replicate 4 Float.negInf

/-- Rust `transform(graph, frame)`: the `Component` of a graph for the packer. -/
def transform (graph : LGraphId) (frame : Bounds) : LayeredM Component := do
  let mut nodes ← collectComponentNodes graph
  let mut anyNormal := false
  for n in nodes do
    if (← getNode n).type == .normal then anyNormal := true
  if !anyNormal then
    let some first := nodes[0]? | illegalState "component has nodes"
    createDummy graph first
    nodes ← collectComponentNodes graph
  let mut hull : HullPoints := {}
  for node in nodes do
    if (← getNode node).type == .externalPort then continue
    hull := hull.rectangle (← nodeBounds node)
    for edge in ← withArena (·.nodeOutgoingEdges node) do
      if !(← isExternal edge) then
        for point in (← getEdge edge).bendPoints do
          hull := hull.add point
  let mut acc : SideAcc := {}
  let mut externalEdges : Array LEdgeId := #[]
  for node in nodes do
    for edge in ← withArena (·.nodeOutgoingEdges node) do
      if !(← isExternal edge) then continue
      let (source, target, bends) ← edgePath edge
      let sourceNode ← portOwner source
      let sourceExternal := (← getNode sourceNode).type == .externalPort
      let externalNode ← if sourceExternal then pure sourceNode else portOwner target
      let side := (← getNode externalNode).internal.extPortSide
      let first ← if sourceExternal then pure (frame.externalPosition (← absoluteAnchor source) side)
        else marginAnchor source
      let last ← if sourceExternal then marginAnchor target
        else pure (frame.externalPosition (← absoluteAnchor target) side)
      let points := #[first] ++ bends ++ #[last]
      let thickness := fmax ((← getEdge edge).props.getD CoreOptions.EDGE_THICKNESS fl0p0) fl1p0
      for index in [0:points.size - 1] do
        let a := points[index]!
        let b := points[index + 1]!
        let rect : ElkRectangle := ⟨fmin a.x b.x - thickness / fl2p0, fmin a.y b.y - thickness / fl2p0,
          Float.abs (a.x - b.x) + thickness, Float.abs (a.y - b.y) + thickness⟩
        let outer := if sourceExternal then index == 0 else index == points.size - 2
        if outer then
          let i ← sideIndex side
          let (low, length) := if side == .west || side == .east then (rect.y, rect.height) else (rect.x, rect.width)
          acc := { acc with min := acc.min.set! i (fmin acc.min[i]! low),
                            max := acc.max.set! i (fmax acc.max[i]! (low + length)) }
        else
          hull := hull.rectangle rect
      let margin := (← getNode externalNode).margin
      let value ← match side with
        | .west => pure margin.right
        | .east => pure margin.left
        | .north => pure margin.bottom
        | .south => pure margin.top
        | .undefined => illegalState "external port has a side"
      let i ← sideIndex side
      acc := { acc with extent := acc.extent.set! i (fmax acc.extent[i]! value) }
      externalEdges := externalEdges.push edge
  let sides := (← getGraph graph).internal.extPortConnections
  let mut extensions : Array ComponentExtension := #[]
  for side in sides.toArray do
    let i ← sideIndex side
    let lo := acc.min[i]!
    let length := acc.max[i]! - lo
    let width := acc.extent[i]!
    let (rectangle, placeholder) : ElkRectangle × ElkRectangle := match side with
      | .west => (⟨frame.min.x, lo, hull.bounds.min.x - frame.min.x, length⟩, ⟨frame.min.x, lo, width, length⟩)
      | .east => (⟨hull.bounds.max.x, lo, frame.max.x - hull.bounds.max.x, length⟩,
          ⟨frame.max.x - width, lo, width, length⟩)
      | .north => (⟨lo, frame.min.y, length, hull.bounds.min.y - frame.min.y⟩, ⟨lo, frame.min.y, length, width⟩)
      | .south => (⟨lo, hull.bounds.max.y, length, frame.max.y - hull.bounds.max.y⟩,
          ⟨lo, frame.max.y - width, length, width⟩)
      | .undefined => (default, default)
    match side with
    | .west => hull := (hull.add rectangle.topRight).add rectangle.bottomRight
    | .east => hull := (hull.add rectangle.topLeft).add rectangle.bottomLeft
    | .north => hull := (hull.add rectangle.bottomLeft).add rectangle.bottomRight
    | .south => hull := (hull.add rectangle.topLeft).add rectangle.topRight
    | .undefined => pure ()
    extensions := extensions.push { rectangle, placeholder, side }
  return { hull := (RectilinearConvexHull.of hull.points).splitIntoRectangles, sides, extensions, externalEdges }

/-- Rust `compact(graphs, spacing)` (Java `ComponentsCompactor.compact`): compacts the
components (already in a common coordinate system) and returns the new graph size and the
offset every component graph has to get. -/
def compact (graphs : Array LGraphId) (spacing : Float) : LayeredM (KVector × KVector) := do
  let mut frame : Bounds := {}
  for graph in graphs do
    for node in ← collectComponentNodes graph do
      let rect ← nodeBounds node
      frame := (frame.includePoint rect.topLeft).includePoint rect.bottomRight
  let mut components : Array Component := #[]
  for graph in graphs do
    components := components.push (← transform graph frame)
  let (offsets, packedSize) ← OneDimensionalComponentsCompaction.pack components spacing
  let mut size := packedSize
  for (graph, offset) in graphs.zip offsets do
    offsetGraph graph offset.x offset.y
    for node in ← collectComponentNodes graph do
      let nd ← getNode node
      if nd.type == .externalPort then
        let position := frame.externalPosition nd.position nd.internal.extPortSide
        modifyNode node fun x => { x with position := position }
  -- Only the coordinate perpendicular to an external edge segment contributes.
  let mut offset : KVector := ⟨fl0p0, fl0p0⟩
  for component in components do
    for edge in component.externalEdges do
      let (source, target, bends) ← edgePath edge
      let points := #[← absoluteAnchor source] ++ bends ++ #[← absoluteAnchor target]
      for index in [0:points.size - 1] do
        let s0 := points[index]!
        let s1 := points[index + 1]!
        if Float.abs (s0.x - s1.x) <= fl0p0001 then
          offset := { offset with x := fmin offset.x s0.x }
          size := { size with x := fmax size.x s0.x }
        else if Float.abs (s0.y - s1.y) <= fl0p0001 then
          offset := { offset with y := fmin offset.y s0.y }
          size := { size with y := fmax size.y s0.y }
  offset := ⟨-offset.x, -offset.y⟩
  size := ⟨size.x + offset.x, size.y + offset.y⟩
  return (size, offset)

end ComponentsCompactor

/-- Rust `maybe_compact_components(components, target, require_orthogonal)`: if
`COMPACTION_CONNECTED_COMPONENTS` is set on the first component (and, for the group placers,
the edges are routed orthogonally), applies every component's offset to its nodes, compacts
the components and stores the common offset and the new target size. -/
def maybeCompactComponents (components : Array LGraphId) (target : LGraphId) (requireOrthogonal : Bool) :
    LayeredM Unit := do
  if components.size < 2 then return
  let some firstId := components[0]? | return
  let first ← getGraph firstId
  let compactEnabled := first.props.getD LayeredOptions.COMPACTION_CONNECTED_COMPONENTS false
  let edgeRouting := first.props.getD LayeredOptions.EDGE_ROUTING EdgeRouting.orthogonal
  if !compactEnabled then return
  if requireOrthogonal && edgeRouting != .orthogonal then return
  -- Java parity: component compaction works in a shared absolute coordinate system.
  for component in components do
    let off := (← getGraph component).offset
    if off.x != fl0p0 || off.y != fl0p0 then
      offsetGraph component off.x off.y
    modifyGraph component fun g => { g with offset := ⟨fl0p0, fl0p0⟩ }
  let spacing := (← getGraph firstId).props.getD LayeredOptions.SPACING_COMPONENT_COMPONENT fl20p0
  let (size, offset) ← ComponentsCompactor.compact components spacing
  for component in components do
    modifyGraph component fun g => { g with offset := offset }
  modifyGraph target fun g => { g with size := size }

end Elk.Alg.Layered.Components.Compaction
