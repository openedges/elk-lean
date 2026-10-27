import Elk.Alg.Layered.LayeredPhases
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.layered.intermediate.InteractiveExternalPortPositioner`

Port of elk-rs `intermediate/interactive_external_port_positioner.rs`. For interactive layouts the
external port dummies need coordinates before cycle breaking/layering: western dummies
(`FIRST_SEPARATE`) are put left of all normal nodes, eastern ones (`LAST_SEPARATE`) right of them,
both at the y centre of the first connected node; northern (`TOP`) / southern (`BOTTOM`) dummies above
/ below all normal nodes, at the x coordinate of the connected nodes. The bounding box of the normal
nodes includes their `MARGINS` property.

Differences to Java (Rust is followed):
* Java takes the first of all connected edges (`getConnectedEdges`) for the y coordinate; Rust looks
  only at the outgoing (western) / incoming (eastern) edges, skipping dangling ends;
* Java handles the layer constraint and the in-layer constraint exclusively (`break`); Rust applies
  both when a dummy has both;
* Java throws `IllegalArgumentException` for non-normal nodes other than external port dummies and
  `IllegalStateException` for north/south dummies with incoming and outgoing edges; Rust skips the
  former and uses the outgoing edges first for the latter (falling back to the incoming ones).

Slot: before phase 1.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace InteractiveExternalPortPositioner

/-- `ARBITRARY_SPACING`: the spacing between external port dummies and the other nodes. -/
def ARBITRARY_SPACING : Float := 10.0

/-- Rust `find_y_from_targets` (western ports): the y centre of the target node of the node's first
outgoing edge with a target. -/
def findYFromTargets (node : LNodeId) : LayeredM (Option Float) := do
  for edge in (← withArena (·.nodeOutgoingEdges node)) do
    let some targetPort := (← getEdge edge).target | continue
    let some targetNode := (← getPort targetPort).owner | continue
    let nd ← getNode targetNode
    return some (nd.position.y + nd.size.y / 2.0)
  return none

/-- Rust `find_y_from_sources` (eastern ports): the y centre of the source node of the node's first
incoming edge with a source. -/
def findYFromSources (node : LNodeId) : LayeredM (Option Float) := do
  for edge in (← withArena (·.nodeIncomingEdges node)) do
    let some sourcePort := (← getEdge edge).source | continue
    let some sourceNode := (← getPort sourcePort).owner | continue
    let nd ← getNode sourceNode
    return some (nd.position.y + nd.size.y / 2.0)
  return none

/-- Rust `find_north_south_x` (`findNorthSouthPortXCoordinate`): on the dummy's first port, the
minimum left border (minus margin) of the targets of its outgoing edges, else the maximum right border
(plus margin) of the sources of its incoming edges. -/
def findNorthSouthX (node : LNodeId) : LayeredM (Option Float) := do
  let some port := (← getNode node).ports[0]? | return none
  let pt ← getPort port
  let mut min := Float.posInf
  for edge in pt.outgoingEdges do
    let some targetPort := (← getEdge edge).target | continue
    let some targetNode := (← getPort targetPort).owner | continue
    let nd ← getNode targetNode
    let margins := (nd.props.get CoreOptions.MARGINS).getD {}
    min := fmin min (nd.position.x - margins.left)
  if min != Float.posInf then return some min
  let mut max := Float.negInf
  for edge in pt.incomingEdges do
    let some sourcePort := (← getEdge edge).source | continue
    let some sourceNode := (← getPort sourcePort).owner | continue
    let nd ← getNode sourceNode
    let margins := (nd.props.get CoreOptions.MARGINS).getD {}
    max := fmax max (nd.position.x + nd.size.x + margins.right)
  return if max != Float.negInf then some max else none

/-- `process(layeredGraph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  if !gr.internal.graphProperties.contains .externalPorts then return
  let nodes := gr.layerlessNodes
  let mut minX := Float.posInf
  let mut maxX := Float.negInf
  let mut minY := Float.posInf
  let mut maxY := Float.negInf
  for node in nodes do
    let nd ← getNode node
    if nd.type == .normal then
      let pos := nd.position
      let size := nd.size
      let margins := (nd.props.get CoreOptions.MARGINS).getD {}
      minX := fmin minX (pos.x - margins.left)
      maxX := fmax maxX (pos.x + size.x + margins.right)
      minY := fmin minY (pos.y - margins.top)
      maxY := fmax maxY (pos.y + size.y + margins.bottom)
  for node in nodes do
    let nd ← getNode node
    if nd.type != .externalPort then continue
    let layerConstraint := nd.props.get LayeredOptions.LAYERING_LAYER_CONSTRAINT
    let inLayerConstraint := nd.internal.inLayerConstraint
    let mut xFrom : Option Float := none
    let mut yFrom : Option Float := none
    match layerConstraint with
    | some .firstSeparate => yFrom ← findYFromTargets node
    | some .lastSeparate => yFrom ← findYFromSources node
    | _ => pure ()
    if inLayerConstraint == .top || inLayerConstraint == .bottom then
      xFrom ← findNorthSouthX node
    let mut pos := (← getNode node).position
    match layerConstraint with
    | some .firstSeparate =>
      pos := { pos with x := minX - ARBITRARY_SPACING }
      if let some y := yFrom then pos := { pos with y := y }
    | some .lastSeparate =>
      pos := { pos with x := maxX + ARBITRARY_SPACING }
      if let some y := yFrom then pos := { pos with y := y }
    | _ => pure ()
    match inLayerConstraint with
    | .top =>
      if let some x := xFrom then pos := { pos with x := x + ARBITRARY_SPACING }
      pos := { pos with y := minY - ARBITRARY_SPACING }
    | .bottom =>
      if let some x := xFrom then pos := { pos with x := x + ARBITRARY_SPACING }
      pos := { pos with y := maxY + ARBITRARY_SPACING }
    | .none => pure ()
    let finalPos := pos
    modifyNode node fun x => { x with position := finalPos }

/-- The `InteractiveExternalPortPositioner`. -/
def processor : LayeredProcessor :=
  { name := "InteractiveExternalPortPositioner"
    process := fun graph _monitor => run graph }

end InteractiveExternalPortPositioner

builtin_initialize registerInteractiveExternalPortPositioner : Unit ←
  IntermediateProcessorStrategy.register .interactiveExternalPortPositioner InteractiveExternalPortPositioner.processor

end Elk.Alg.Layered.Intermediate
