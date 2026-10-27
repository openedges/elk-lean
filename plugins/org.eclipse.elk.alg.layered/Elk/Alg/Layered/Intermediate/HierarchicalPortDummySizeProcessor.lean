import Elk.Alg.Layered.LayeredPhases
/-!
# `org.eclipse.elk.alg.layered.intermediate.HierarchicalPortDummySizeProcessor`

Port of elk-rs `intermediate/hierarchical_port_dummy_size_processor.rs`. Sets the widths of the
northern and southern external port dummies of each layer so that the edges attached to them are
routed with `SPACING_EDGE_EDGE_BETWEEN_LAYERS` between them: northern dummies get the widths
`0, d, 2d, …` (top-down), southern dummies `(k-1)d, …, d, 0`, with `d = 2 · spacing`. The eastern
ports of each dummy are moved to its new right border and its alignment is set to `CENTER`.

Precondition: a layered graph with north/south external port dummies (replaced by
`HierarchicalPortConstraintProcessor`). Slot: before phase 4.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace HierarchicalPortDummySizeProcessor

/-- `setWidths(nodes, topDown, delta)` (Rust `set_widths`). -/
def setWidths (nodes : Array LNodeId) (topDown : Bool) (delta : Float) : LayeredM Unit := do
  if nodes.isEmpty then return
  -- Rust `nodes.len().saturating_sub(1)`: `Nat` subtraction saturates the same way
  let mut currentWidth := if topDown then 0.0 else delta * (nodes.size - 1).toFloat
  let step := if topDown then delta else -delta
  for node in nodes do
    let width := currentWidth
    modifyNode node fun x => { x with
      props := x.props.set CoreOptions.ALIGNMENT Alignment.center
      size := { x.size with x := width } }
    for port in (← withArena (·.nodePortsBySide node .east)) do
      modifyPort port fun p => { p with position := { p.position with x := width } }
    currentWidth := currentWidth + step

/-- `process(layeredGraph, monitor)` body: per layer the northern and southern external port
dummies in layer order. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let edgeSpacing := (gr.props.get LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS).getD 0.0
  let delta := edgeSpacing * 2.0
  for layer in gr.layers do
    let mut northernDummies : Array LNodeId := #[]
    let mut southernDummies : Array LNodeId := #[]
    for node in (← getLayer layer).nodes do
      let nd ← getNode node
      if nd.type == .externalPort then
        if nd.internal.extPortSide == .north then northernDummies := northernDummies.push node
        else if nd.internal.extPortSide == .south then southernDummies := southernDummies.push node
    setWidths northernDummies true delta
    setWidths southernDummies false delta

/-- The `HierarchicalPortDummySizeProcessor`. -/
def processor : LayeredProcessor :=
  { name := "HierarchicalPortDummySizeProcessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Hierarchical port dummy size processing" 1.0
      run graph
      monitor.done }

end HierarchicalPortDummySizeProcessor

builtin_initialize registerHierarchicalPortDummySizeProcessor : Unit ←
  IntermediateProcessorStrategy.register .hierarchicalPortDummySizeProcessor HierarchicalPortDummySizeProcessor.processor

end Elk.Alg.Layered.Intermediate
