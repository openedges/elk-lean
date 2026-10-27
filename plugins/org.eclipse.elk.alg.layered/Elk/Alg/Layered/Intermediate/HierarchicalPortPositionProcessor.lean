import Elk.Alg.Layered.LayeredPhases
/-!
# `org.eclipse.elk.alg.layered.intermediate.HierarchicalPortPositionProcessor`

Port of elk-rs `intermediate/hierarchical_port_position_processor.rs`. With `FIXED_RATIO` or
`FIXED_POS` port constraints on the graph, the eastern and western external port dummies of the first
and (if different) the last layer get their final y coordinate from `PORT_RATIO_OR_POSITION` (scaled
by the graph's actual height for `FIXED_RATIO`), corrected by the dummy's `PORT_ANCHOR`, the graph's
top padding and its y offset.

Precondition: a layered graph with node placement done. Slot: before phase 5.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace HierarchicalPortPositionProcessor

/-- `fixCoordinates(layer, layeredGraph)` (Rust `fix_coordinates`):
`y = ratioOrPos (· actualHeight) - anchor.y - padding.top - offset.y`, evaluated left to right. -/
def fixCoordinates (layer : LayerId) (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let portConstraints := gr.props.getD CoreOptions.PORT_CONSTRAINTS PortConstraints.undefined
  if !(portConstraints.isRatioFixed || portConstraints.isPosFixed) then return
  let graphHeight := gr.actualSize.y
  let paddingTop := gr.padding.top
  let offsetY := gr.offset.y
  for node in (← getLayer layer).nodes do
    let nd ← getNode node
    if nd.type != .externalPort then continue
    let extSide := nd.internal.extPortSide
    if extSide != .east && extSide != .west then continue
    let anchor := (nd.props.get CoreOptions.PORT_ANCHOR).getD {}
    let mut finalY := nd.internal.portRatioOrPosition
    if portConstraints == .fixedRatio then finalY := finalY * graphHeight
    let y := finalY - anchor.y - paddingTop - offsetY
    modifyNode node fun x => { x with position := { x.position with y := y } }

/-- `process(layeredGraph, monitor)` body: the first and (if different) the last layer. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let layers := (← getGraph graph).layers
  if !layers.isEmpty then fixCoordinates layers[0]! graph
  if layers.size > 1 then fixCoordinates layers[layers.size - 1]! graph

/-- The `HierarchicalPortPositionProcessor`. -/
def processor : LayeredProcessor :=
  { name := "HierarchicalPortPositionProcessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Hierarchical port position processing" 1.0
      run graph
      monitor.done }

end HierarchicalPortPositionProcessor

builtin_initialize registerHierarchicalPortPositionProcessor : Unit ←
  IntermediateProcessorStrategy.register .hierarchicalPortPositionProcessor HierarchicalPortPositionProcessor.processor

end Elk.Alg.Layered.Intermediate
