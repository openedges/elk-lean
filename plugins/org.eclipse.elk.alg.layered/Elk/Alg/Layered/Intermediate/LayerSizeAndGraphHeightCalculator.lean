import Elk.Alg.Layered.LayeredPhases
import Elk.Core.Util.Java
/-!
# `org.eclipse.elk.alg.layered.intermediate.LayerSizeAndGraphHeightCalculator`

Port of elk-rs `intermediate/layer_size_and_graph_height_calculator.rs` (Java
`LayerSizeAndGraphHeightCalculator`): "Calculates the size of each layer, the height of the graph,
and the graph's vertical offset. The graph's width cannot be set at this point since that would
require the edge routing phase to have already finished."

Slot: before phase 5. Precondition: node placement is finished and node margins are calculated.

elk-rs runs the computation on an `ArenaSync` copy (`all_layer_ids` = the graph's layers in order,
`layer_nodes` = the layer's node list) and syncs the layer sizes back; the Lean port works on the
arena directly in the same order (`PORTING.md` §15.1). `f64::max`/`f64::min` are `fmax`/`fmin`.
The `ELK_TRACE_LAYER_HEIGHT` debug output of elk-rs is omitted.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace LayerSizeAndGraphHeightCalculator

/-- Rust `spacing_ports_surrounding(graph)`: the stored `SPACING_PORTS_SURROUNDING` (its default when
it cannot be read), or an empty margin when the property is not set. -/
def spacingPortsSurrounding (graph : LGraphId) : LayeredM ElkMargin := do
  let gr ← getGraph graph
  if gr.props.has LayeredOptions.SPACING_PORTS_SURROUNDING then
    return gr.props.getD LayeredOptions.SPACING_PORTS_SURROUNDING {}
  return {}

/-- `process(layeredGraph, monitor)`: per layer the width (`max(size.x + margin.left + margin.right)`)
and height (`bottom - top` of the first and last node incl. margins; external port dummies add the
surrounding port spacing), then the graph height `maxY - minY` and `offset.y -= minY`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Layer size calculation" 1.0
  let spacing ← spacingPortsSurrounding graph
  let mut minY := Float.posInf
  let mut maxY := Float.negInf
  let mut foundNodes := false
  let layers := (← getGraph graph).layers
  for layer in layers do
    modifyLayer layer fun l => { l with size := ⟨0.0, 0.0⟩ }
    let nodeIds := (← getLayer layer).nodes
    if nodeIds.isEmpty then continue
    foundNodes := true
    let mut layerWidth : Float := 0.0
    for nid in nodeIds do
      let nd ← getNode nid
      layerWidth := fmax layerWidth (nd.size.x + nd.margin.left + nd.margin.right)
    let first ← getNode nodeIds[0]!
    let mut top := first.position.y - first.margin.top
    if first.type == .externalPort then
      top := top - spacing.top
    let last ← getNode nodeIds[nodeIds.size - 1]!
    let mut bottom := last.position.y + last.size.y + last.margin.bottom
    if last.type == .externalPort then
      bottom := bottom + spacing.bottom
    let width := layerWidth
    let height := bottom - top
    modifyLayer layer fun l => { l with size := ⟨width, height⟩ }
    minY := fmin minY top
    maxY := fmax maxY bottom
  if !foundNodes then
    minY := 0.0
    maxY := 0.0
  let sizeY := maxY - minY
  let offsetY := minY
  modifyGraph graph fun g =>
    { g with size := { g.size with y := sizeY }, offset := { g.offset with y := g.offset.y - offsetY } }
  monitor.done

/-- The `LayerSizeAndGraphHeightCalculator` processor. -/
def processor : LayeredProcessor := { name := "LayerSizeAndGraphHeightCalculator", process := process }

end LayerSizeAndGraphHeightCalculator

builtin_initialize registerLayerSizeAndGraphHeightCalculator : Unit ←
  IntermediateProcessorStrategy.register .layerSizeAndGraphHeightCalculator LayerSizeAndGraphHeightCalculator.processor

end Elk.Alg.Layered.Intermediate
