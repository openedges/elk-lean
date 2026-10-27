import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.ConstraintsPostprocessor`

Port of elk-rs `intermediate/constraints_postprocessor.rs`. Writes the computed layering and in-layer
order back as constraints: every `NORMAL` node gets `LAYERING_LAYER_ID` (index among the layers that
contain at least one normal node) and `CROSSING_MINIMIZATION_POSITION_ID` (index among the normal nodes of
its layer). Dummy nodes are skipped and do not count.

elk-rs copies the graph into an `ArenaSync` and syncs the node properties back; the Lean port writes the
arena directly in the same order (`graph.layers`, then `layer.nodes`; see `PORTING.md` §15.1).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace ConstraintsPostprocessor

/-- `process(graph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let mut layerIndex : Int := 0
  for layer in (← getGraph graph).layers do
    let mut positionIndex : Int := 0
    let mut hasNormalNode := false
    for node in (← getLayer layer).nodes do
      if (← getNode node).type != .normal then continue
      hasNormalNode := true
      setNodeProp node LayeredOptions.LAYERING_LAYER_ID layerIndex
      setNodeProp node LayeredOptions.CROSSING_MINIMIZATION_POSITION_ID positionIndex
      positionIndex := positionIndex + 1
    -- like Java: layers without normal nodes do not increase the layer id
    if hasNormalNode then layerIndex := layerIndex + 1

/-- The `ConstraintsPostprocessor` processor. -/
def processor : LayeredProcessor :=
  { name := "ConstraintsPostprocessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Constraints Postprocessor" 1.0
      run graph
      monitor.done }

end ConstraintsPostprocessor

builtin_initialize registerConstraintsPostprocessor : Unit ←
  IntermediateProcessorStrategy.register .constraintsPostprocessor ConstraintsPostprocessor.processor

end Elk.Alg.Layered.Intermediate
