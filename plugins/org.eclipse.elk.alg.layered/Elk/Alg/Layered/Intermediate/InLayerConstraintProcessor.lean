import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.InLayerConstraintProcessor`

Port of elk-rs `intermediate/in_layer_constraint_processor.rs`. Per layer (snapshot of the node order),
`TOP` nodes found after the first non-`TOP` node are moved to the end of the leading `TOP` block (keeping
their relative order) and all `BOTTOM` nodes are moved to the end of the layer (in their original order).
The node order within each group is otherwise kept (a stable partition).

The monitor task name is elk-rs's ("Layer constraint edge reversal"). The `ELK_TRACE_ILC` debug print is
omitted.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace InLayerConstraintProcessor

/-- Reorders one layer (Rust loop body). -/
def processLayer (layer : LayerId) : LayeredM Unit := do
  let nodes := (← getLayer layer).nodes
  let mut topInsertionIndex : Option Nat := none
  let mut bottomConstrainedNodes : Array LNodeId := #[]
  let mut i := 0
  for node in nodes do
    let constraint := (← getNode node).internal.inLayerConstraint
    match topInsertionIndex with
    | none =>
      if constraint != .top then topInsertionIndex := some i
    | some insertIndex =>
      if constraint == .top then
        setNodeLayer node none
        setNodeLayerAtIndex node insertIndex (some layer)
        topInsertionIndex := some (insertIndex + 1)
    if constraint == .bottom then bottomConstrainedNodes := bottomConstrainedNodes.push node
    i := i + 1
  for node in bottomConstrainedNodes do
    setNodeLayer node none
    setNodeLayer node (some layer)

/-- `process(layeredGraph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  for layer in (← getGraph graph).layers do
    processLayer layer

/-- The `InLayerConstraintProcessor` processor. -/
def processor : LayeredProcessor :=
  { name := "InLayerConstraintProcessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Layer constraint edge reversal" 1.0
      run graph
      monitor.done }

end InLayerConstraintProcessor

builtin_initialize registerInLayerConstraintProcessor : Unit ←
  IntermediateProcessorStrategy.register .inLayerConstraintProcessor InLayerConstraintProcessor.processor

end Elk.Alg.Layered.Intermediate
