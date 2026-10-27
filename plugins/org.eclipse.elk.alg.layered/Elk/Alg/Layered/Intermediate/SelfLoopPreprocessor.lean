import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.Intermediate.Loops.Ops
/-!
# `org.eclipse.elk.alg.layered.intermediate.SelfLoopPreProcessor`

Port of elk-rs `intermediate/self_loop_preprocessor.rs`. For every layerless node with self loops
it installs a `SelfLoopHolder`, configures the hyper loop labels, detaches the self-loop edges
from their ports and — unless the port order is fixed or the node is a hierarchical node with
external ports — removes the ports that only carry self loops from the node (they are restored
by `SelfLoopPortRestorer`).

Rust/Java difference (Rust followed): the label direction (`DIRECTION` of the graph, `RIGHT` if
unset — the option default `UNDEFINED` is not horizontal) and spacing (`SPACING_LABEL_LABEL` of
the graph) are read once from the graph and set on the hyper loop labels here, instead of in the
`SelfHyperLoopLabels` constructor (`getIndividualOrInherited` on the node).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Options Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate.Loops LayeredM

namespace SelfLoopPreProcessor

/-- `set_hyper_loop_label_properties(holder, spacing, horizontal)`: sets the layout direction and
then the label-label spacing on every hyper loop's labels (each recalculating the size). -/
def setHyperLoopLabelProperties (n : LNodeId) (spacing : Float) (horizontal : Bool) : LayeredM Unit := do
  let some h ← SelfLoopHolder.get? n | return
  let loops ← withArena fun a =>
    let sizeOf := fun (l : LLabelId) => (a.label l).size
    h.slHyperLoops.map fun loop =>
      { loop with slLabels := loop.slLabels.map fun labels =>
          (labels.setLayoutDirectionHorizontal horizontal sizeOf).setLabelLabelSpacing spacing sizeOf }
  SelfLoopHolder.update n fun h => { h with slHyperLoops := loops }

/-- `hide_self_loops(holder)`: disconnects every self-loop edge (source, then target). -/
def hideSelfLoops (n : LNodeId) : LayeredM Unit := do
  let some h ← SelfLoopHolder.get? n | return
  for e in h.allSelfLoopEdges do
    setEdgeSource e none
    setEdgeTarget e none

/-- `hide_ports(holder)`: unless the node's port order is fixed or its nested graph has external
ports, removes every self-loop port that had only self loops from the node and marks it (and the
holder) hidden. Ports are visited in map order. -/
def hidePorts (n : LNodeId) : LayeredM Unit := do
  let some h ← SelfLoopHolder.get? n | return
  let nd ← getNode n
  let orderFixed := ((nd.props.get LayeredOptions.PORT_CONSTRAINTS).getD .undefined).isOrderFixed
  let hierarchyMode ← match nd.nestedGraph with
    | some g => pure ((← getGraph g).internal.graphProperties.contains .externalPorts)
    | none => pure false
  if orderFixed || hierarchyMode then return
  for p in h.slPortValues do
    let slPort := h.slPort p
    if !slPort.hadOnlySelfLoops then continue
    setPortNode slPort.lPort none
    SelfLoopHolder.update n fun h =>
      { (h.modifySLPort p fun x => { x with isHidden := true }) with arePortsHidden := true }

/-- `process(graph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  let labelLabelSpacing := (gr.props.get LayeredOptions.SPACING_LABEL_LABEL).getD 0.0
  let direction := (gr.props.get LayeredOptions.DIRECTION).getD .right
  let layoutDirHorizontal := direction.isHorizontal
  for n in gr.layerlessNodes do
    if ← withArena (SelfLoopHolder.needsSelfLoopProcessing · n) then
      let _ ← SelfLoopHolder.install n
      setHyperLoopLabelProperties n labelLabelSpacing layoutDirHorizontal
      hideSelfLoops n
      hidePorts n

/-- The `SelfLoopPreProcessor` intermediate processor. -/
def processor : LayeredProcessor :=
  { name := "SelfLoopPreProcessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Self-Loop pre-processing" 1.0
      run graph
      monitor.done }

end SelfLoopPreProcessor

builtin_initialize registerSelfLoopPreProcessor : Unit ←
  IntermediateProcessorStrategy.register .selfLoopPreprocessor SelfLoopPreProcessor.processor

end Elk.Alg.Layered.Intermediate
