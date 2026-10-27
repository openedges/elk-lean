import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Intermediate.Loops.Ops
/-!
# `org.eclipse.elk.alg.layered.intermediate.SelfLoopPostProcessor`

Port of elk-rs `intermediate/self_loop_postprocessor.rs`. For every normal node (in layer order)
with a `SelfLoopHolder` it moves the hyper loop label blocks and labels into absolute coordinates
and reconnects the self-loop edges, offsetting their bend points by the node position.

Rust/Java difference (Rust followed): Java calls `SelfHyperLoopLabels.applyPlacement(nodePosition)`
here (after reconnecting all edges); Rust expects the router to have placed the labels already
(relative to the node) and adds the node position to the label block position and to every label
position, loop by loop, before reconnecting that loop's edges.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate.Loops LayeredM

namespace SelfLoopPostProcessor

/-- `process_node(node)`: label offsets and edge restoration, hyper loop by hyper loop. -/
def processNode (n : LNodeId) : LayeredM Unit := do
  let some h ← SelfLoopHolder.get? n | return
  let nodePos := (← getNode n).position
  for l in h.hyperLoopIds do
    let loop := h.slHyperLoop l
    if let some labels := loop.slLabels then
      SelfLoopHolder.update n fun h => h.modifySLHyperLoop l fun x =>
        { x with slLabels := x.slLabels.map fun lb => { lb with position := lb.position + nodePos } }
      for lb in labels.lLabels do
        modifyLabel lb fun x => { x with position := x.position + nodePos }
    for e in loop.slEdges do
      let slEdge := h.slEdge e
      setEdgeSource slEdge.lEdge (some (h.lPortOf slEdge.slSource))
      setEdgeTarget slEdge.lEdge (some (h.lPortOf slEdge.slTarget))
      modifyEdge slEdge.lEdge fun x => { x with bendPoints := x.bendPoints.offset nodePos }

/-- `process(graph, monitor)` body: the nodes of all layers, in order. -/
def run (graph : LGraphId) : LayeredM Unit := do
  for layer in (← getGraph graph).layers do
    for n in (← getLayer layer).nodes do
      let nd ← getNode n
      if nd.type == .normal && nd.internal.selfLoopHolder.isSome then
        processNode n

/-- The `SelfLoopPostProcessor` intermediate processor. -/
def processor : LayeredProcessor :=
  { name := "SelfLoopPostProcessor"
    process := fun graph monitor => do
      let _ ← monitor.begin "Self-Loop post-processing" 1.0
      run graph
      monitor.done }

end SelfLoopPostProcessor

builtin_initialize registerSelfLoopPostProcessor : Unit ←
  IntermediateProcessorStrategy.register .selfLoopPostprocessor SelfLoopPostProcessor.processor

end Elk.Alg.Layered.Intermediate
