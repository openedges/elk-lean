import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.ReversedEdgeRestorer`

Port of elk-rs `intermediate/reversed_edge_restorer.rs`. Restores the direction of the edges that
were reversed during cycle breaking (`REVERSED`): each such edge is reversed again without port
adaptation (`LEdge.reverse(graph, false)`: source and target swapped, bend points reversed,
`HEAD`/`TAIL` labels swapped, `REVERSED` toggled back).

Iteration order (Rust): layers → nodes (copy per layer) → ports (copy per node) → outgoing edges
(copy per port, read when the port is visited); an edge moved to a port visited later is no
longer marked `REVERSED` there. Rust passes a placeholder graph to `LEdge::reverse`; the graph is
only used for collector ports, which `adaptPorts = false` never requests.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM

namespace ReversedEdgeRestorer

/-- `process(layered_graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Restoring reversed edges" 1.0
  for layer in (← getGraph graph).layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      let ports := (← getNode node).ports
      for port in ports do
        let outgoing := (← getPort port).outgoingEdges
        for edge in outgoing do
          if (← getEdge edge).internal.reversed then
            LGraphUtil.reverseEdge edge graph false
  monitor.done

/-- The `ReversedEdgeRestorer` processor. -/
def processor : LayeredProcessor := { name := "ReversedEdgeRestorer", process := process }

end ReversedEdgeRestorer

builtin_initialize registerReversedEdgeRestorer : Unit ←
  IntermediateProcessorStrategy.register .reversedEdgeRestorer ReversedEdgeRestorer.processor

end Elk.Alg.Layered.Intermediate
