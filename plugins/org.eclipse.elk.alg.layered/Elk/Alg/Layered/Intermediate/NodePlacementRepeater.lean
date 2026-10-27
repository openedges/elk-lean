import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.Transform.LGraphAdapters
import Elk.Alg.Common.NodeSpacing.NodeDimensionCalculation
/-!
# `org.eclipse.elk.alg.layered.intermediate.NodePlacementRepeater`

Port of elk-rs `intermediate/node_placement_repeater.rs` (Java `NodePlacementRepeater`): "Repeats
node placement with the sizes produced by node flexibility fixed." Requested by the
`GraphConfigurator` after phase 4 when
`NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT` names a second node
placer.

Steps (Rust order): create the second placer; remove the graph's
`NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT`; for every layer node remove
`NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY` and `NODE_SIZE_CONSTRAINTS` (the default is a
fixed size) and reset `position.y` to `0`; recompute port and label positions of the `NORMAL`
nodes with `NodeLabelAndSizeCalculator.process` (fixed size: ports and labels are repositioned
without growing the sizes chosen by the first placer) on `LGraphAdapters.adapt(graph, true, true,
NORMAL)` with the graph's `DIRECTION`; recompute the margins
(`NodeDimensionCalculation.calculateNodeMargins`); run the second placer.

The placer is created through the phase registry (`LayeredPhases.strategyFactory .p4NodePlacement`,
the Rust `strategy.create_phase()`), which avoids importing the `p4nodes` package here. A missing
strategy throws `IllegalStateException` (Rust `expect("Missing second node placement strategy")`;
Java fails with a `NullPointerException`).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Options Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM
open Elk.Alg.Layered.Graph.Transform Elk.Alg.Common.NodeSpacing

namespace NodePlacementRepeater

/-- Rust `strategy.create_phase()` for the second node placer. -/
def createNodePlacer (strategy : NodePlacementStrategy) : IO LayeredPhase :=
  (LayeredPhases.strategyFactory .p4NodePlacement "NodePlacementStrategy" (ElkEnum.ordinal strategy)
    (ElkEnum.javaName strategy)).create

/-- `process(graph, monitor)` (Rust `process`): see the module doc. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Node placement repeater" 1.0
  let some strategy := (← getGraph graph).props.get
      LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_RECOMPUTE_NODE_PLACEMENT
    | throw (IO.userError "java.lang.IllegalStateException: Missing second node placement strategy")
  let nodePlacer ← createNodePlacer strategy
  -- disable node flexibility for the second node placement run
  modifyGraph graph fun g =>
    { g with props := g.props.remove LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT }
  for layer in (← getGraph graph).layers do
    for node in (← getLayer layer).nodes do
      modifyNode node fun n =>
        { n with
          -- removing the constraints restores their fixed-size default
          props := (n.props.remove LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY).remove
            LayeredOptions.NODE_SIZE_CONSTRAINTS
          position := { n.position with y := 0.0 } }
  let adapter ← LGraphAdapters.adapt graph true true fun n => n.type == .normal
  let direction ← adapter.graph.getPropertyD graph LayeredOptions.DIRECTION Direction.undefined
  -- the full calculator: its fixed-size path repositions ports and labels without growing sizes
  for node in ← adapter.getNodes graph do
    let _ ← NodeLabelAndSizeCalculator.process adapter node direction
  NodeDimensionCalculation.calculateNodeMargins adapter graph
  -- second node placement run
  nodePlacer.process graph monitor
  monitor.done

/-- The `NodePlacementRepeater` processor. -/
def processor : LayeredProcessor := { name := "NodePlacementRepeater", process := process }

end NodePlacementRepeater

builtin_initialize registerNodePlacementRepeater : Unit ←
  IntermediateProcessorStrategy.register .nodePlacementRepeater NodePlacementRepeater.processor

end Elk.Alg.Layered.Intermediate
