import Elk.Core.Alg
import Elk.Core.LayoutProvider
import Elk.Core.Options
import Elk.Alg.TopdownPacking.GridElkNode
import Elk.Alg.TopdownPacking.INodeArranger
import Elk.Alg.TopdownPacking.NodeArrangementStrategy
import Elk.Alg.TopdownPacking.WhitespaceEliminationStrategy
import Elk.Alg.TopdownPacking.TopdownPackingPhases
import Elk.Alg.TopdownPacking.LeftRightTopDownNodePlacer
import Elk.Alg.TopdownPacking.BottomRowEqualWhitespaceEliminator
import Elk.Alg.TopdownPacking.Options.TopdownpackingOptions
/-!
# `org.eclipse.elk.alg.topdownpacking.TopdownpackingLayoutProvider`

Port of `topdownpacking_layout_provider.rs` (elk-rs): assembles the two phases chosen by
`NODE_ARRANGEMENT_STRATEGY` / `WHITESPACE_ELIMINATION_STRATEGY` with an `AlgorithmAssembler`
and runs them, and predicts the graph size for top-down layout (`ITopdownLayoutProvider`).

The strategy factories of Rust (`NodeArrangementStrategy::create_phase` / `create_arranger`,
`WhitespaceEliminationStrategy::create_phase`) are defined here (`phaseFactory`, `createArranger`)
to keep the enumerations free of dependencies on the phase implementations.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl1p0 : Float := 1.0

namespace Elk.Alg.TopdownPacking

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Util
open Elk.Alg.TopdownPacking.Options

/-- `ILayoutPhase<TopdownPackingPhases, GridElkNode>`. -/
abbrev TopdownPackingPhase := LayoutPhase GridM TopdownPackingPhases GridElkNode TopdownPackingProcessors
/-- `ILayoutPhaseFactory<TopdownPackingPhases, GridElkNode>`. -/
abbrev TopdownPackingPhaseFactory :=
  LayoutPhaseFactory GridM TopdownPackingPhases GridElkNode TopdownPackingProcessors

namespace NodeArrangementStrategy

/-- `NodeArrangementStrategy::create_arranger()`. -/
def createArranger : NodeArrangementStrategy → INodeArranger
  | .leftRightTopDownNodePlacer => LeftRightTopDownNodePlacer.arranger

/-- `NodeArrangementStrategy` as `ILayoutPhaseFactory` (`create_phase`). -/
def phaseFactory (s : NodeArrangementStrategy) : TopdownPackingPhaseFactory :=
  LayoutPhaseFactory.ofEnum "NodeArrangementStrategy" s
    (match s with | .leftRightTopDownNodePlacer => pure LeftRightTopDownNodePlacer.phase)

end NodeArrangementStrategy

namespace WhitespaceEliminationStrategy

/-- `WhitespaceEliminationStrategy` as `ILayoutPhaseFactory` (`create_phase`). -/
def phaseFactory (s : WhitespaceEliminationStrategy) : TopdownPackingPhaseFactory :=
  LayoutPhaseFactory.ofEnum "WhitespaceEliminationStrategy" s
    (match s with
      | .bottomRowEqualWhitespaceEliminator => pure BottomRowEqualWhitespaceEliminator.phase)

end WhitespaceEliminationStrategy

namespace TopdownpackingLayoutProvider

/-- `assemble_algorithm(graph)`: the processor list for the strategies set on the graph's node. -/
def assembleAlgorithm (graph : GridElkNode) : GridM (Array (LayoutProcessor GridM GridElkNode)) := do
  let assembler : AlgorithmAssembler GridM TopdownPackingPhases GridElkNode TopdownPackingProcessors ←
    AlgorithmAssembler.create (fun _ =>
      throw (IO.userError "java.lang.UnsupportedOperationException: topdown packing has no intermediate processors"))
  let props := (← ElkM.getNode graph.node).props
  let nodeArrangement := props.getD TopdownpackingOptions.NODE_ARRANGEMENT_STRATEGY default
  let whitespaceElimination := props.getD TopdownpackingOptions.WHITESPACE_ELIMINATION_STRATEGY default
  assembler.setPhase .p1NodeArrangement nodeArrangement.phaseFactory
  assembler.setPhase .p2WhitespaceElimination whitespaceElimination.phaseFactory
  assembler.build graph

/-- `layout(layout_graph, progress_monitor)`. -/
def layout (layoutGraph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let wrapped := GridElkNode.new layoutGraph
  let run : GridM Unit := do
    let algorithm ← assembleAlgorithm wrapped
    let _ ← monitor.begin "Topdown Packing" algorithm.size.toFloat
    for processor in algorithm do
      let sub ← monitor.subTask fl1p0
      processor.process wrapped sub
    monitor.done
  StateRefT'.run' run wrapped

/-- `get_predicted_graph_size(graph)` (`ITopdownLayoutProvider`). -/
def predictedGraphSize (graph : NodeId) : ElkM KVector := do
  let strategy := (← ElkM.getNode graph).props.getD TopdownpackingOptions.NODE_ARRANGEMENT_STRATEGY default
  strategy.createArranger.getPredictedSize graph

/-- The `org.eclipse.elk.topdownpacking` layout provider as registered by elk-rs.

Deliberate deviation from Java (follows the Rust oracle): elk-rs implements
`ITopdownLayoutProvider` for `TopdownpackingLayoutProvider`, but its `AbstractLayoutProvider`
impl is empty, so `as_topdown_layout_provider()` returns `None` and
`RecursiveGraphLayoutEngine::apply_topdown_layout` never asks the provider for a predicted
size; parallel nodes are sized from `TOPDOWN_HIERARCHICAL_NODE_WIDTH` / `_ASPECT_RATIO` plus
padding instead. `predictedGraphSize` is therefore left unset here (it is still available as
`TopdownpackingLayoutProvider.predictedGraphSize`, and `providerWithPrediction` is the Java
behaviour). -/
def provider : LayoutProvider :=
  { id := TopdownpackingOptions.ALGORITHM_ID
    layout := layout }

/-- Java behaviour: the provider additionally exposes `getPredictedGraphSize`
(`ITopdownLayoutProvider`) to the top-down layout of `RecursiveGraphLayoutEngine`. Not registered
(elk-rs does not expose it, see `provider`). -/
def providerWithPrediction : LayoutProvider :=
  { provider with predictedGraphSize := some predictedGraphSize }

end TopdownpackingLayoutProvider

end Elk.Alg.TopdownPacking
