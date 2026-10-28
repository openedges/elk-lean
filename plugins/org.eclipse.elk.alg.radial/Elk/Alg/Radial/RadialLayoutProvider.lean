import Elk.Graph
import Elk.Alg.Common.NodeSpacing.NodeMicroLayout
import Elk.Core.Alg
import Elk.Core.Exceptions
import Elk.Core.LayoutProvider
import Elk.Core.Options
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.Radial.InternalProperties
import Elk.Alg.Radial.RadialLayoutPhases
import Elk.Alg.Radial.RadialUtil
import Elk.Alg.Radial.Options.RadialOptions
import Elk.Alg.Radial.Options.CompactionStrategy
import Elk.Alg.Radial.P1Position.EadesRadial
import Elk.Alg.Radial.P2Routing.StraightLineEdgeRouter
import Elk.Alg.Radial.Intermediate.IntermediateProcessorStrategy
/-!
# `org.eclipse.elk.alg.radial.RadialLayoutProvider`

Port of `radial_layout_provider.rs` (elk-rs): assembles the two phases (`EadesRadial`,
`StraightLineEdgeRouter`) and the intermediate processors selected by the options
(`OverlapRemoval` and `GraphSizeCalculation` always, `Compaction` if `COMPACTOR` is not `NONE`,
`Rotation` if `ROTATE`, `OutgoingEdgeAngles` after the routing if `ROTATION_OUTGOING_EDGE_ANGLES`),
runs the node micro layout (unless `OMIT_NODE_MICRO_LAYOUT`), finds the root of the tree and
the initial radius (`RADIUS`, or the largest node diagonal if zero) and runs the processors.

The phase factory half of the Rust `RadialLayoutPhases` (`create_phase`) is
`RadialLayoutPhases.phaseFactory` here, because the phases refer to the enumeration.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0

namespace Elk.Alg.Radial

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Common.NodeSpacing
open Elk.Alg.Radial.Options Elk.Alg.Radial.P1Position Elk.Alg.Radial.P2Routing Elk.Alg.Radial.Intermediate

/-- `ILayoutPhase<RadialLayoutPhases, ElkNode>`. -/
abbrev RadialPhase := LayoutPhase RadialM RadialLayoutPhases NodeId IntermediateProcessorStrategy
/-- `ILayoutPhaseFactory<RadialLayoutPhases, ElkNode>`. -/
abbrev RadialPhaseFactory := LayoutPhaseFactory RadialM RadialLayoutPhases NodeId IntermediateProcessorStrategy

namespace RadialLayoutPhases

/-- `RadialLayoutPhases::create_phase()` as an `ILayoutPhaseFactory`. -/
def phaseFactory (p : RadialLayoutPhases) : RadialPhaseFactory :=
  LayoutPhaseFactory.ofEnum "RadialLayoutPhases" p
    (match p with
      | .p1NodePlacement => pure EadesRadial.phase
      | .p2EdgeRouting => pure StraightLineEdgeRouter.phase)

end RadialLayoutPhases

namespace RadialLayoutProvider

/-- `assemble_algorithm(layout_graph)`: the processor list for the options of the graph. -/
def assembleAlgorithm (layoutGraph : NodeId) : RadialM (Array (LayoutProcessor RadialM NodeId)) := do
  let assembler : AlgorithmAssembler RadialM RadialLayoutPhases NodeId IntermediateProcessorStrategy ←
    AlgorithmAssembler.create IntermediateProcessorStrategy.create
  assembler.setPhase .p1NodePlacement (RadialLayoutPhases.phaseFactory .p1NodePlacement)
  assembler.setPhase .p2EdgeRouting (RadialLayoutPhases.phaseFactory .p2EdgeRouting)
  let props := (← ElkM.getNode layoutGraph).props
  let mut configuration : LayoutProcessorConfiguration RadialLayoutPhases IntermediateProcessorStrategy :=
    LayoutProcessorConfiguration.create
  configuration := configuration.addBefore .p2EdgeRouting .overlapRemoval
  if props.getD RadialOptions.COMPACTOR CompactionStrategy.none != CompactionStrategy.none then
    configuration := configuration.addBefore .p2EdgeRouting .compaction
  if props.getD RadialOptions.ROTATE false then
    configuration := configuration.addBefore .p2EdgeRouting .rotation
  configuration := configuration.addBefore .p2EdgeRouting .graphSizeCalculation
  if props.getD RadialOptions.ROTATION_OUTGOING_EDGE_ANGLES false then
    configuration := configuration.addAfter .p2EdgeRouting .outgoingEdgeAngles
  assembler.addProcessorConfiguration configuration
  assembler.build layoutGraph

/-- `layout(layout_graph, progress_monitor)`. -/
def layout (layoutGraph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let run : RadialM Unit := do
    let algorithm ← assembleAlgorithm layoutGraph
    let _ ← monitor.begin "Radial layout" algorithm.size.toFloat
    if !((← ElkM.getNode layoutGraph).props.getD RadialOptions.OMIT_NODE_MICRO_LAYOUT false) then
      (← NodeMicroLayout.forGraph layoutGraph).execute
    let some root ← RadialUtil.findRoot layoutGraph
      | throwUnsupportedConfiguration "The given graph is not a tree!"
    InternalProperties.setRootNode layoutGraph root
    let mut layoutRadius := ((← ElkM.getNode layoutGraph).props.get RadialOptions.RADIUS).getD fl0p0
    if layoutRadius == fl0p0 then
      layoutRadius ← RadialUtil.findLargestNodeInGraph layoutGraph
    ElkM.setNodeProp layoutGraph RadialOptions.RADIUS layoutRadius
    let mut index := 0
    for processor in algorithm do
      if ← monitor.isCanceled then return
      if ← monitor.isLoggingEnabled then monitor.logGraph s!"{index}-Before processor"
      let sub ← monitor.subTask fl1p0
      processor.process layoutGraph sub
      index := index + 1
    if ← monitor.isLoggingEnabled then monitor.logGraph s!"{algorithm.size}-Finished"
    monitor.done
  StateRefT'.run' run {}

/-- The `org.eclipse.elk.radial` layout provider. -/
def provider : LayoutProvider :=
  { id := RadialOptions.ALGORITHM_ID
    layout := layout }

end RadialLayoutProvider

end Elk.Alg.Radial
