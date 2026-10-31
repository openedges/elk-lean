import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Alg.Layered.Options.CycleBreakingStrategy
import Elk.Alg.Layered.P1Cycles.GroupModelOrderCalculator
/-!
# `org.eclipse.elk.alg.layered.p1cycles.ModelOrderCycleBreaker`

Port of elk-rs `p1cycles/model_order_cycle_breaker.rs`. Reverses every edge (from an output port
of a layerless node) whose target has a smaller constraint (group) model order than its source.
One `GroupModelOrderCalculator` is created per source node and shared with its targets (so the
separate-node counters advance as in Rust). `bigOffset = offset * max(CB_NUM_MODEL_ORDER_GROUPS, 1)`.
-/
namespace Elk.Alg.Layered.P1Cycles

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace ModelOrderCycleBreaker

/-- `INTERMEDIATE_PROCESSING_CONFIGURATION`: `REVERSED_EDGE_RESTORER` after P5. -/
def intermediateProcessingConfiguration : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration).addAfter .p5EdgeRouting .reversedEdgeRestorer

/-- `process(layeredGraph, monitor)` body. -/
def run (graph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph graph
  if gr.internal.maxModelOrderNodesNull then throw (IO.userError maxModelOrderNodesNullError)
  let layerlessNodes := gr.layerlessNodes
  let offset : Int := max (layerlessNodes.size : Int) gr.internal.maxModelOrderNodes
  let modelOrderGroupCount : Int := max gr.internal.cbNumModelOrderGroups 1
  let bigOffset := offset * modelOrderGroupCount
  let enforceGroupModelOrder :=
    gr.props.getD LayeredOptions.GROUP_MODEL_ORDER_CB_GROUP_ORDER_STRATEGY .onlyWithinGroup == .enforced
  let compute (c : GroupModelOrderCalculator) (nd : LNode) : Int × GroupModelOrderCalculator :=
    if enforceGroupModelOrder then c.computeConstraintGroupModelOrder nd bigOffset offset
    else c.computeConstraintModelOrder nd offset
  let mut revEdges : Array LEdgeId := #[]
  for source in layerlessNodes do
    let (modelOrderSource, c) := compute GroupModelOrderCalculator.new (← getNode source)
    let mut calculator := c
    let outputPorts ← withArena (·.nodePortsByType source .output)
    for port in outputPorts do
      for edge in (← getPort port).outgoingEdges do
        let some targetPort := (← getEdge edge).target | continue
        let some target := (← getPort targetPort).owner | continue
        let (modelOrderTarget, c) := compute calculator (← getNode target)
        calculator := c
        if modelOrderTarget < modelOrderSource then
          revEdges := revEdges.push edge
  for edge in revEdges do
    LGraphUtil.reverseEdge edge graph true
    modifyGraph graph fun g => { g with internal := { g.internal with cyclic := true } }

/-- The `ModelOrderCycleBreaker` phase. -/
def phase : LayeredPhase :=
  { name := "ModelOrderCycleBreaker"
    process := fun graph monitor => do
      let _ ← monitor.begin "Model order cycle breaking" 1.0
      run graph
      monitor.done
    getLayoutProcessorConfiguration := fun _ => pure (some intermediateProcessingConfiguration) }

end ModelOrderCycleBreaker

builtin_initialize registerModelOrderCycleBreaker : Unit ←
  LayeredPhases.registerPhase .p1CycleBreaking (ElkEnum.ordinal CycleBreakingStrategy.modelOrder)
    (pure ModelOrderCycleBreaker.phase)

end Elk.Alg.Layered.P1Cycles
