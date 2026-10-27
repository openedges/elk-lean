import Elk.Alg.Layered.GraphConfigurator
import Elk.Alg.Layered.TraceRecorder
import Elk.Core.Util.ElkUtil
/-!
# `org.eclipse.elk.alg.layered.ElkLayered`

The layered algorithm driver: configures the graph, splits it into connected components,
runs the processor list on every component (or, for compound layout, on all nested graphs
in the hierarchical round-robin order) and resizes the graph. The components processor and
the compound pre- and post-processors are injected (`ElkLayered.new`) so that this module does
not depend on their packages; processors are kept per graph instead of in `PROCESSORS`.
Phase-step traces are recorded after every root-graph processor (`TraceRecorder`).
-/
namespace Elk.Alg.Layered

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Alg
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

/-- `ElkLayered` with its collaborators. -/
structure ElkLayered where
  graphConfigurator : GraphConfigurator
  /-- `ComponentsProcessor.split(graph)`. -/
  splitComponents : LGraphId → LayeredM (Array LGraphId)
  /-- `ComponentsProcessor.combine(components, target)`. -/
  combineComponents : Array LGraphId → LGraphId → LayeredM Unit
  /-- `CompoundGraphPreprocessor`. -/
  compoundGraphPreprocessor : LayeredProcessor
  /-- `CompoundGraphPostprocessor`. -/
  compoundGraphPostprocessor : LayeredProcessor

/-- State of a white-box layout test run (`prepareLayoutTest` … `runLayoutTestStep`). -/
structure TestExecutionState where
  graphs : Array LGraphId
  processors : Array LayeredProcessor
  step : Nat := 0

namespace ElkLayered

/-- `new ElkLayered()` with the given collaborators. -/
def new (splitComponents : LGraphId → LayeredM (Array LGraphId)) (combineComponents : Array LGraphId → LGraphId → LayeredM Unit)
    (compoundGraphPreprocessor compoundGraphPostprocessor : LayeredProcessor) : IO ElkLayered := do
  return { graphConfigurator := ← GraphConfigurator.new, splitComponents, combineComponents,
           compoundGraphPreprocessor, compoundGraphPostprocessor }

/-- `runProcessorForGraph`: runs one processor and records the trace snapshot for root graphs. -/
def runProcessorForGraph (lgraph : LGraphId) (processor : LayeredProcessor) (monitor : ProgressMonitor) : LayeredM Unit := do
  processor.process lgraph monitor
  let a ← get
  if (a.graph lgraph).parentNode.isNone then
    TraceRecorder.recordSnapshotForRoot a lgraph processor.name

/-- `layoutComponent`: runs the processors of one component. -/
def layoutComponent (lgraph : LGraphId) (processors : Array LayeredProcessor) (monitor : ProgressMonitor) : LayeredM Unit := do
  if processors.isEmpty then return
  let monitorProgress := 1.0 / processors.size.toFloat
  for processor in processors do
    if ← monitor.isCanceled then return
    let subMonitor ← monitor.subTask monitorProgress
    runProcessorForGraph lgraph processor subMonitor

/-- `resizeGraphNoReally(lgraph, oldSize, newSize)`: content alignment offsets and external port dummies. -/
def resizeGraphNoReally (lgraph : LGraphId) (oldSize newSize : KVector) : LayeredM Unit := do
  let gr ← getGraph lgraph
  let contentAlignment := gr.props.getD CoreOptions.CONTENT_ALIGNMENT (EnumSet.empty : EnumSet ContentAlignment)
  let graphProperties := gr.internal.graphProperties
  if newSize.x > oldSize.x then
    if contentAlignment.contains .hCenter then
      modifyGraph lgraph fun g => { g with offset := { g.offset with x := g.offset.x + (newSize.x - oldSize.x) / 2.0 } }
    else if contentAlignment.contains .hRight then
      modifyGraph lgraph fun g => { g with offset := { g.offset with x := g.offset.x + (newSize.x - oldSize.x) } }
  if newSize.y > oldSize.y then
    if contentAlignment.contains .vCenter then
      modifyGraph lgraph fun g => { g with offset := { g.offset with y := g.offset.y + (newSize.y - oldSize.y) / 2.0 } }
    else if contentAlignment.contains .vBottom then
      modifyGraph lgraph fun g => { g with offset := { g.offset with y := g.offset.y + (newSize.y - oldSize.y) } }
  if graphProperties.contains .externalPorts && (newSize.x > oldSize.x || newSize.y > oldSize.y) then
    for n in gr.layerlessNodes do
      let nd ← getNode n
      if nd.type != .externalPort then continue
      match nd.internal.extPortSide with
      | .east => modifyNode n fun x => { x with position := { x.position with x := x.position.x + (newSize.x - oldSize.x) } }
      | .south => modifyNode n fun x => { x with position := { x.position with y := x.position.y + (newSize.y - oldSize.y) } }
      | _ => pure ()
  modifyGraph lgraph fun g => { g with size := ⟨newSize.x - g.padding.left - g.padding.right, newSize.y - g.padding.top - g.padding.bottom⟩ }

/-- `resizeGraph(lgraph)`: applies the minimum size constraint unless the graph size is fixed. -/
def resizeGraph (lgraph : LGraphId) : LayeredM Unit := do
  let gr ← getGraph lgraph
  let sizeConstraints := gr.props.getD CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.empty : EnumSet SizeConstraint)
  let sizeOptions := gr.props.getD CoreOptions.NODE_SIZE_OPTIONS (EnumSet.empty : EnumSet SizeOptions)
  let minSize0 := gr.props.getD CoreOptions.NODE_SIZE_MINIMUM ({} : KVector)
  let fixedGraphSize := gr.props.getD CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE false
  let calculatedSize := gr.actualSize
  let mut adjustedSize := calculatedSize
  if sizeConstraints.contains .minimumSize then
    let mut minSize := minSize0
    if sizeOptions.contains .defaultMinimumSize then
      if minSize.x <= 0.0 then minSize := { minSize with x := ElkUtil.DEFAULT_MIN_WIDTH }
      if minSize.y <= 0.0 then minSize := { minSize with y := ElkUtil.DEFAULT_MIN_HEIGHT }
    adjustedSize := ⟨fmax adjustedSize.x minSize.x, fmax adjustedSize.y minSize.y⟩
  if !fixedGraphSize then
    resizeGraphNoReally lgraph calculatedSize adjustedSize

/-- `collectAllGraphsBottomUp(root)`: nested graphs before their parents (Java stack order). -/
def collectAllGraphsBottomUp (root : LGraphId) : LayeredM (Array LGraphId) := do
  let mut collected : Array LGraphId := #[root]
  let mut stack : Array LGraphId := #[root]
  while !stack.isEmpty do
    let graph := stack.back!
    stack := stack.pop
    for n in (← getGraph graph).layerlessNodes do
      if let some nested := (← getNode n).nestedGraph then
        collected := #[nested] ++ collected
        stack := stack.push nested
  return collected

/-- `reviewAndCorrectHierarchicalProcessors(root, graphs)`: child graphs must use the root's
crossing minimization strategy; the hierarchical greedy switch type is inherited. -/
def reviewAndCorrectHierarchicalProcessors (root : LGraphId) (graphs : Array LGraphId) : LayeredM Unit := do
  let rootGraph ← getGraph root
  let rootCrossingMinimization := rootGraph.props.getD LayeredOptions.CROSSING_MINIMIZATION_STRATEGY CrossingMinimizationStrategy.layerSweep
  let rootGreedySwitchType := rootGraph.props.getD LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_HIERARCHICAL_TYPE GreedySwitchType.off
  for graph in graphs do
    let childCrossingMinimization := (← getGraph graph).props.getD LayeredOptions.CROSSING_MINIMIZATION_STRATEGY CrossingMinimizationStrategy.layerSweep
    if childCrossingMinimization != rootCrossingMinimization then
      throwUnsupportedConfiguration s!"The hierarchy aware processor {ElkEnum.javaName childCrossingMinimization} in a child graph is only allowed if the root graph uses the same processor."
    setGraphProp graph LayeredOptions.CROSSING_MINIMIZATION_GREEDY_SWITCH_HIERARCHICAL_TYPE rootGreedySwitchType

/-- `hierarchicalLayout(lgraph, monitor)`: runs the processors of all nested graphs in lock
step; hierarchy-aware processors run on the root graph only. -/
def hierarchicalLayout (e : ElkLayered) (lgraph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let graphs ← collectAllGraphsBottomUp lgraph
  reviewAndCorrectHierarchicalProcessors lgraph graphs
  let mut entries : Array (LGraphId × Array LayeredProcessor × Nat) := #[]
  let mut totalWork := 0.0
  for graph in graphs do
    let processors ← e.graphConfigurator.prepareGraphForLayout graph
    totalWork := totalWork + processors.size.toFloat
    entries := entries.push (graph, processors, 0)
  let _ ← monitor.begin "Recursive hierarchical layout" totalWork
  if entries.isEmpty then
    monitor.done
    return
  let mut rootIndex := entries.size - 1
  for h : i in [0:entries.size] do
    if (← getGraph entries[i].1).parentNode.isNone then
      rootIndex := i
      break
  while entries[rootIndex]!.2.2 < entries[rootIndex]!.2.1.size do
    for h : i in [0:entries.size] do
      let mut continueLoop := true
      while continueLoop && !(← monitor.isCanceled) do
        let (graph, processors, index) := entries[i]!
        if index >= processors.size then
          continueLoop := false
        else
          let processor := processors[index]!
          entries := entries.set! i (graph, processors, index + 1)
          let isRoot := (← getGraph graph).parentNode.isNone
          if !processor.isHierarchyAware then
            let subMonitor ← monitor.subTask 1.0
            runProcessorForGraph graph processor subMonitor
          else
            if isRoot then
              let subMonitor ← monitor.subTask 1.0
              runProcessorForGraph graph processor subMonitor
            continueLoop := false
      if ← monitor.isCanceled then return
  monitor.done

/-- Runs `x` inside a `TraceLayoutScope` (trace nesting depth). -/
private def withTraceScope {α : Type} (x : LayeredM α) : LayeredM α :=
  fun ref => TraceRecorder.withLayoutScope (x ref)

/-- `doLayout(lgraph, monitor)`. -/
def doLayoutWithMonitor (e : ElkLayered) (lgraph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Layered layout" 1.0
  withTraceScope (do
    let processors ← e.graphConfigurator.prepareGraphForLayout lgraph
    let components ← e.splitComponents lgraph
    if components.size == 1 then
      layoutComponent components[0]! processors monitor
    else
      let compWork := 1.0 / (max components.size 1).toFloat
      for component in components do
        if ← monitor.isCanceled then return
        let subMonitor ← monitor.subTask compWork
        layoutComponent component processors subMonitor
    e.combineComponents components lgraph
    resizeGraph lgraph
    monitor.done)

/-- `doLayout(lgraph, monitor)` with the default monitor (`BasicProgressMonitor` with 0 hierarchy levels). -/
def doLayout (e : ElkLayered) (lgraph : LGraphId) (monitor : Option ProgressMonitor := none) : LayeredM Unit := do
  let monitor ← match monitor with
    | some m => pure m
    | none => ProgressMonitor.basic (maxHierarchyLevels := 0)
  e.doLayoutWithMonitor lgraph monitor

/-- `doCompoundLayout(lgraph, monitor)`: compound pre-processing, hierarchical layout,
compound post-processing. -/
def doCompoundLayoutWithMonitor (e : ElkLayered) (lgraph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  withTraceScope (do
    let _ ← monitor.begin "Layered layout" 2.0
    let preMonitor ← monitor.subTask 1.0
    e.compoundGraphPreprocessor.process lgraph preMonitor
    TraceRecorder.recordSnapshotForRoot (← get) lgraph "CompoundGraphPreprocessor"
    let layoutMonitor ← monitor.subTask 1.0
    e.hierarchicalLayout lgraph layoutMonitor
    let postMonitor ← monitor.subTask 1.0
    e.compoundGraphPostprocessor.process lgraph postMonitor
    TraceRecorder.recordSnapshotForRoot (← get) lgraph "CompoundGraphPostprocessor"
    monitor.done)

/-- `doCompoundLayout` with the default monitor. -/
def doCompoundLayout (e : ElkLayered) (lgraph : LGraphId) (monitor : Option ProgressMonitor := none) : LayeredM Unit := do
  let monitor ← match monitor with
    | some m => pure m
    | none => ProgressMonitor.basic (maxHierarchyLevels := 0)
  e.doCompoundLayoutWithMonitor lgraph monitor

/-- `prepareLayoutTest(lgraph)`: configures the graph and splits it for a white-box test. -/
def prepareLayoutTest (e : ElkLayered) (lgraph : LGraphId) : LayeredM TestExecutionState := do
  let processors ← e.graphConfigurator.prepareGraphForLayout lgraph
  let graphs ← e.splitComponents lgraph
  return { graphs, processors }

/-- `isLayoutTestFinished(state)`. -/
def isLayoutTestFinished (state : TestExecutionState) : Bool := state.step >= state.processors.size

/-- `layoutTest(graphs, processor)`: runs a processor on all test graphs with a fresh monitor. -/
def layoutTest (graphs : Array LGraphId) (processor : LayeredProcessor) : LayeredM Unit := do
  for graph in graphs do
    let monitor ← ProgressMonitor.basic
    processor.process graph monitor

/-- `runLayoutTestUntil(processorClass, inclusive, state)`: runs processors up to the first
one named `processorName` (exclusive or inclusive). -/
def runLayoutTestUntil (state : TestExecutionState) (processorName : String) (inclusive : Bool) : LayeredM TestExecutionState := do
  let mut phaseIndex := state.step
  let mut found := false
  while phaseIndex < state.processors.size && !found do
    if state.processors[phaseIndex]!.name == processorName then
      found := true
      if inclusive then phaseIndex := phaseIndex + 1
    else phaseIndex := phaseIndex + 1
  let mut state := state
  while state.step < phaseIndex do
    if let some processor := state.processors[state.step]? then
      layoutTest state.graphs processor
    state := { state with step := state.step + 1 }
  return state

/-- `runLayoutTestStep(state)`: runs the next processor; throws when finished. -/
def runLayoutTestStep (state : TestExecutionState) : LayeredM TestExecutionState := do
  if isLayoutTestFinished state then
    throwIllegalState "Current layout test run has finished."
  if let some processor := state.processors[state.step]? then
    layoutTest state.graphs processor
  return { state with step := state.step + 1 }

/-- `getLayoutTestConfiguration(state)`. -/
def getLayoutTestConfiguration (state : TestExecutionState) : Array LayeredProcessor := state.processors

end ElkLayered

end Elk.Alg.Layered
