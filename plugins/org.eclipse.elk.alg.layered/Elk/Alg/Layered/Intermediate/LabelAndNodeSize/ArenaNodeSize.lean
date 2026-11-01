import Elk.Alg.Layered.Graph.Transform.LGraphAdapters
import Elk.Alg.Common.NodeSpacing.NodeDimensionCalculation
import Elk.Core.Util.FastFloat
/-!
# `LabelAndNodeSizeProcessor` — arena fast path of the node size calculation (FIX)

Java's `LabelAndNodeSizeProcessor` runs `NodeDimensionCalculation.calculateLabelAndNodeSizes` on
`LGraphAdapters.adapt(graph, true, true, NORMAL)`: for every adapted node the full cell system
pipeline `NodeLabelAndSizeCalculator.process(graph, node, true, false)`. The generic Lean pipeline
(`NodeDimensionCalculation.calculateLabelAndNodeSizesJava`) goes through the adapter record: every
size, position, option map, label list and port side is a closure call into `LayeredM`, and every
option read that misses calls the adapter's `defaultOverride` closure. This module is the same
pipeline with the adapter reads of the preparatory steps done on the arena (the PLAN 7.1 item 37
idea for `LGraph`):

* `trivialNodeSize?`, `NodeContext.new` and `PortContextCreator.createPortContexts` read the
  `LNode`/`LPort`/`LLabel` directly and use the shared pure builders (`NodeContext.build`,
  `PortContextCreator.addPortContextFrom`) with the LGraph adapters' constant `defaultOverride`
  (`fun _ => none`: `LGraphAdapters` overrides no default);
* the size and the port positions are written with `modifyNode`/`modifyPort` (the adapter's
  `setSize`/`setPosition`);
* phases 1–7 (`NodeLabelAndSizeCalculator.runPhases`) and the rarely needed adapter reads
  (incident edges of outside next-to-port labels, `getGraph` of comment nodes, node labels, label
  placement, `setNodePadding`) still go through the adapter.

The adapter's volatile ids are not written: `PortContextCreator` stores the id in the
`PortContext`, and only the ElkGraph path of `NodeDimensionCalculation` reads `getVolatileId` back
(the adapter family is local to `LabelAndNodeSizeProcessor.processWith`). The generic path stays
the reference (`LabelAndNodeSizeFlags.arenaFastPath := false`); the differential test
`layered.labelAndNodeSize.arenaFastPath` compares the arenas and the exceptions on random graphs.
-/

namespace Elk.Alg.Layered.Intermediate.LabelAndNodeSize

open Elk Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Util.Adapters
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Graph.Transform Elk.Alg.Common.NodeSpacing
open Elk.Alg.Common.NodeSpacing.Internal Elk.Alg.Common.NodeSpacing.Internal.Algorithm LayeredM

namespace ArenaNodeSize

/-- The `defaultOverride` of every `LGraphAdapters` element adapter (none is overridden). -/
@[inline] def noOverride (_ : PropKey) : Option PropValue := none

/-- `NodeLabelAndSizeCalculator.trivialNodeSize?` on the node itself: `some` its size when it has
no ports and no labels, effectively fixed size constraints and no `COMPUTE_PADDING` (after the
placement validation), else `none`. -/
def trivialNodeSize (nd : LNode) : LayeredM (Option KVector) := do
  if !nd.ports.isEmpty || !nd.labels.isEmpty then return none
  let props := nd.props
  let sizeConstraints := NodeContext.propertyDFrom noOverride props CoreOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
  if !NodeLabelAndSizeCalculator.hasEffectivelyFixedSizeConstraints sizeConstraints then return none
  if (NodeContext.propertyDFrom noOverride props CoreOptions.NODE_SIZE_OPTIONS EnumSet.empty).contains .computePadding then
    return none
  NodeContext.validatePlacements
    (NodeContext.propertyDFrom noOverride props CoreOptions.PORT_LABELS_PLACEMENT EnumSet.empty)
    (NodeContext.propertyDFrom noOverride props CoreOptions.NODE_LABELS_PLACEMENT EnumSet.empty)
  return some nd.size

/-- `PortContextCreator.createPortContexts(nodeContext, false)` on the arena: the ports in node
order (an `UNDEFINED` side throws the Java message), volatile ids `0, 1, …`, then the SOUTH and WEST
lists reversed. -/
def createPortContexts (a : LAdapters) (ctx : NodeContext LNodeId LPortId LLabelId) (ports : Array LPortId) :
    LayeredM (NodeContext LNodeId LPortId LLabelId) := do
  let imPortLabels := true
  let mut ctx := ctx
  let mut volatileId : Int := 0
  for port in ports do
    let ar ← get
    let pt := ar.port port
    let portSide := pt.side
    if portSide == .undefined then
      throwIllegalArgument
        "Label and node size calculator can only be used with ports that have port sides assigned."
    let labels := pt.labels
    let labelSizes := labels.map fun l => (ar.label l).size
    let labelPositions := labels.map fun l => (ar.label l).position
    let hasCompoundConnections := pt.internal.insideConnections
    let labelsNextToPort ← PortContextCreator.computeLabelsNextToPort a ctx port hasCompoundConnections
    ctx := PortContextCreator.addPortContextFrom noOverride ctx port portSide volatileId imPortLabels pt.size
      pt.position pt.props hasCompoundConnections labels labelSizes labelPositions labelsNextToPort
      pt.internal.portRatioOrPosition
    volatileId := volatileId + 1
  ctx := ctx.modifyPortContextsOf .south (·.reverse)
  ctx := ctx.modifyPortContextsOf .west (·.reverse)
  return ctx

/-- `NodeLabelAndSizeCalculator.applyPortPositions` on the arena: the port contexts in volatile id
order zipped with the node's ports. -/
def applyPortPositions (ctx : NodeContext LNodeId LPortId LLabelId) : LayeredM Unit := do
  let allPortContexts := ctx.allPortContexts
  let order := NodeLabelAndSizeCalculator.volatileIdOrder allPortContexts
  let ports := (← getNode ctx.node).ports
  for k in [0:min ports.size order.size] do
    if h : k < ports.size then
      if let some pc := allPortContexts[order.getD k 0]? then
        let pos := pc.portPosition
        modifyPort ports[k] fun pt => { pt with position := pos }

/-- `NodeLabelAndSizeCalculator.process(graph, node, true, false)` (`processWithOptions` with
`applyStuff`) with the arena reads described in the module doc. -/
def processNode (a : LAdapters) (node : LNodeId) (layoutDirection : Direction) : LayeredM KVector := do
  let nd ← getNode node
  -- nothing to lay out (`trivialNodeSize?`)
  if let some size ← trivialNodeSize nd then return size
  -- PREPARATORY PREPARATIONS: Create context objects (`NodeContext.new`, `createPortContexts`)
  let graphProps ← match ← a.getGraph node with
    | some g => pure (some (← getGraph g).props)
    | none => pure none
  let ctx : NodeContext LNodeId LPortId LLabelId ←
    NodeContext.build noOverride noOverride node nd.size nd.props nd.internal.compoundNode graphProps
  let ctx ← createPortContexts a ctx nd.ports
  -- PHASES 1–7
  let ctx ← NodeLabelAndSizeCalculator.runPhases a ctx layoutDirection true
  -- applyStuff
  let size := ctx.nodeSize
  modifyNode node fun x => { x with size := size }
  applyPortPositions ctx
  return size

/-- `NodeDimensionCalculation.calculateLabelAndNodeSizesJava(adapter)` with `processNode`: every
adapted node in `getNodes()` order, layout direction = the graph's `DIRECTION`. -/
def calculateLabelAndNodeSizes (a : LAdapters) (graph : LGraphId) : LayeredM Unit := do
  let layoutDirection ← a.graph.getPropertyD graph CoreOptions.DIRECTION Direction.undefined
  for node in ← a.getNodes graph do
    let _ ← processNode a node layoutDirection

end ArenaNodeSize

end Elk.Alg.Layered.Intermediate.LabelAndNodeSize
