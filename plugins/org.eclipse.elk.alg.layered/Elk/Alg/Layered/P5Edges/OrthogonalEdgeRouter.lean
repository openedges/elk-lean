import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Alg.Layered.Options.GraphProperties
import Elk.Alg.Layered.P5Edges.Orthogonal
import Elk.Alg.Layered.P5Edges.PolylineEdgeRouter
import Elk.Core.Options
import Elk.Core.Util.ElkTrace
/-!
# `org.eclipse.elk.alg.layered.p5edges.OrthogonalEdgeRouter`

Port of elk-rs `p5edges/orthogonal_edge_router.rs`. Walks the layers left to right; for every pair of
consecutive layers (plus the virtual empty layers before the first and after the last) it places the
left layer at the current `x` (`LGraphUtil.placeNodesHorizontally`), routes the edges between the two
layers with a west-to-east `OrthogonalRoutingGenerator` starting `SPACING_EDGE_NODE_BETWEEN_LAYERS`
right of the left layer, and advances `x` by the width the routing slots need (at least
`SPACING_NODE_NODE_BETWEEN_LAYERS` between two non-external layers). The final `x` is the graph width.

Java accumulates `xpos`, `startPos` and `routingWidth` in `float`; Rust rounds through `f32` after every
step (`Float.toF32` here). The `ArenaSync` snapshot Rust takes at the start is the `ArenaScope` passed to
every `routeEdges` call (the generator only reads `y` anchors from it, see
`WestToEastRoutingStrategy`).
-/
namespace Elk.Alg.Layered.P5Edges

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate Elk.Alg.Layered.P5Edges.Orthogonal
  Elk.Alg.Layered.P5Edges.Orthogonal.Direction LayeredM

namespace OrthogonalEdgeRouter

/-- elk-rs `DISABLE_NS` (`ELK_DISABLE_NS` set): debug switch that suppresses the north/south port
processors. -/
builtin_initialize disableNs : Bool ← do return (← IO.getEnv "ELK_DISABLE_NS").isSome

/-- `HYPEREDGE_PROCESSING_ADDITIONS`. -/
def HYPEREDGE_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration).addBefore .p4NodePlacement .hyperedgeDummyMerger

/-- `INVERTED_PORT_PROCESSING_ADDITIONS`. -/
def INVERTED_PORT_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration).addBefore .p3NodeOrdering .invertedPortProcessor

/-- `NORTH_SOUTH_PORT_PROCESSING_ADDITIONS`. -/
def NORTH_SOUTH_PORT_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p3NodeOrdering .northSouthPortPreprocessor
    |>.addAfter .p5EdgeRouting .northSouthPortPostprocessor

/-- `HIERARCHICAL_PORT_PROCESSING_ADDITIONS`. -/
def HIERARCHICAL_PORT_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p3NodeOrdering .hierarchicalPortConstraintProcessor
    |>.addBefore .p4NodePlacement .hierarchicalPortDummySizeProcessor
    |>.addAfter .p5EdgeRouting .hierarchicalPortOrthogonalEdgeRouter

/-- `SELF_LOOP_PROCESSING_ADDITIONS`. -/
def SELF_LOOP_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p1CycleBreaking .selfLoopPreprocessor
    |>.addAfter .p5EdgeRouting .selfLoopPostprocessor
    |>.addBefore .p4NodePlacement .selfLoopPortRestorer
    |>.addBefore .p4NodePlacement .selfLoopRouter

/-- `HYPERNODE_PROCESSING_ADDITIONS`. -/
def HYPERNODE_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration).addAfter .p5EdgeRouting .hypernodeProcessor

/-- `CENTER_EDGE_LABEL_PROCESSING_ADDITIONS`. -/
def CENTER_EDGE_LABEL_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p2Layering .labelDummyInserter
    |>.addBefore .p4NodePlacement .labelDummySwitcher
    |>.addBefore .p4NodePlacement .labelSideSelector
    |>.addAfter .p5EdgeRouting .labelDummyRemover

/-- `END_EDGE_LABEL_PROCESSING_ADDITIONS`. -/
def END_EDGE_LABEL_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p4NodePlacement .labelSideSelector
    |>.addBefore .p4NodePlacement .endLabelPreprocessor
    |>.addAfter .p5EdgeRouting .endLabelPostprocessor

/-- `getLayoutProcessorConfiguration(graph)`: the additions selected by the graph properties (and the
`FEEDBACK_EDGES` option). -/
def getLayoutProcessorConfiguration (graph : LGraphId) : LayeredM (Option LayeredProcessorConfiguration) := do
  let gr ← getGraph graph
  let graphProperties := gr.internal.graphProperties
  let mut configuration : LayeredProcessorConfiguration := LayoutProcessorConfiguration.create
  if graphProperties.contains .hyperedges then
    configuration := configuration.addAll HYPEREDGE_PROCESSING_ADDITIONS
    configuration := configuration.addAll INVERTED_PORT_PROCESSING_ADDITIONS
  if graphProperties.contains .nonFreePorts || gr.props.getD LayeredOptions.FEEDBACK_EDGES false then
    configuration := configuration.addAll INVERTED_PORT_PROCESSING_ADDITIONS
    if graphProperties.contains .northSouthPorts && !disableNs then
      configuration := configuration.addAll NORTH_SOUTH_PORT_PROCESSING_ADDITIONS
  if graphProperties.contains .externalPorts then
    configuration := configuration.addAll HIERARCHICAL_PORT_PROCESSING_ADDITIONS
  if graphProperties.contains .selfLoops then
    configuration := configuration.addAll SELF_LOOP_PROCESSING_ADDITIONS
  if graphProperties.contains .hypernodes then
    configuration := configuration.addAll HYPERNODE_PROCESSING_ADDITIONS
  if graphProperties.contains .centerLabels then
    configuration := configuration.addAll CENTER_EDGE_LABEL_PROCESSING_ADDITIONS
  if graphProperties.contains .endLabels then
    configuration := configuration.addAll END_EDGE_LABEL_PROCESSING_ADDITIONS
  return some configuration

/-- Whether every node of an optional layer is a west/east external port dummy (`true` for `None`). -/
private def isLayerExternal (nodes : Option (Array LNodeId)) : LayeredM Bool := do
  match nodes with
  | some ns => ns.allM PolylineEdgeRouter.isExternalWestOrEastPort
  | none => return true

/-- `ELK_TRACE_COMPOUND_WIDTH` layer summary (Rust `{:?}` of the node types approximated by the Java names). -/
private def traceLayers (layers : Array LayerId) : LayeredM Unit := do
  if !ElkTrace.global.compoundWidth then return
  let mut info : Array String := #[]
  for i in [0:layers.size] do
    let nodes := (← getLayer layers[i]!).nodes
    let mut types : Array String := #[]
    for n in nodes do types := types.push (ElkEnum.javaName (← getNode n).type)
    info := info.push s!"L{i}[{nodes.size}]: {", ".intercalate types.toList}"
  IO.eprintln s!"[compound-width] edge_router layers={layers.size} detail: {" | ".intercalate info.toList}"

/-- `process(layeredGraph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Orthogonal edge routing" 1.0
  let gr ← getGraph graph
  let nodeNodeSpacing := (gr.props.get LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS).getD 0.0
  let edgeEdgeSpacing := (gr.props.get LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS).getD 0.0
  let edgeNodeSpacing := (gr.props.get LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS).getD 0.0
  let routingGenerator := OrthogonalRoutingGenerator.new .westToEast edgeEdgeSpacing (some "phase5")
  let scope ← withArena (ArenaScope.ofGraph · graph)
  let layers := gr.layers
  traceLayers layers
  let mut xpos : Float := 0.0
  let mut leftLayer : Option LayerId := none
  let mut leftLayerNodes : Option (Array LNodeId) := none
  let mut leftLayerIndex : Int := -1
  let mut layerIndex : Nat := 0
  while true do
    let rightLayer := layers[layerIndex]?
    let rightLayerNodes ← match rightLayer with
      | some l => pure (some (← getLayer l).nodes)
      | none => pure none
    let rightLayerIndex : Int := if rightLayer.isSome then (layerIndex : Int) else (layers.size : Int) - 1
    if let some l := leftLayer then
      LGraphUtil.placeNodesHorizontally l xpos
      let leftWidth := (← getLayer l).size.x
      xpos := Float.toF32 (xpos + leftWidth)
    -- Java: float startPos = leftLayer == null ? xpos : xpos + edgeNodeSpacing
    let startPos := if leftLayer.isNone then Float.toF32 xpos else Float.toF32 (xpos + edgeNodeSpacing)
    let slotsCount ← routingGenerator.routeEdges graph (leftLayerNodes.getD #[]) leftLayerIndex
      (rightLayerNodes.getD #[]) startPos (some scope)
    let isLeftLayerExternal ← isLayerExternal leftLayerNodes
    let isRightLayerExternal ← isLayerExternal rightLayerNodes
    if slotsCount > 0 then
      -- Java: float routingWidth
      let mut routingWidth :=
        Float.toF32 (Float.toF32 (Float.toF32 slotsCount.toFloat - 1.0) * Float.toF32 edgeEdgeSpacing)
      if leftLayer.isSome then routingWidth := Float.toF32 (routingWidth + Float.toF32 edgeNodeSpacing)
      if rightLayer.isSome then routingWidth := Float.toF32 (routingWidth + Float.toF32 edgeNodeSpacing)
      if routingWidth < nodeNodeSpacing && !isLeftLayerExternal && !isRightLayerExternal then
        routingWidth := nodeNodeSpacing
      xpos := Float.toF32 (xpos + routingWidth)
    else if !isLeftLayerExternal && !isRightLayerExternal then
      xpos := Float.toF32 (xpos + nodeNodeSpacing)
    if ElkTrace.global.compoundWidth then
      IO.eprintln (s!"[compound-width] edge_router: layer_index={layerIndex} xpos={Float.toRustDisplay xpos} " ++
        s!"slots={slotsCount} left_ext={isLeftLayerExternal} right_ext={isRightLayerExternal}")
    leftLayer := rightLayer
    leftLayerNodes := rightLayerNodes
    leftLayerIndex := rightLayerIndex
    if leftLayer.isNone then break
    layerIndex := layerIndex + 1
    if layerIndex > layers.size then break
  if ElkTrace.global.compoundWidth then
    IO.eprintln s!"[compound-width] edge_router: FINAL xpos={Float.toRustDisplay xpos} graph_size_x={Float.toRustDisplay (Float.toF32 xpos)}"
  let width := Float.toF32 xpos
  modifyGraph graph fun g => { g with size := { g.size with x := width } }
  monitor.done

/-- The phase (`new OrthogonalEdgeRouter()`). -/
def phase : LayeredPhase :=
  { name := "OrthogonalEdgeRouter"
    process := process
    getLayoutProcessorConfiguration := getLayoutProcessorConfiguration }

end OrthogonalEdgeRouter

builtin_initialize registerOrthogonalEdgeRouter : Unit ←
  LayeredPhases.registerPhase .p5EdgeRouting (ElkEnum.ordinal EdgeRouting.orthogonal) (pure OrthogonalEdgeRouter.phase)

end Elk.Alg.Layered.P5Edges
