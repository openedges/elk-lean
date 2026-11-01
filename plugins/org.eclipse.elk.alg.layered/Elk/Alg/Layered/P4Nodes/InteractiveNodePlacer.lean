import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.p4nodes.InteractiveNodePlacer` (elk-rs `p4nodes/interactive_node_placer.rs`)

Node placement for interactive layout: normal nodes keep their y coordinate, dummy nodes are
placed at `ORIGINAL_DUMMY_NODE_POSITION` (or right below the previous node), and overlaps are
removed top-down using the vertical spacing between the node types.

Arena access instead of the Rust `ArenaSync` snapshot (`PORTING.md` §15.1): layers in
`graph.layers` order, nodes in `layer.nodes` order.
-/

namespace Elk.Alg.Layered.P4Nodes

open Elk.Graph Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
open Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace InteractiveNodePlacer

/-- `HIERARCHY_PROCESSING_ADDITIONS`: the hierarchical port position processor before edge routing. -/
def HIERARCHY_PROCESSING_ADDITIONS : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p5EdgeRouting .hierarchicalPortPositionProcessor

/-- `getLayoutProcessorConfiguration(graph)`: the hierarchy additions if the graph has external ports. -/
def getLayoutProcessorConfiguration (graph : LGraphId) : LayeredM (Option LayeredProcessorConfiguration) := do
  if (← getGraph graph).internal.graphProperties.contains .externalPorts then
    return some (LayoutProcessorConfiguration.createFrom HIERARCHY_PROCESSING_ADDITIONS)
  else
    return none

/-- `placeNodes(nodes)` (Rust `place_nodes`): places the nodes of one layer top-down.
`minValidY` starts at `-∞`; a dummy without an original position is put right below the
previous node (clamped to `0`). -/
def placeNodes (nodeIds : Array LNodeId) (spacings : Spacings) : LayeredM Unit := do
  let mut minValidY := Float.negInf
  let mut prevNodeType := NodeType.normal
  for n in nodeIds do
    let nd ← getNode n
    let nodeType := nd.type
    let spacing ← spacings.getVerticalSpacingForTypes nodeType prevNodeType
    let mut posY := nd.position.y
    if nodeType != .normal then
      match nd.internal.originalDummyNodePosition with
      | some original => posY := original
      | none =>
        minValidY := fmax minValidY fl0p0
        posY := minValidY + spacing
    let marginTop := nd.margin.top
    let marginBottom := nd.margin.bottom
    let sizeY := nd.size.y
    if posY < minValidY + spacing + marginTop then
      posY := minValidY + spacing + marginTop
    let y := posY
    modifyNode n fun x => { x with position := { x.position with y := y } }
    minValidY := posY + sizeY + marginBottom
    prevNodeType := nodeType

/-- `process(graph, monitor)` (Rust `InteractiveNodePlacer::process`): `placeNodes` per layer. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Interactive node placement" 1.0
  let some spacings := (← getGraph graph).internal.spacings
    | throw (IO.userError "java.lang.IllegalStateException: Missing spacings configuration for interactive node placement")
  for layer in (← getGraph graph).layers do
    placeNodes (← getLayer layer).nodes spacings
  monitor.done

/-- The `InteractiveNodePlacer` phase. -/
def phase : LayeredPhase :=
  { name := "InteractiveNodePlacer"
    process := process
    getLayoutProcessorConfiguration := getLayoutProcessorConfiguration }

end InteractiveNodePlacer

/-- Registers `NodePlacementStrategy.INTERACTIVE` → `InteractiveNodePlacer`. -/
builtin_initialize registerInteractiveNodePlacer : Unit ←
  LayeredPhases.registerPhase .p4NodePlacement (ElkEnum.ordinal NodePlacementStrategy.interactive)
    (pure InteractiveNodePlacer.phase)

end Elk.Alg.Layered.P4Nodes
