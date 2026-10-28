import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options
/-!
# `org.eclipse.elk.alg.layered.p4nodes.SimpleNodePlacer` (elk-rs `p4nodes/simple_node_placer.rs`)

Node placement that centres the nodes of each layer vertically: every layer is stacked
top-down (margins plus the vertical spacing between consecutive nodes) and then shifted by
half of the difference to the highest layer.

The Rust port copies the graph into an `ArenaSync` snapshot; here the arena is read and
written directly (`PORTING.md` §15.1): layers in `graph.layers` order, nodes in
`layer.nodes` order. The layer heights are written to `Layer.size.y` (Rust
`sync_layer_sizes_to_graph`), node positions to `LNode.position.y`.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.Layered.P4Nodes

open Elk.Graph Elk.Core.Alg Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
open Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace SimpleNodePlacer

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

/-- `Spacings.getVerticalSpacing(n1, n2)` for two arena nodes. -/
private def verticalSpacing (spacings : Spacings) (n1 n2 : LNodeId) : LayeredM Float := do
  let a ← getNode n1
  let b ← getNode n2
  spacings.getVerticalSpacing a.type a.props b.type b.props

/-- `process(graph, monitor)` (Rust `SimpleNodePlacer::process`). First pass: the height of
every layer (`layer.size.y`) and the maximum height; second pass: node y positions, each
layer centred in the maximum height. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Simple node placement" fl1p0
  let some spacings := (← getGraph graph).internal.spacings
    | throw (IO.userError "java.lang.IllegalStateException: Missing spacings configuration for simple node placement")
  let layerIds := (← getGraph graph).layers
  let mut maxHeight := fl0p0
  -- first pass: compute layer heights
  for layer in layerIds do
    let nodeIds := (← getLayer layer).nodes
    let mut layerHeight := fl0p0
    let mut lastNode : Option LNodeId := none
    for n in nodeIds do
      if let some prev := lastNode then
        layerHeight := layerHeight + (← verticalSpacing spacings n prev)
      let nd ← getNode n
      layerHeight := layerHeight + (nd.margin.top + nd.size.y + nd.margin.bottom)
      lastNode := some n
    modifyLayer layer fun l => { l with size := { l.size with y := layerHeight } }
    if layerHeight > maxHeight then
      maxHeight := layerHeight
  -- second pass: set node y positions
  for layer in layerIds do
    let layerHeight := (← getLayer layer).size.y
    let nodeIds := (← getLayer layer).nodes
    let mut pos := (maxHeight - layerHeight) / fl2p0
    let mut lastNode : Option LNodeId := none
    for n in nodeIds do
      if let some prev := lastNode then
        pos := pos + (← verticalSpacing spacings n prev)
      let nd ← getNode n
      pos := pos + nd.margin.top
      let y := pos
      modifyNode n fun x => { x with position := { x.position with y := y } }
      pos := pos + (nd.size.y + nd.margin.bottom)
      lastNode := some n
  monitor.done

/-- The `SimpleNodePlacer` phase. -/
def phase : LayeredPhase :=
  { name := "SimpleNodePlacer"
    process := process
    getLayoutProcessorConfiguration := getLayoutProcessorConfiguration }

end SimpleNodePlacer

/-- Registers `NodePlacementStrategy.SIMPLE` → `SimpleNodePlacer`. -/
builtin_initialize registerSimpleNodePlacer : Unit ←
  LayeredPhases.registerPhase .p4NodePlacement (ElkEnum.ordinal NodePlacementStrategy.simple) (pure SimpleNodePlacer.phase)

end Elk.Alg.Layered.P4Nodes
