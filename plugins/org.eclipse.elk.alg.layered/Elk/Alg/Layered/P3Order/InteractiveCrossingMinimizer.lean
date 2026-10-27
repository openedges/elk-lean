import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options
import Elk.Alg.Layered.P3Order.NodeRelativePortDistributor
import Elk.Alg.Layered.P3Order.Counting.IInitializable
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
import Elk.Core.Util.RustSort
/-!
# `org.eclipse.elk.alg.layered.p3order.InteractiveCrossingMinimizer` (elk-rs `interactive_crossing_minimizer.rs`)

A crossing minimizer that allows user interaction by respecting previous node positions: every
layer is sorted by a vertical position computed per node (long edge dummies interpolate the
bend points of the edge they stem from, north/south dummies use the north or south side of
their origin node, everything else the node's reference point), ties are broken by the
`IN_LAYER_SUCCESSOR_CONSTRAINTS`. After each layer the ports are distributed by a
`NodeRelativePortDistributor` (forward sweep, no random numbers are drawn).

Deviations of the Rust port from Java (followed here): the long edge position interpolates the
edge's *current* bend points (`bendPoints`), not `ORIGINAL_BENDPOINTS`; a long edge dummy whose
`ORIGIN` is no edge, or whose edge has fewer than two points, and a north/south dummy whose
origin port cannot be resolved or lies on an east/west side fall back to the reference point
(Java throws or falls out of the switch); a zero x distance between the two interpolation
points yields the second point's y (`|dx| <= f64::EPSILON`). The distributor receives the node
order captured *before* sorting (`toNodeArray()` copies the layers), exactly like Rust and Java.

Orders reproduced: layers in `graph.layers` order, ports numbered in the pre-sort node order,
the layer sort is Rust `sort_by` (`rustSortBy`; Java `Collections.sort`).
-/
namespace Elk.Alg.Layered.P3Order

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Options Elk.Core.Alg Elk.Core.Util
open Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate
open Elk.Alg.Layered.P3Order.Counting LayeredM

namespace InteractiveCrossingMinimizer

/-- `INTERMEDIATE_PROCESSING_CONFIGURATION`: `LONG_EDGE_SPLITTER` before P3,
`IN_LAYER_CONSTRAINT_PROCESSOR` before P4, `LONG_EDGE_JOINER` after P5. -/
def intermediateProcessingConfiguration : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p3NodeOrdering .longEdgeSplitter
    |>.addBefore .p4NodePlacement .inLayerConstraintProcessor
    |>.addAfter .p5EdgeRouting .longEdgeJoiner

/-- `getLayoutProcessorConfiguration(graph)`: the intermediate configuration plus
`PORT_LIST_SORTER` before P3 when the graph has `NON_FREE_PORTS`. -/
def getLayoutProcessorConfiguration (graph : LGraphId) : LayeredM (Option LayeredProcessorConfiguration) := do
  let mut configuration := LayoutProcessorConfiguration.createFrom intermediateProcessingConfiguration
  if (← getGraph graph).internal.graphProperties.contains .nonFreePorts then
    configuration := configuration.addBefore .p3NodeOrdering .portListSorter
  return some configuration

/-- Rust `f64::EPSILON`. -/
def EPSILON : Float := 2.220446049250313e-16

/-- Rust `long_edge_position(node, horiz_pos)`: the y coordinate at `horizPos` of the polyline
formed by the source anchor, the edge's bend points (reversed for reversed edges) and the target
anchor; `none` where Rust returns `None`. -/
def longEdgePosition (node : LNodeId) (horizPos : Float) : LayeredM (Option Float) := do
  let nd ← getNode node
  let some (.lEdge edge) := nd.internal.origin | return none
  let ed ← getEdge edge
  let mut bendPoints : KVectorChain := ed.bendPoints
  if ed.internal.reversed then
    bendPoints := KVectorChain.reverse bendPoints
  if let some sourcePort := nd.internal.longEdgeSource then
    let anchor ← withArena (·.portAbsoluteAnchor sourcePort)
    if let some sourcePoint := anchor then
      if horizPos <= sourcePoint.x then
        return some sourcePoint.y
      bendPoints := bendPoints.insertIdx! 0 sourcePoint
  if let some targetPort := nd.internal.longEdgeTarget then
    let anchor ← withArena (·.portAbsoluteAnchor targetPort)
    if let some targetPoint := anchor then
      if targetPoint.x <= horizPos then
        return some targetPoint.y
      bendPoints := bendPoints.push targetPoint
  if bendPoints.size < 2 then
    return none
  let mut point1 := bendPoints[0]!
  let mut point2 := bendPoints[1]!
  for i in [2:bendPoints.size] do
    if point2.x >= horizPos then
      break
    point1 := point2
    point2 := bendPoints[i]!
  let deltaX := point2.x - point1.x
  if deltaX.abs <= EPSILON then
    return some point2.y
  return some (point1.y + (horizPos - point1.x) / deltaX * (point2.y - point1.y))

/-- Rust `north_south_port_position(node)`: the north (south) side of the node the dummy's first
port stems from; `none` for other sides or unresolved origins. -/
def northSouthPortPosition (node : LNodeId) : LayeredM (Option Float) := do
  let some dummyPort := (← getNode node).ports[0]? | return none
  let some (.lPort originPort) := (← getPort dummyPort).internal.origin | return none
  let originPortData ← getPort originPort
  let some originNode := originPortData.owner | return none
  let originNodeData ← getNode originNode
  match originPortData.side with
  | .north => return some originNodeData.position.y
  | .south => return some (originNodeData.position.y + originNodeData.size.y)
  | _ => return none

/-- `getPos(node, horizPos)` (Rust `get_pos`): the vertical position used for sorting. -/
def getPos (node : LNodeId) (horizPos : Float) (reference : InteractiveReferencePoint) : LayeredM Float := do
  let nodeType := (← getNode node).type
  let special ← match nodeType with
    | .longEdge => longEdgePosition node horizPos
    | .northSouthPort => northSouthPortPosition node
    | _ => pure none
  if let some position := special then
    return position
  let nd ← getNode node
  return match reference with
    | .center => nd.position.y + nd.size.y / 2.0
    | .topLeft => nd.position.y

/-- A layer node with its sort position and its `IN_LAYER_SUCCESSOR_CONSTRAINTS` (snapshotted
so the comparator is pure). -/
structure SortEntry where
  node : LNodeId
  pos : Float
  successors : Array LNodeId
  deriving Inhabited

/-- Rust `compare_nodes_by_pos`: by position (`partial_cmp`, NaN equal), then the successor
constraint of the first node (`Less`), then of the second node (`Greater`). -/
def compareEntries (a b : SortEntry) : Ordering :=
  match Float.comparePartial a.pos b.pos with
  | .eq =>
    if a.successors.contains b.node then .lt
    else if b.successors.contains a.node then .gt
    else .eq
  | c => c

/-- `process(layeredGraph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Interactive crossing minimization" 1.0
  let layers := (← getGraph graph).layers
  -- layer ids index into arrays of the port distribution code
  for h : layerIndex in [0:layers.size] do
    let id : Int := layerIndex
    modifyLayer layers[layerIndex] fun l => { l with id := id }
  let nodeOrder ← withArena (·.graphToNodeArray graph)
  let reference ← getGraphPropD graph LayeredOptions.INTERACTIVE_REFERENCE_POINT .center
  let portDistributor ← NodeRelativePortDistributor.new nodeOrder.size
  Initializable.init #[portDistributor.initializable] nodeOrder
  let mut portCount : Int := 0
  for h : layerIndex in [0:layers.size] do
    let layer := layers[layerIndex]
    let layerNodes := (← getLayer layer).nodes
    -- a horizontal position for the bend point comparison
    let mut horizPos : Float := 0.0
    let mut positionedNodes : Nat := 0
    for node in layerNodes do
      let nd ← getNode node
      if nd.position.x > 0.0 then
        horizPos := horizPos + (nd.position.x + nd.size.x / 2.0)
        positionedNodes := positionedNodes + 1
      for port in nd.ports do
        modifyPort port fun p => { p with id := portCount }
        portCount := portCount + 1
    if positionedNodes > 0 then
      horizPos := horizPos / positionedNodes.toFloat
    -- the vertical positions
    let mut entries : Array SortEntry := Array.mkEmpty layerNodes.size
    for h2 : nodeIndex in [0:layerNodes.size] do
      let node := layerNodes[nodeIndex]
      let pos ← getPos node horizPos reference
      let id : Int := nodeIndex
      -- long edge dummies keep their position for the interactive node placer
      modifyNode node fun x => { x with
        id := id
        internal := if x.type == .longEdge then { x.internal with originalDummyNodePosition := some pos } else x.internal }
      let successors := (← getNode node).internal.inLayerSuccessorConstraints
      entries := entries.push { node := node, pos := pos, successors := successors }
    -- sort the nodes by position
    -- Rust `sort_by(compare_nodes_by_pos)`: successor constraints can make the comparator
    -- intransitive, so Rust's exact algorithm decides the result
    let sorted ← match Elk.Core.Util.rustSortBy entries compareEntries with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"java.lang.IllegalArgumentException: {e}")
    modifyLayer layer fun l => { l with nodes := sorted.map (·.node) }
    let _ ← portDistributor.distributePortsWhileSweeping nodeOrder layerIndex true
  monitor.done

/-- The `InteractiveCrossingMinimizer` phase. -/
def phase : LayeredPhase :=
  { name := "InteractiveCrossingMinimizer"
    process := process
    getLayoutProcessorConfiguration := getLayoutProcessorConfiguration }

end InteractiveCrossingMinimizer

/-- Registers `CrossingMinimizationStrategy.INTERACTIVE` → `InteractiveCrossingMinimizer`. -/
builtin_initialize registerInteractiveCrossingMinimizer : Unit ←
  LayeredPhases.registerPhase .p3NodeOrdering (ElkEnum.ordinal CrossingMinimizationStrategy.interactive)
    (pure InteractiveCrossingMinimizer.phase)

end Elk.Alg.Layered.P3Order
