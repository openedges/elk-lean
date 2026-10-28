import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options
import Elk.Alg.Layered.P3Order.NodeRelativePortDistributor
import Elk.Alg.Layered.P3Order.Counting.IInitializable
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
import Elk.Core.Util.JavaSort
import Std.Data.HashMap
/-!
# `org.eclipse.elk.alg.layered.p3order.InteractiveCrossingMinimizer` (elk-rs `interactive_crossing_minimizer.rs`)

A crossing minimizer that allows user interaction by respecting previous node positions: every
layer is sorted by a vertical position computed per node (long edge dummies interpolate the
bend points of the edge they stem from, north/south dummies use the north or south side of
their origin node, everything else the node's reference point), ties are broken by the
`IN_LAYER_SUCCESSOR_CONSTRAINTS`. After each layer the ports are distributed by a
`NodeRelativePortDistributor` (forward sweep, no random numbers are drawn).

Java semantics (elk-rs differs, see below): a long edge dummy interpolates the polyline of the
`ORIGINAL_BENDPOINTS` of its `ORIGIN` edge (the start point, bend points and end point of the
imported section, set by the importer only for the interactive strategies; reversed for a reversed
edge), extended by the absolute anchors of `LONG_EDGE_SOURCE` (in front) and `LONG_EDGE_TARGET` (at
the end). For an edge that is not reversed Java extends the stored chain object itself (`addFirst`/
`addLast` on the property value); the segments of a split long edge share that object
(`copyProperties`), so later dummies of the same edge see the points added before. This is
reproduced with the chains extended so far, by object identity, for the duration of `process`. The interpolation divides by the x distance of the two points without a guard
(`±Infinity`/`NaN` positions sort like `Double.compare`). The layer is sorted with JDK `TimSort`
(`javaSortBy`, Java `Collections.sort`) by `Double.compare` of the positions with the
`IN_LAYER_SUCCESSOR_CONSTRAINTS` tie-break — not a consistent order, so the comparison sequence
matters. The distributor receives the node order captured *before* sorting (`toNodeArray()` copies
the layers).

elk-rs interpolates the edge's current `bendPoints` (empty in P3) with an `f64::EPSILON` guard,
compares with `partial_cmp` and sorts with Rust's `sort_by`.

Unreachable Java crashes kept as fallbacks: a long edge dummy whose `ORIGIN` is no edge and a
north/south dummy without ports or without origin port use the reference point (Java throws a
`ClassCastException`/`NullPointerException`/`IndexOutOfBoundsException`; every dummy of these types
has them).
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

/-- The long edge position of `getPos(node, horizPos)`: the y coordinate at `horizPos` of the polyline
of the `ORIGIN` edge's `ORIGINAL_BENDPOINTS` (reversed copy for a reversed edge, else the stored
chain itself, which is extended in place like Java's) with the source anchor in front and the target
anchor at the end; `none` (reference point fallback) with fewer than two points or no edge origin. -/
def longEdgePosition (chains : IO.Ref (Std.HashMap Nat KVectorChain)) (node : LNodeId) (horizPos : Float) :
    LayeredM (Option Float) := do
  let nd ← getNode node
  let some (.lEdge edge) := nd.internal.origin | return none
  let ed ← getEdge edge
  -- `shared`: the identity of the property's chain object when Java mutates it (not reversed)
  let (bendPoints, shared) : KVectorChain × Option Nat ← match ed.internal.originalBendpoints with
    | none => pure (#[], none)
    | some (id, initial) => do
      let current := ((← chains.get).get? id).getD initial
      if ed.internal.reversed then pure (KVectorChain.reverse current, none) else pure (current, some id)
  let store (chain : KVectorChain) : LayeredM Unit := do
    if let some id := shared then chains.modify (·.insert id chain)
  let mut bendPoints := bendPoints
  if let some sourcePort := nd.internal.longEdgeSource then
    if let some sourcePoint ← withArena (·.portAbsoluteAnchor sourcePort) then
      if horizPos <= sourcePoint.x then
        return some sourcePoint.y
      bendPoints := bendPoints.insertIdx! 0 sourcePoint
      store bendPoints
  if let some targetPort := nd.internal.longEdgeTarget then
    if let some targetPoint ← withArena (·.portAbsoluteAnchor targetPort) then
      if targetPoint.x <= horizPos then
        return some targetPoint.y
      bendPoints := bendPoints.push targetPoint
      store bendPoints
  if bendPoints.size < 2 then
    return none
  let mut point1 := bendPoints[0]!
  let mut point2 := bendPoints[1]!
  let mut i := 2
  while point2.x < horizPos && i < bendPoints.size do
    point1 := point2
    point2 := bendPoints[i]!
    i := i + 1
  return some (point1.y + (horizPos - point1.x) / (point2.x - point1.x) * (point2.y - point1.y))

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

/-- `getPos(node, horizPos)`: the vertical position used for sorting (`chains`: the
`ORIGINAL_BENDPOINTS` objects extended so far). -/
def getPos (chains : IO.Ref (Std.HashMap Nat KVectorChain)) (node : LNodeId) (horizPos : Float)
    (reference : InteractiveReferencePoint) : LayeredM Float := do
  let nodeType := (← getNode node).type
  let special ← match nodeType with
    | .longEdge => longEdgePosition chains node horizPos
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

/-- The comparator of `process`: `Double.compare` of the positions, on equality the successor
constraint of the first node (`-1`), then of the second node (`1`). -/
def compareEntries (a b : SortEntry) : Ordering :=
  match Float.compareJava a.pos b.pos with
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
  let chains ← IO.mkRef ({} : Std.HashMap Nat KVectorChain)
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
      let pos ← getPos chains node horizPos reference
      let id : Int := nodeIndex
      -- long edge dummies keep their position for the interactive node placer
      modifyNode node fun x => { x with
        id := id
        internal := if x.type == .longEdge then { x.internal with originalDummyNodePosition := some pos } else x.internal }
      let successors := (← getNode node).internal.inLayerSuccessorConstraints
      entries := entries.push { node := node, pos := pos, successors := successors }
    -- sort the nodes by position: Java `Collections.sort` (TimSort); successor constraints make the
    -- comparator intransitive, so TimSort's comparison sequence decides the result
    let sorted ← match javaSortBy entries compareEntries with
      | .ok r => pure r
      | .error _ => throw (IO.userError JavaSort.contractViolationError)
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
