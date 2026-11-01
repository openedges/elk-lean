import Elk.Alg.Layered.Intermediate.Wrapping.BreakingPointInserter
import Elk.Alg.Layered.P5Edges.Splines.SplineEdgeRouter
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping.BreakingPointRemover`

Port of elk-rs `intermediate/breaking_point_remover.rs`. Locates the breaking point end dummies
whose info has no `next` and removes each chain (following `prev`) after transferring the routes
of the split edges to the original edge:

```
node --nodeStartEdge--> startMarker --startEndEdge--> endMarker --e--> node
```

* `SPLINES`: the spline segments (`SPLINE_ROUTE_START`) and edge chains (`SPLINE_EDGE_CHAIN`) are
  joined (`s1 ++ reverse(s2) ++ s3`; the segments of `s2` get `inverseOrder` in the graph's segment
  table) and stored on the original edge, which becomes its own `SPLINE_SURVIVING_EDGE`; both are
  removed from the two dummy edges; the original edge loses its bend points (Java; elk-rs left them).
  A `null` route on one of the three edges throws Java's `NullPointerException` of the first
  `addAll`/`forEach` that dereferences it.
* `POLYLINE`: `nodeStartEdge` bends, the start dummy position, the reversed `startEndEdge` bends,
  the end dummy position, the original bends.
* otherwise (orthogonal): as polyline without the two dummy positions.

The junction points of the three edges are concatenated (original, `startEndEdge`,
`nodeStartEdge`); since `JUNCTION_POINTS` has a default (empty chain) the Rust `is_some()` test is
always true, so the joined chain is always stored. The original edge gets the source of
`nodeStartEdge` back; the dummy edges are disconnected and the dummies removed from their layers.

Slots: after phase 5; after `LongEdgeJoiner`, before `HorizontalGraphCompactor`.

`SPLINE_ROUTE_START` is `LEdgeInternals.splineRouteStart` (ids into the processed graph's
`LGraphInternals.splineSegments`, Rust `SplineSegmentRef`s); the original edge always gets `some`
joined list.
-/
namespace Elk.Alg.Layered.Intermediate.Wrapping

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace BreakingPointRemover

/-- The `SPLINES` branch of `remove` (see the module doc): `graph` owns the segment table. -/
private def joinSplineRoutes (graph : LGraphId) (bp : BreakingPointInfo) : LayeredM Unit := do
  -- Java: `joinedSegments.addAll(s1)`, `s2.forEach(..)`, `joinedSegments.addAll(s3)` on a `null`
  -- route (an edge that is not the start edge of a spline chain); the edge chains are set together
  -- with the routes (`SplineEdgeRouter`), so they are `null` exactly when the routes are
  let some s1 := (← getEdge bp.nodeStartEdge).internal.splineRouteStart
    | throwNullPointer "Cannot invoke \"java.util.Collection.toArray()\" because \"c\" is null"
  let some s2 := (← getEdge bp.startEndEdge).internal.splineRouteStart
    | throwNullPointer
        "Cannot invoke \"java.util.List.forEach(java.util.function.Consumer)\" because \"s2\" is null"
  let some s3 := (← getEdge bp.originalEdge).internal.splineRouteStart
    | throwNullPointer "Cannot invoke \"java.util.Collection.toArray()\" because \"c\" is null"
  let e1 := (← getEdge bp.nodeStartEdge).internal.splineEdgeChain
  let e2 := (← getEdge bp.startEndEdge).internal.splineEdgeChain
  let e3 := (← getEdge bp.originalEdge).internal.splineEdgeChain
  for segment in s2 do
    P5Edges.Splines.modifySplineSegment graph segment fun x => { x with inverseOrder := true }
  let joinedSegments := s1 ++ s2.reverse ++ s3
  let joinedEdges := e1 ++ e2.reverse ++ e3
  let originalEdge := bp.originalEdge
  modifyEdge originalEdge fun e => { e with internal := { e.internal with
    splineRouteStart := some joinedSegments, splineEdgeChain := joinedEdges,
    splineSurvivingEdge := some originalEdge } }
  modifyEdge bp.nodeStartEdge fun e => { e with internal := { e.internal with
    splineRouteStart := none, splineEdgeChain := #[] } }
  modifyEdge bp.startEndEdge fun e => { e with internal := { e.internal with
    splineRouteStart := none, splineEdgeChain := #[] } }

/-- `remove(graph, bpi)`: restores the original edge of `bp` and removes the dummies, then
continues with `bp.prev`. -/
partial def remove (graph : LGraphId) (bp : BreakingPointInfo) (edgeRouting : EdgeRouting) : LayeredM Unit := do
  let mut newBends : KVectorChain := #[]
  match edgeRouting with
  | .splines => joinSplineRoutes graph bp
  | .polyline =>
    newBends := newBends ++ (← getEdge bp.nodeStartEdge).bendPoints
    newBends := newBends.push (← getNode bp.start).position
    newBends := newBends ++ (← getEdge bp.startEndEdge).bendPoints.reverse
    newBends := newBends.push (← getNode bp.endNode).position
    newBends := newBends ++ (← getEdge bp.originalEdge).bendPoints
  | _ =>
    newBends := newBends ++ (← getEdge bp.nodeStartEdge).bendPoints
    newBends := newBends ++ (← getEdge bp.startEndEdge).bendPoints.reverse
    newBends := newBends ++ (← getEdge bp.originalEdge).bendPoints
  -- Java clears the original edge's bend points for every routing style (`SPLINES`: no new bends)
  let bends := newBends
  modifyEdge bp.originalEdge fun e => { e with bendPoints := bends }
  let restoredSource := (← getEdge bp.nodeStartEdge).source
  setEdgeSource bp.originalEdge restoredSource
  let junctionPointsOne := (← getEdge bp.nodeStartEdge).props.get LayeredOptions.JUNCTION_POINTS
  let junctionPointsTwo := (← getEdge bp.startEndEdge).props.get LayeredOptions.JUNCTION_POINTS
  let junctionPointsThree := (← getEdge bp.originalEdge).props.get LayeredOptions.JUNCTION_POINTS
  if junctionPointsOne.isSome || junctionPointsTwo.isSome || junctionPointsThree.isSome then
    let newJunctionPoints : KVectorChain :=
      junctionPointsThree.getD #[] ++ junctionPointsTwo.getD #[] ++ junctionPointsOne.getD #[]
    setEdgeProp bp.originalEdge LayeredOptions.JUNCTION_POINTS newJunctionPoints
  setEdgeSource bp.startEndEdge none
  setEdgeTarget bp.startEndEdge none
  setEdgeSource bp.nodeStartEdge none
  setEdgeTarget bp.nodeStartEdge none
  setNodeLayer bp.endNode none
  setNodeLayer bp.start none
  if let some prevStart := bp.prev then
    if let some prev ← BreakingPointInfo.get? prevStart then
      remove graph prev edgeRouting

/-- `process(graph, monitor)`: `EDGE_ROUTING` falls back to `ORTHOGONAL` (Rust `unwrap_or`). -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Breaking Point Removing" 1.0
  let edgeRouting := ((← getGraph graph).props.get LayeredOptions.EDGE_ROUTING).getD .orthogonal
  for layer in (← getGraph graph).layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      if !(← BreakingPointInfo.isEnd node) then continue
      let some bpInfo ← BreakingPointInfo.get? node | continue
      if bpInfo.next.isNone then
        remove graph bpInfo edgeRouting
  monitor.done

/-- The `BreakingPointRemover` processor. -/
def processor : LayeredProcessor := { name := "BreakingPointRemover", process := process }

end BreakingPointRemover

builtin_initialize registerBreakingPointRemover : Unit ←
  IntermediateProcessorStrategy.register .breakingPointRemover BreakingPointRemover.processor

end Elk.Alg.Layered.Intermediate.Wrapping
