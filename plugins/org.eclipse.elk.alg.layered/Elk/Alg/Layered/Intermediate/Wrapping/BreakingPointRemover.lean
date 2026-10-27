import Elk.Alg.Layered.Intermediate.Wrapping.BreakingPointInserter
/-!
# `org.eclipse.elk.alg.layered.intermediate.wrapping.BreakingPointRemover`

Port of elk-rs `intermediate/breaking_point_remover.rs`. Locates the breaking point end dummies
whose info has no `next` and removes each chain (following `prev`) after transferring the routes
of the split edges to the original edge:

```
node --nodeStartEdge--> startMarker --startEndEdge--> endMarker --e--> node
```

* `SPLINES`: the spline segments and edge chains are joined (`s1 ++ reverse(s2) ++ s3`, the
  segments of `s2` get `inverseOrder`) and stored on the original edge, which becomes its own
  `SPLINE_SURVIVING_EDGE`; the bend points are left untouched (Rust; Java clears them).
* `POLYLINE`: `nodeStartEdge` bends, the start dummy position, the reversed `startEndEdge` bends,
  the end dummy position, the original bends.
* otherwise (orthogonal): as polyline without the two dummy positions.

The junction points of the three edges are concatenated (original, `startEndEdge`,
`nodeStartEdge`); since `JUNCTION_POINTS` has a default (empty chain) the Rust `is_some()` test is
always true, so the joined chain is always stored. The original edge gets the source of
`nodeStartEdge` back; the dummy edges are disconnected and the dummies removed from their layers.

Slots: after phase 5; after `LongEdgeJoiner`, before `HorizontalGraphCompactor`.

TODO(internal-field): `InternalProperties.SPLINE_ROUTE_START` (and `SplineSegment.inverseOrder`)
are not modelled yet (the splines package is not ported); for `SPLINES` only the edge chains and
the surviving edge are transferred. Requested field once `SplineSegment` exists:
`splineRouteStart : Array SplineSegmentId := #[]` in `LEdgeInternals`.
-/
namespace Elk.Alg.Layered.Intermediate.Wrapping

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace BreakingPointRemover

/-- The `SPLINES` branch of `remove` (see the module doc and its TODO). -/
private def joinSplineRoutes (bp : BreakingPointInfo) : LayeredM Unit := do
  let e1 := (← getEdge bp.nodeStartEdge).internal.splineEdgeChain
  let e2 := (← getEdge bp.startEndEdge).internal.splineEdgeChain
  let e3 := (← getEdge bp.originalEdge).internal.splineEdgeChain
  -- TODO(internal-field): SPLINE_ROUTE_START s1 ++ reverse(s2) (inverseOrder := true) ++ s3
  let joinedEdges := e1 ++ e2.reverse ++ e3
  let originalEdge := bp.originalEdge
  modifyEdge originalEdge fun e => { e with internal := { e.internal with
    splineEdgeChain := joinedEdges, splineSurvivingEdge := some originalEdge } }
  modifyEdge bp.nodeStartEdge fun e => { e with internal := { e.internal with splineEdgeChain := #[] } }
  modifyEdge bp.startEndEdge fun e => { e with internal := { e.internal with splineEdgeChain := #[] } }

/-- `remove(graph, bpi)`: restores the original edge of `bp` and removes the dummies, then
continues with `bp.prev`. -/
partial def remove (bp : BreakingPointInfo) (edgeRouting : EdgeRouting) : LayeredM Unit := do
  let mut newBends : KVectorChain := #[]
  match edgeRouting with
  | .splines => joinSplineRoutes bp
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
  if edgeRouting != .splines then
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
      remove prev edgeRouting

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
        remove bpInfo edgeRouting
  monitor.done

/-- The `BreakingPointRemover` processor. -/
def processor : LayeredProcessor := { name := "BreakingPointRemover", process := process }

end BreakingPointRemover

builtin_initialize registerBreakingPointRemover : Unit ←
  IntermediateProcessorStrategy.register .breakingPointRemover BreakingPointRemover.processor

end Elk.Alg.Layered.Intermediate.Wrapping
