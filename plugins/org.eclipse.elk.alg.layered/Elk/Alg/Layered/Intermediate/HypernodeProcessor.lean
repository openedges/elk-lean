import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.HypernodesProcessor`

Port of elk-rs `intermediate/hypernode_processor.rs` (Java class `HypernodesProcessor`). Improves
the placement of hypernodes (at most two ports, none on the north/south sides) by moving them onto
the first join point of their connected edges: the edges starting (or ending) at the leftmost
(rightmost) first (last) bend point are reconnected to a new north or south port and lose that
bend point (and the equal junction points).

The processor name is the Java simple class name `HypernodesProcessor` (the elk-rs `type_name` is
`HypernodeProcessor`).

Follows Java (agent COV): the removed bend point is removed from the **first** equal entry of
`JUNCTION_POINTS` only (`KVectorChain.remove(Object)`; elk-rs removed all equal entries).
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace HypernodeProcessor

/-- `i32::MAX as f64` (Java `Integer.MAX_VALUE` start values). -/
private def INT_MAX : Float := 2147483647.0

/-- `junctionPoints.remove(first)` (Java `KVectorChain.remove(Object)` = `LinkedList.remove`): drops
the first junction point equal to the point (`KVector.equals`: `x == x' && y == y'`). -/
def removeJunctionPoint (edge : LEdgeId) (removedPoint : KVector) : LayeredM Unit := do
  let some junctionPoints := (← getEdge edge).props.get LayeredOptions.JUNCTION_POINTS | return
  let some i := junctionPoints.findIdx? (· == removedPoint) | return
  let remaining := junctionPoints.eraseIdx! i
  modifyEdge edge fun e => { e with props := e.props.set LayeredOptions.JUNCTION_POINTS remaining }

/-- `process_right_edge(edge, north_port, south_port)`: removes the first bend point; the edge
leaves through the south port when the next point (next bend point, else the target anchor) is
not above it, else through the north port. -/
def processRightEdge (edge : LEdgeId) (northPort southPort : LPortId) : LayeredM Unit := do
  let ed ← getEdge edge
  let points := ed.bendPoints
  let some first := points[0]? | return
  let rest := points.extract 1 points.size
  modifyEdge edge fun e => { e with bendPoints := rest }
  let second ← match rest[0]? with
    | some next => pure (some next)
    | none => match ed.target with
      | some target => withArena (·.portAbsoluteAnchor target)
      | none => pure none
  let some secondPoint := second | return
  if secondPoint.y >= first.y then
    setEdgeSource edge (some southPort)
  else
    setEdgeSource edge (some northPort)
  removeJunctionPoint edge first

/-- `process_left_edge(edge, north_port, south_port)`: mirror of `processRightEdge` on the last
bend point and the edge target. -/
def processLeftEdge (edge : LEdgeId) (northPort southPort : LPortId) : LayeredM Unit := do
  let ed ← getEdge edge
  let points := ed.bendPoints
  let some lastPoint := points.back? | return
  let rest := points.pop
  modifyEdge edge fun e => { e with bendPoints := rest }
  let second ← match rest.back? with
    | some prev => pure (some prev)
    | none => match ed.source with
      | some source => withArena (·.portAbsoluteAnchor source)
      | none => pure none
  let some secondPoint := second | return
  if secondPoint.y >= lastPoint.y then
    setEdgeTarget edge (some southPort)
  else
    setEdgeTarget edge (some northPort)
  removeJunctionPoint edge lastPoint

/-- Rust `move_hypernode` (right branch): edges whose first bend point has the minimal x
(starting from the graph width) and the x/y distances to the next candidates. -/
private def collectRightBendEdges (graph : LGraphId) (ports : Array LPortId) :
    LayeredM (Array LEdgeId × Float × Float × Float) := do
  let mut bendEdges : Array LEdgeId := #[]
  let mut bendX := (← getGraph graph).size.x
  let mut diffX := INT_MAX
  let mut diffY := INT_MAX
  for port in ports do
    for edge in (← getPort port).outgoingEdges do
      let points := (← getEdge edge).bendPoints
      let some first := points[0]? | continue
      if first.x < bendX then
        diffX := bendX - first.x
        diffY := INT_MAX
        bendEdges := #[]
        bendX := first.x
      if first.x <= bendX then
        bendEdges := bendEdges.push edge
        if points.size > 1 then
          diffY := fmin diffY (Float.abs (points[1]!.y - first.y))
  return (bendEdges, bendX, diffX, diffY)

/-- Rust `move_hypernode` (left branch): edges whose last bend point has the maximal x; the start
value is `Integer.MAX_VALUE` as in Java. -/
private def collectLeftBendEdges (ports : Array LPortId) : LayeredM (Array LEdgeId × Float × Float × Float) := do
  let mut bendEdges : Array LEdgeId := #[]
  let mut bendX := INT_MAX
  let mut diffX := INT_MAX
  let mut diffY := INT_MAX
  for port in ports do
    for edge in (← getPort port).incomingEdges do
      let points := (← getEdge edge).bendPoints
      let some last := points.back? | continue
      if last.x > bendX then
        diffX := last.x - bendX
        diffY := INT_MAX
        bendEdges := #[]
        bendX := last.x
      if last.x >= bendX then
        bendEdges := bendEdges.push edge
        if points.size > 1 then
          let penultimate := points[points.size - 2]!
          diffY := fmin diffY (Float.abs (penultimate.y - last.y))
  return (bendEdges, bendX, diffX, diffY)

/-- `move_hypernode(layered_graph, hypernode, right)` (Java `moveHypernode`). -/
def moveHypernode (graph : LGraphId) (hypernode : LNodeId) (right : Bool) : LayeredM Unit := do
  let ports := (← getNode hypernode).ports
  let (bendEdges, bendX, diffX, diffY) ← if right then collectRightBendEdges graph ports
    else collectLeftBendEdges ports
  let size := (← getNode hypernode).size
  let nodeWidth := size.x
  let nodeHeight := size.y
  if bendEdges.isEmpty || diffX <= nodeWidth / 2.0 || diffY <= nodeHeight / 2.0 then return
  let northPort ← LayeredM.createPort
  setPortNode northPort (some hypernode)
  modifyPort northPort fun p =>
    let p := p.setSide .north
    { p with position := { p.position with x := nodeWidth / 2.0 } }
  let southPort ← LayeredM.createPort
  setPortNode southPort (some hypernode)
  modifyPort southPort fun p =>
    let p := p.setSide .south
    { p with position := ⟨nodeWidth / 2.0, nodeHeight⟩ }
  for edge in bendEdges do
    if right then
      processRightEdge edge northPort southPort
    else
      processLeftEdge edge northPort southPort
  modifyNode hypernode fun n => { n with position := { n.position with x := bendX - nodeWidth / 2.0 } }

/-- `process(layered_graph, monitor)`: hypernodes with at most two ports and no north/south ports
move right when they have at least as many eastern as western ports, else left. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Hypernodes processing" 1.0
  for layer in (← getGraph graph).layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      let nd ← getNode node
      let isHypernode := nd.props.getD LayeredOptions.HYPERNODE false
      if !isHypernode || nd.ports.size > 2 then continue
      let mut topEdges := 0
      let mut rightEdges := 0
      let mut bottomEdges := 0
      let mut leftEdges := 0
      for port in nd.ports do
        match (← getPort port).side with
        | .north => topEdges := topEdges + 1
        | .east => rightEdges := rightEdges + 1
        | .south => bottomEdges := bottomEdges + 1
        | .west => leftEdges := leftEdges + 1
        | .undefined => pure ()
      -- Java parity: only move if there are no top/bottom connections
      if topEdges == 0 && bottomEdges == 0 then
        moveHypernode graph node (leftEdges <= rightEdges)
  monitor.done

/-- The hypernode processor (`HypernodesProcessor` in Java). -/
def processor : LayeredProcessor := { name := "HypernodesProcessor", process := process }

end HypernodeProcessor

builtin_initialize registerHypernodeProcessor : Unit ←
  IntermediateProcessorStrategy.register .hypernodeProcessor HypernodeProcessor.processor

end Elk.Alg.Layered.Intermediate
