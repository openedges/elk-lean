import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
/-!
# `org.eclipse.elk.alg.layered.intermediate.LongEdgeJoiner`

Port of elk-rs `intermediate/long_edge_joiner.rs`. Removes the `LONG_EDGE` dummy nodes created by
edge splitting: of a chain of edges `e1, …, ek` the first edge `e1` survives (it takes over the
target of the last edge, at the dropped edge's index in the target's incoming list) and collects
the bend points, labels and junction points of the dropped edges. With `UNNECESSARY_BENDPOINTS`
the absolute anchor of the dummy's first port is added as an extra bend point.

Iteration order (Rust): the graph's layers, per layer the node list taken when the layer is
visited; each joined dummy is removed from its layer (`set_layer(None)`).

`joinAt` is public, as in Java/Rust, for other processors that join long edges.
-/
namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace LongEdgeJoiner

/-- Appends the dropped edge's junction points to the surviving edge's `JUNCTION_POINTS` (Rust:
only when the dropped edge has the property; the surviving chain starts empty when unset). -/
private def joinJunctionPoints (survivingEdge : LEdgeId) (dropped : LEdge) : LayeredM Unit := do
  let droppedJunctionPoints := if dropped.props.has LayeredOptions.JUNCTION_POINTS then
    dropped.props.get LayeredOptions.JUNCTION_POINTS else none
  if let some djp := droppedJunctionPoints then
    modifyEdge survivingEdge fun e =>
      let survivingJunctions := (if e.props.has LayeredOptions.JUNCTION_POINTS then
        e.props.get LayeredOptions.JUNCTION_POINTS else none).getD KVectorChain.empty
      { e with props := e.props.set LayeredOptions.JUNCTION_POINTS (survivingJunctions ++ djp) }

/-- `LongEdgeJoiner::join_at(long_edge_dummy, add_unnecessary_bendpoints)` (Java `joinAt`): joins
the edges of the dummy's first western input port with those of its first eastern output port,
pairing them by index (the splitter and the hyperedge merger keep both lists aligned). As in Java,
the loop runs once per incoming edge and takes the first remaining outgoing edge each time: with
fewer outgoing than incoming edges (after merged hyperedge dummies or wrapping dummies) Java's
`outputPortEdges.get(0)` throws `IndexOutOfBoundsException: Index 0 out of bounds for length 0`
(elk-rs paired only `min(in, out)` edges). -/
def joinAt (longEdgeDummy : LNodeId) (addUnnecessaryBendpoints : Bool) : LayeredM Unit := do
  let westPort := (← withArena (·.nodePortsBySide longEdgeDummy .west))[0]?
  let eastPort := (← withArena (·.nodePortsBySide longEdgeDummy .east))[0]?
  let (some westPort, some eastPort) := (westPort, eastPort) | return
  let inputEdges := (← getPort westPort).incomingEdges
  let outputEdges := (← getPort eastPort).outgoingEdges
  let edgeCount := inputEdges.size
  let unnecessaryBendpoint ← match (← getNode longEdgeDummy).ports[0]? with
    | some p => withArena (·.portAbsoluteAnchor p)
    | none => pure none
  for i in [0:edgeCount] do
    let survivingEdge := inputEdges[i]!
    let some droppedEdge := outputEdges[i]?
      | throwJava indexOutOfBoundsExceptionClass "Index 0 out of bounds for length 0"
    let some droppedTarget := (← getEdge droppedEdge).target | continue
    let droppedEdgeListIndex := ((← getPort droppedTarget).incomingEdges.findIdx? (· == droppedEdge)).getD 0
    setEdgeTargetAndInsertAtIndex survivingEdge (some droppedTarget) droppedEdgeListIndex
    setEdgeSource droppedEdge none
    setEdgeTarget droppedEdge none
    if addUnnecessaryBendpoints then
      if let some bp := unnecessaryBendpoint then
        modifyEdge survivingEdge fun e => { e with bendPoints := e.bendPoints.push bp }
    let dropped ← getEdge droppedEdge
    modifyEdge survivingEdge fun e => { e with bendPoints := e.bendPoints ++ dropped.bendPoints }
    modifyEdge droppedEdge fun e => { e with labels := #[] }
    modifyEdge survivingEdge fun e => { e with labels := e.labels ++ dropped.labels }
    joinJunctionPoints survivingEdge dropped

/-- `process(layered_graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Edge joining" 1.0
  let gr ← getGraph graph
  let addUnnecessaryBendpoints := if gr.props.has LayeredOptions.UNNECESSARY_BENDPOINTS then
    gr.props.getD LayeredOptions.UNNECESSARY_BENDPOINTS false else false
  for layer in gr.layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      if (← getNode node).type != .longEdge then continue
      joinAt node addUnnecessaryBendpoints
      setNodeLayer node none
  monitor.done

/-- The `LongEdgeJoiner` processor. -/
def processor : LayeredProcessor := { name := "LongEdgeJoiner", process := process }

end LongEdgeJoiner

builtin_initialize registerLongEdgeJoiner : Unit ←
  IntermediateProcessorStrategy.register .longEdgeJoiner LongEdgeJoiner.processor

end Elk.Alg.Layered.Intermediate
