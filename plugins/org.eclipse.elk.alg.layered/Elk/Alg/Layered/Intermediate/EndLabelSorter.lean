import Elk.Alg.Layered.Intermediate.EndLabelPreprocessor
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.intermediate.EndLabelSorter`

Port of Java `EndLabelSorter` (agent COV; elk-rs sorted the `REPRESENTED_LABELS` of `LABEL` dummies
by text instead, which is a no-op in the regular pipeline): "Sorts end labels according to the order
of nodes their respective edges come from or head to. This is to prevent seemingly random label
orders in diagrams that employ end labels and have multiple edges going into or leaving the same
port."

Slot: after phase 5 (same-slot dependencies `LongEdgeJoiner`, `NorthSouthPortPostprocessor`).

For every `NORMAL` node with `END_LABELS`, every port with at least two incident edges carrying end
labels for it (head labels of incoming, tail labels of outgoing edges) gets the labels of its cell
regrouped by edge (`END_LABEL_EDGE`) and the groups sorted by source port id, then target node id,
then target port id descending, with the ids of the whole graph assigned in layer/node/port order
the first time a node needs sorting (Java `initialize`, written into `LNode.id`/`LPort.id` like
Java). The sort is the stable `List.sort` with a consistent comparator (`stableSort`). Java collects
the groups from a `HashMap<LEdge, LabelGroup>` keyed by identity hash, so groups that compare equal
(parallel edges between the same ports) come out in an identity-hash order that depends on the JVM
run; here they keep the order of their first label in the cell. A port that needs sorting but has no
label cell makes Java throw a `NullPointerException` in `createLabelGroups`, reproduced here.
-/

namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Options Elk.Core.Util Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options LayeredM
open Elk.Alg.Common.NodeSpacing

namespace EndLabelSorter

/-- Java's `NullPointerException` of `createLabelGroups(portLabelCell)` for a port without cell. -/
def nullCellError : String :=
  "Cannot invoke \"org.eclipse.elk.alg.common.nodespacing.cellsystem.LabelCell.getLabels()\" because " ++
  "\"portLabelCell\" is null"

/-- Whether one of the edge's labels has the given `EDGE_LABELS_PLACEMENT`. -/
private def hasLabelWithPlacement (edge : LEdgeId) (placement : EdgeLabelPlacement) : LayeredM Bool := do
  for label in (← getEdge edge).labels do
    if (← getLabel label).props.getD LayeredOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.center == placement then
      return true
  return false

/-- `needsSorting(port)`: at least two incident edges with end labels for the port (head labels of
incoming, tail labels of outgoing edges). -/
def needsSorting (port : LPortId) : LayeredM Bool := do
  let pt ← getPort port
  let mut edgesWithEndLabels : Nat := 0
  for inEdge in pt.incomingEdges do
    if ← hasLabelWithPlacement inEdge .head then edgesWithEndLabels := edgesWithEndLabels + 1
  for outEdge in pt.outgoingEdges do
    if ← hasLabelWithPlacement outEdge .tail then edgesWithEndLabels := edgesWithEndLabels + 1
  return edgesWithEndLabels >= 2

/-- `initialize(lGraph)`: ascending ids for the nodes and ports of all layers (a node, then its
ports). -/
def initializeIds (graph : LGraphId) : LayeredM Unit := do
  let mut nextElementId : Int := 0
  for layer in (← getGraph graph).layers do
    for node in (← getLayer layer).nodes do
      let nodeId := nextElementId
      modifyNode node fun n => { n with id := nodeId }
      nextElementId := nextElementId + 1
      for port in (← getNode node).ports do
        let portId := nextElementId
        modifyPort port fun p => { p with id := portId }
        nextElementId := nextElementId + 1

/-- `LABEL_GROUP_COMPARATOR` on the sort keys of two groups' edges:
`(source port id, target node id, -target port id)`. -/
private def compareGroupKeys (a b : Int × Int × Int) : Ordering :=
  match compare a.1 b.1 with
  | .eq =>
    match compare a.2.1 b.2.1 with
    | .eq => compare b.2.2 a.2.2
    | o => o
  | o => o

/-- The sort key of the group of `edge`. Every gathered end label has its `END_LABEL_EDGE`
(`EndLabelPreprocessor.gatherLabels`) and the edges are connected after `LongEdgeJoiner`; Java would
dereference `null` in the comparator otherwise. -/
private def groupKey (edge : Option LEdgeId) : LayeredM (Int × Int × Int) := do
  let some e := edge | throwNullPointer "label group without edge"
  let ed ← getEdge e
  let (some source, some target) := (ed.source, ed.target) | throwNullPointer "label group edge without ports"
  let some targetNode := (← getPort target).owner | throwNullPointer "label group edge target without node"
  return ((← getPort source).id, (← getNode targetNode).id, (← getPort target).id)

/-- `sort(port, portLabelCell)`: regroups the labels of the cell by `END_LABEL_EDGE` (groups in
order of their first label) and sorts the groups; the cell's label list is replaced directly (its
size is not recomputed). -/
def sortCell (cell : EndLabelPreprocessor.EndLabelCell) : LayeredM EndLabelPreprocessor.EndLabelCell := do
  match cell.kind with
  | .label d =>
    -- `createLabelGroups`
    let mut groupEdges : Array (Option LEdgeId) := #[]
    let mut groupLabels : Array (Array (LLabelId × Elk.Core.Math.KVector)) := #[]
    for entry in d.labels do
      let edge := (← getLabel entry.1).internal.endLabelEdge
      match groupEdges.findIdx? (· == edge) with
      | some i => groupLabels := groupLabels.modify i (·.push entry)
      | none =>
        groupEdges := groupEdges.push edge
        groupLabels := groupLabels.push #[entry]
    -- a single group is not compared (Java's sort calls no comparator)
    if groupEdges.size < 2 then
      return { cell with kind := .label { d with labels := groupLabels.foldl (· ++ ·) #[] } }
    let mut keyed : Array ((Int × Int × Int) × Array (LLabelId × Elk.Core.Math.KVector)) := #[]
    for (edge, labels) in groupEdges.zip groupLabels do
      keyed := keyed.push ((← groupKey edge), labels)
    let sorted := stableSort keyed fun a b => compareGroupKeys a.1 b.1
    let labels := sorted.foldl (fun acc g => acc ++ g.2) #[]
    return { cell with kind := .label { d with labels := labels } }
  | _ => return cell

/-- `processNode(node)`. -/
def processNode (graph : LGraphId) (node : LNodeId) : LayeredM Unit := do
  let some labelCellMap := (← getNode node).internal.endLabels | return
  let mut cellMap := labelCellMap
  let mut initializeMethodCalled := false
  for port in (← getNode node).ports do
    if ← needsSorting port then
      if !initializeMethodCalled then
        initializeIds graph
        initializeMethodCalled := true
      match cellMap.findIdx? (·.1 == port) with
      | some i => cellMap := cellMap.set! i (port, ← sortCell cellMap[i]!.2)
      | none => throwNullPointer nullCellError
  let m := cellMap
  modifyNode node fun n => { n with internal := { n.internal with endLabels := some m } }

/-- `process(layeredGraph, monitor)`: the `NORMAL` nodes of all layers (layer order, node order). -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Sort end labels" 1.0
  for layer in (← getGraph graph).layers do
    for node in (← getLayer layer).nodes do
      if (← getNode node).type == .normal then
        let some owner ← nodeGraph node | continue
        processNode owner node
  monitor.done

/-- The `EndLabelSorter` processor. -/
def processor : LayeredProcessor := { name := "EndLabelSorter", process := process }

end EndLabelSorter

builtin_initialize registerEndLabelSorter : Unit ←
  IntermediateProcessorStrategy.register .endLabelSorter EndLabelSorter.processor

end Elk.Alg.Layered.Intermediate
