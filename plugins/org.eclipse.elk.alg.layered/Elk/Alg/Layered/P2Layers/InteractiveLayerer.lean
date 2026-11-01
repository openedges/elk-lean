import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Options.LayeredOptions
import Elk.Core.Util.Java
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.layered.p2layers.InteractiveLayerer` (elk-rs `interactive_layerer.rs`)

A layerer that infers the layering from the current node positions: the horizontal extents
`[x, x + max(width, 1))` of the nodes are merged into a sorted list of overlapping layer spans,
one layer per span; afterwards the layering is corrected so that edges point to later layers
(targets in the same or an earlier layer are moved to the layer after their source, repeatedly).

Orders reproduced from the Rust port: the spans list is scanned left to right and a new span is
inserted before the first span that starts at or after the node's right end; merged spans keep
the earlier span. The correction queue is a FIFO without duplicates (Java `LinkedHashSet`).
`LNode.id` is used as visited flag (`0` = not yet checked, `1` = checked) and `Layer.id` as layer
index. A target without layer counts as layer `-1` (Rust; Java would throw).
-/

namespace Elk.Alg.Layered.P2Layers

open Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Alg
open Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate LayeredM

namespace InteractiveLayerer

/-- `LayerSpan`: a horizontal span of the drawing and the nodes in it. -/
structure LayerSpan where
  start : Float
  «end» : Float
  nodes : Array LNodeId
  deriving Inhabited

/-- `getLayoutProcessorConfiguration(graph)`. -/
def processorConfiguration : LayeredProcessorConfiguration :=
  (LayoutProcessorConfiguration.create : LayeredProcessorConfiguration)
    |>.addBefore .p1CycleBreaking .interactiveExternalPortPositioner
    |>.addBefore .p2Layering .layerConstraintPreprocessor
    |>.addBefore .p3NodeOrdering .layerConstraintPostprocessor

/-- Inserts `node` with extent `[minx, maxx)` into the sorted span list. -/
def addToSpans (spans : Array LayerSpan) (node : LNodeId) (minx maxx : Float) : Array LayerSpan := Id.run do
  let mut spans := spans
  let mut idx := 0
  let mut foundIdx : Option Nat := none
  while idx < spans.size do
    let span := spans[idx]!
    if span.start >= maxx then
      break
    if span.end > minx then
      match foundIdx with
      | some found =>
        -- merge the previously found layer span with the current one
        spans := spans.modifyIn found fun f => { f with nodes := f.nodes ++ span.nodes, «end» := fmax f.end span.end }
        spans := spans.eraseIdx! idx
        continue
      | none =>
        -- add the node to the current layer span
        spans := spans.modifyIn idx fun s =>
          { s with nodes := s.nodes.push node, start := fmin s.start minx, «end» := fmax s.end maxx }
        foundIdx := some idx
    idx := idx + 1
  if foundIdx.isNone then
    spans := spans.insertIdx! idx { start := minx, «end» := maxx, nodes := #[node] }
  return spans

/-- `checkNode(node, graph)`: marks `node` as checked and moves every target of its output ports
that is not in a later layer to the layer after the node's layer (creating it if needed).
Returns the moved nodes without duplicates, in order. -/
def checkNode (graph graphRef : LGraphId) (node : LNodeId) : LayeredM (Array LNodeId) := do
  modifyNode node fun x => { x with id := 1 }
  let some layer1 := (← getNode node).layer | return #[]
  let layer1Id := (← getLayer layer1).id
  let mut shiftedNodes : Array LNodeId := #[]
  let mut seen : Std.HashSet LNodeId := {}
  for port in ← withArena (·.nodePortsByType node .output) do
    for edge in (← getPort port).outgoingEdges do
      let some targetPort := (← getEdge edge).target | continue
      let some targetNode := (← getPort targetPort).owner | continue
      if targetNode == node then continue
      let layer2Id ← match (← getNode targetNode).layer with
        | some l => pure (← getLayer l).id
        | none => pure (-1)
      if layer2Id <= layer1Id then
        let newIndex := (max (layer1Id + 1) 0).toNat
        if newIndex == (← getGraph graph).layers.size then
          let newLayer ← createLayer graphRef
          modifyLayer newLayer fun l => { l with id := layer1Id + 1 }
          modifyGraph graph fun g => { g with layers := g.layers.push newLayer }
          setNodeLayer targetNode (some newLayer)
        else if let some newLayer := (← getGraph graph).layers[newIndex]? then
          setNodeLayer targetNode (some newLayer)
        if !seen.contains targetNode then
          seen := seen.insert targetNode
          shiftedNodes := shiftedNodes.push targetNode
  return shiftedNodes

/-- `process(graph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Interactive node layering" fl1p0
  let nodes := (← getGraph graph).layerlessNodes
  if nodes.isEmpty then
    monitor.done
    return
  let graphRef := (← nodeGraph nodes[0]!).getD graph
  -- create layers with a start and an end position, merging when they overlap with others
  let mut currentSpans : Array LayerSpan := #[]
  for node in nodes do
    let nd ← getNode node
    let minx := nd.position.x
    let maxx := fmax (nd.position.x + nd.size.x) (minx + fl1p0)
    currentSpans := addToSpans currentSpans node minx maxx
  -- create real layers from the layer spans
  for h : nextIndex in [0:currentSpans.size] do
    let span := currentSpans[nextIndex]
    let layer ← createLayer graphRef
    modifyLayer layer fun l => { l with id := nextIndex }
    modifyGraph graph fun g => { g with layers := g.layers.push layer }
    for node in span.nodes do
      setNodeLayer node (some layer)
      modifyNode node fun x => { x with id := 0 }
  -- correct the layering respecting the graph topology, so edges point from left to right
  for node in nodes do
    if (← getNode node).id == 0 then
      let mut pending ← checkNode graph graphRef node
      let mut pendingSet : Std.HashSet LNodeId := pending.foldl (·.insert ·) {}
      let mut head := 0
      while head < pending.size do
        let nodeToCheck := pending[head]!
        head := head + 1
        pendingSet := pendingSet.erase nodeToCheck
        for newNode in ← checkNode graph graphRef nodeToCheck do
          if !pendingSet.contains newNode then
            pending := pending.push newNode
            pendingSet := pendingSet.insert newNode
  -- remove empty layers, which can happen when the layering has to be corrected
  let layers := (← getGraph graph).layers
  let nonEmpty ← layers.filterM fun l => do return !(← getLayer l).nodes.isEmpty
  modifyGraph graph fun g => { g with layers := nonEmpty, layerlessNodes := #[] }
  monitor.done

/-- The `InteractiveLayerer` phase. -/
def phase : LayeredPhase :=
  { name := "InteractiveLayerer"
    process := process
    getLayoutProcessorConfiguration := fun _ => pure (some processorConfiguration) }

end InteractiveLayerer

end Elk.Alg.Layered.P2Layers
