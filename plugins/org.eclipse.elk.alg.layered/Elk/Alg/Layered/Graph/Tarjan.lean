import Std.Data.HashMap
import Elk.Alg.Layered.Graph.Monad
/-!
# `org.eclipse.elk.alg.layered.graph.Tarjan`

Tarjan's strongly connected components over the layerless nodes of a graph, treating the
edges in `edgesToBeReversed` as reversed. Results: `stronglyConnectedComponents` (only
components with more than one node, in discovery order) and `nodeToSccId` (lookup only;
the Rust `BTreeMap` is keyed by pointer address, so its iteration order is never used).
-/
namespace Elk.Alg.Layered.Graph

open Elk.Graph

/-- `Tarjan` state. -/
structure Tarjan where
  edgesToBeReversed : Array LEdgeId
  stronglyConnectedComponents : Array (Array LNodeId) := #[]
  nodeToSccId : Std.HashMap LNodeId Nat := {}
  index : Int := 0
  stack : Array LNodeId := #[]

namespace Tarjan

/-- `Tarjan(edgesToBeReversed, sccs, nodeToSccId)` with empty results. -/
def new (edgesToBeReversed : Array LEdgeId) : Tarjan := { edgesToBeReversed := edgesToBeReversed }

abbrev TarjanM := StateT Tarjan LayeredM

private def edgeIsReversed (t : Tarjan) (e : LEdgeId) : Bool := t.edgesToBeReversed.contains e

/-- `strongConnected(v)`: the recursive DFS step. -/
partial def stronglyConnected (v : LNodeId) : TarjanM Unit := do
  let index := (← get).index
  LayeredM.modifyNode v fun nd => { nd with internal := { nd.internal with tarjanId := index, tarjanLowlink := index, tarjanOnStack := true } }
  modify fun t => { t with index := t.index + 1, stack := t.stack.push v }
  let edges ← LayeredM.withArena (·.nodeConnectedEdges v)
  for e in edges do
    let ed ← LayeredM.getEdge e
    let some source := ed.source | continue
    let some target := ed.target | continue
    let some sourceNode := (← LayeredM.getPort source).owner | continue
    let some targetNode := (← LayeredM.getPort target).owner | continue
    let sourceIsV := sourceNode == v
    let reversed := (← get).edgeIsReversed e
    if !sourceIsV && !reversed then continue
    if sourceIsV && reversed then continue
    let other := if targetNode == v then sourceNode else targetNode
    let targetId := (← LayeredM.getNode other).internal.tarjanId
    if targetId == -1 then
      stronglyConnected other
      let targetLowlink := (← LayeredM.getNode other).internal.tarjanLowlink
      LayeredM.modifyNode v fun nd => { nd with internal := { nd.internal with tarjanLowlink := min nd.internal.tarjanLowlink targetLowlink } }
    else if (← LayeredM.getNode other).internal.tarjanOnStack then
      LayeredM.modifyNode v fun nd => { nd with internal := { nd.internal with tarjanLowlink := min nd.internal.tarjanLowlink targetId } }
  let vNode ← LayeredM.getNode v
  if vNode.internal.tarjanLowlink == vNode.internal.tarjanId then
    let mut scc : Array LNodeId := #[]
    let mut continueLoop := true
    while continueLoop do
      match (← get).stack.back? with
      | none => continueLoop := false
      | some n =>
        modify fun t => { t with stack := t.stack.pop }
        LayeredM.modifyNode n fun nd => { nd with internal := { nd.internal with tarjanOnStack := false } }
        scc := scc.push n
        if n == v then continueLoop := false
    if scc.size > 1 then
      let sccFinal := scc
      modify fun t =>
        let index := t.stronglyConnectedComponents.size
        { t with stronglyConnectedComponents := t.stronglyConnectedComponents.push sccFinal,
                 nodeToSccId := sccFinal.foldl (fun m n => m.insert n index) t.nodeToSccId }

/-- `tarjan(graph)`: runs the DFS from every unvisited layerless node. -/
def tarjan (graph : LGraphId) : TarjanM Unit := do
  modify fun t => { t with index := 0, stack := #[] }
  let nodes := (← LayeredM.getGraph graph).layerlessNodes
  for n in nodes do
    if (← LayeredM.getNode n).internal.tarjanId == -1 then
      stronglyConnected n
      modify fun t => { t with stack := #[] }

/-- `resetTarjan(graph)`: clears the node marks and the edges' `IS_PART_OF_CYCLE`. -/
def resetTarjan (graph : LGraphId) : TarjanM Unit := do
  let nodes := (← LayeredM.getGraph graph).layerlessNodes
  for n in nodes do
    LayeredM.modifyNode n fun nd => { nd with internal := { nd.internal with tarjanOnStack := false, tarjanLowlink := -1, tarjanId := -1 } }
    modify fun t => { t with stack := #[] }
    let edges ← LayeredM.withArena (·.nodeConnectedEdges n)
    for e in edges do
      LayeredM.modifyEdge e fun ed => { ed with internal := { ed.internal with isPartOfCycle := false } }

/-- Runs a `TarjanM` action and returns its result with the final state. -/
def run {α : Type} (x : TarjanM α) (t : Tarjan) : LayeredM (α × Tarjan) := StateT.run x t

end Tarjan

end Elk.Alg.Layered.Graph
