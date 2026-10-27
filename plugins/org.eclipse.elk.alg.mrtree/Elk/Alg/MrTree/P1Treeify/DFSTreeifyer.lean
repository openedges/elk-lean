import Elk.Alg.MrTree.TreeLayoutPhases
import Elk.Alg.MrTree.Options.MrTreeOptions
/-!
# `org.eclipse.elk.alg.mrtree.p1treeify.DFSTreeifyer`

Port of `p1treeify/dfs_treeifyer.rs` (elk-rs), the phase `P1_TREEIFICATION`: turns the graph into a
forest by removing the edges that close a cycle or lead into an already visited node.

1. `init`: every node of the graph gets its list index as `id`; the visit marks are all 0.
2. `collect_edges`: for every node in list order whose mark is 0 a search (`SEARCH_ORDER`,
   `unwrap_or(DFS)`) starts at it; afterwards its mark becomes 2. The search marks a visited node
   with 1; an outgoing edge into a node marked 1 is *eliminated*, into a node marked 2 (the start of
   an earlier search) it is kept and the target is marked 1, into an unmarked node the search
   continues there. DFS recurses in the order of the outgoing edges; BFS (Rust `VecDeque`) marks a
   node only when it is dequeued, so a node can be enqueued (and processed) more than once and an
   edge can be eliminated twice, exactly like Rust.
3. The eliminated edges (in elimination order) leave the outgoing edges of their source and the
   incoming edges of their target (`remove_outgoing`/`remove_incoming`) and are stored as
   `REMOVABLE_EDGES` of the graph; the `Untreeifyer` (`DETREEIFYING_PROC`, slotted after
   `P3_NODE_PLACEMENT`) re-inserts them.

Marks are looked up by the node `id` (Rust `visited.get(id as usize)`, missing index = 0). The
recursion of Rust's `dfs` is kept (`partial def`): it terminates because every node is entered at
most once (its mark is set before its edges are followed).
-/
namespace Elk.Alg.MrTree.P1Treeify

open Elk.Core.Alg Elk.Core.Util Elk.Alg.MrTree Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options
open Elk.Alg.MrTree.Intermediate

namespace DFSTreeifyer

/-- The search state: `visited` marks by node id and the `eliminated` edges. -/
structure SearchState where
  visited : Array Int
  eliminated : Array TEdgeId := #[]

/-- `self.visited.get(id)` (0 for a missing index). -/
@[inline] private def mark (s : SearchState) (id : Int) : Int :=
  if id < 0 then 0 else s.visited[id.toNat]?.getD 0

/-- `if let Some(slot) = self.visited.get_mut(id) { *slot = v }`. -/
@[inline] private def setMark (s : SearchState) (id : Int) (v : Int) : SearchState :=
  if id < 0 then s else { s with visited := s.visited.modify id.toNat fun _ => v }

/-- `dfs(node)`. -/
partial def dfs (a : TArena) (node : TNodeId) (s : SearchState) : SearchState := Id.run do
  let mut s := setMark s (a.node node).id 1
  for edge in (a.node node).outgoingEdges do
    let some target := (a.edge edge).target | continue
    let targetId := (a.node target).id
    let visited := mark s targetId
    if visited == 1 then
      s := { s with eliminated := s.eliminated.push edge }
    else if visited == 2 then
      s := setMark s targetId 1
    else
      s := dfs a target s
  return s

/-- `bfs(start_node)`. -/
def bfs (a : TArena) (startNode : TNodeId) (s : SearchState) : SearchState := Id.run do
  let mut s := s
  let mut queue : Array TNodeId := #[startNode]
  let mut head := 0
  while head < queue.size do
    let node := queue[head]!
    head := head + 1
    s := setMark s (a.node node).id 1
    for edge in (a.node node).outgoingEdges do
      let some target := (a.edge edge).target | continue
      let targetId := (a.node target).id
      let visited := mark s targetId
      if visited == 1 then
        s := { s with eliminated := s.eliminated.push edge }
      else if visited == 2 then
        s := setMark s targetId 1
      else
        queue := queue.push target
  return s

/-- `init(graph)`: node ids := list indices. Returns the initial search state. -/
def init (graph : TGraphId) : MrTreeM SearchState := do
  let nodes := (← MrTreeM.getGraph graph).nodes
  for id in [0:nodes.size] do
    MrTreeM.modifyNode nodes[id]! fun n => { n with id := (id : Int) }
  return { visited := Array.replicate nodes.size 0 }

/-- `collect_edges(graph)`: searches the graph and removes the eliminated edges. -/
def collectEdges (graph : TGraphId) (s : SearchState) : MrTreeM Unit := do
  let g ← MrTreeM.getGraph graph
  let treeifyingOrder := (g.props.get MrTreeOptions.SEARCH_ORDER).getD .dfs
  let mut s := s
  for node in g.nodes do
    let a ← get
    let id := (a.node node).id
    if mark s id == 0 then
      s := match treeifyingOrder with
        | .dfs => dfs a node s
        | .bfs => bfs a node s
      s := setMark s id 2
  for edge in s.eliminated do
    let e ← MrTreeM.getEdge edge
    if let some source := e.source then MrTreeM.removeOutgoing source edge
    if let some target := e.target then MrTreeM.removeIncoming target edge
  MrTreeM.modifyGraph graph fun x => { x with internal.removableEdges := s.eliminated }

/-- `DFSTreeifyer::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "DFS Treeifying phase" 1.0
  let s ← init graph
  collectEdges graph s
  monitor.done

/-- `get_layout_processor_configuration`: `DETREEIFYING_PROC` after `P3_NODE_PLACEMENT`. -/
def configuration : TreeProcessorConfiguration :=
  LayoutProcessorConfiguration.create.addAfter TreeLayoutPhases.p3NodePlacement
    IntermediateProcessorStrategy.detreeifyingProc

/-- The `DFSTreeifyer` phase. -/
def phase : TreePhase :=
  { name := "DFSTreeifyer", process, getLayoutProcessorConfiguration := fun _ => pure (some configuration) }

end DFSTreeifyer

end Elk.Alg.MrTree.P1Treeify
