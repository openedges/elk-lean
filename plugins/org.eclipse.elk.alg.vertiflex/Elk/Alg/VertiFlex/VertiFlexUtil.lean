import Elk.Graph
/-!
# `org.eclipse.elk.alg.vertiflex.VertiFlexUtil`

Port of `vertiflex_util.rs` (elk-rs). The Rust phases each carry private copies of the helpers
`edge_target_node`, `outgoing_children` and `ensure_single_section`; they are shared here.
-/
namespace Elk.Alg.VertiFlex

open Elk.Graph

namespace VertiFlexUtil

/-- `VertiFlexUtil::find_root(graph)`: the first child of the graph without incoming edges
(`ElkGraphUtil::all_incoming_edges`, i.e. including the edges of its ports). -/
def findRoot (graph : NodeId) : ElkM (Option NodeId) :=
  ElkM.withGraph fun g =>
    (g.node graph).children.find? fun child => (ElkGraphUtil.allIncomingEdges g child).isEmpty

/-- `edge_target_node(edge)`: the node of the first target of the edge (the parent node for a
port), `none` for an edge without targets. -/
def edgeTargetNode (e : EdgeId) : ElkM (Option NodeId) :=
  ElkM.withGraph fun g => ((g.edge e).targets[0]?).bind (ElkGraphUtil.connectableShapeToNode g)

/-- The target nodes of `ElkGraphUtil::all_outgoing_edges(node)` in edge order (edges without a
target node are skipped), i.e. the children of a tree node. -/
def outgoingChildren (n : NodeId) : ElkM (Array NodeId) := do
  let edges ← ElkM.withGraph fun g => ElkGraphUtil.allOutgoingEdges g n
  let mut children : Array NodeId := #[]
  for e in edges do
    if let some c ← edgeTargetNode e then
      children := children.push c
  return children

/-- `ensure_single_section(edge)`: the single edge section of the edge. A missing section is
created; of several sections only the last one is kept (`sections.retain_last()`). -/
def ensureSingleSection (e : EdgeId) : ElkM SectionId := do
  let edge ← ElkM.getEdge e
  if edge.sections.isEmpty then
    ElkM.createSection (some e)
  else
    if edge.sections.size > 1 then
      modify fun g => g.retainLastEdgeSection e
    return (← ElkM.getEdge e).sections[0]!

end VertiFlexUtil

end Elk.Alg.VertiFlex
