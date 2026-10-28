import Elk.Graph
/-!
# `org.eclipse.elk.alg.vertiflex.VertiFlexUtil`

Port of `VertiFlexUtil.java` (elk-rs `vertiflex_util.rs`). The Rust phases each carry private copies
of the helpers `edge_target_node`, `outgoing_children` and `ensure_single_section`; they are shared
here. `findRoot` uses `ElkGraphUtil.allIncomingEdges` (ports included) like Java, the tree walks use
the node's own edges (`outgoingChildren`).
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

/-- Java's `ClassCastException` of `(ElkNode) edge.getTargets().get(0)` for a port target. -/
def PORT_CAST_EXCEPTION : String :=
  "java.lang.ClassCastException: class org.eclipse.elk.graph.impl.ElkPortImpl cannot be cast to class " ++
  "org.eclipse.elk.graph.ElkNode (org.eclipse.elk.graph.impl.ElkPortImpl and org.eclipse.elk.graph.ElkNode " ++
  "are in unnamed module of loader 'app')"

/-- `(ElkNode) edge.getTargets().get(0)`: the target node of an edge; a port target is Java's
`ClassCastException`, an edge without targets its `IndexOutOfBoundsException`. -/
def edgeChild (e : EdgeId) : ElkM NodeId := do
  let g : ElkGraph ← get
  let target : Option ConnectableId := (g.edge e).targets[0]?
  match target with
  | some (ConnectableId.node c) => return c
  | some (ConnectableId.port _) => throw (IO.userError PORT_CAST_EXCEPTION)
  | none => throw (IO.userError "java.lang.IndexOutOfBoundsException: Index 0 out of bounds for length 0")

/-- The children of a tree node as Java's phases read them: `(ElkNode)
node.getOutgoingEdges().get(i).getTargets().get(0)` — only the edges of the node itself (not of its
ports; elk-rs used `all_outgoing_edges`), in edge order; a port target is Java's
`ClassCastException`, an edge without targets its `IndexOutOfBoundsException`. -/
def outgoingChildren (n : NodeId) : ElkM (Array NodeId) := do
  let g : ElkGraph ← get
  (g.node n).outgoingEdges.mapM edgeChild

/-- Java `ElkGraphUtil.firstEdgeSection(edge, true, true)` of the edge routers: the first section of
the edge (created if missing), reset, the other sections removed. elk-rs `ensure_single_section`
keeps the *last* of several sections (`sections.retain_last()`). -/
def ensureSingleSection (e : EdgeId) : ElkM SectionId :=
  modifyGet fun g => let (g, s) := ElkGraphUtil.firstEdgeSection g e true true; (s, g)

end VertiFlexUtil

end Elk.Alg.VertiFlex
