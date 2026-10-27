import Elk.Alg.MrTree.Graph.TShape
/-!
# `org.eclipse.elk.alg.mrtree.graph.TLabel`

Port of `graph/t_label.rs` (elk-rs): a label of an edge. The constructor `TLabel::new(edge, text)`
(which appends the label to the edge) lives in `Elk.Alg.MrTree.Graph.TArena`. The elk-rs importer
creates no labels; the type is kept for completeness of the graph model.
-/
namespace Elk.Alg.MrTree.Graph

/-- `org.eclipse.elk.alg.mrtree.graph.TLabel`. -/
structure TLabel extends TShape where
  /-- `getEdge()`. -/
  edge : Option TEdgeId := none
  /-- `getText()`. -/
  text : Option String := none
  deriving Inhabited

end Elk.Alg.MrTree.Graph
