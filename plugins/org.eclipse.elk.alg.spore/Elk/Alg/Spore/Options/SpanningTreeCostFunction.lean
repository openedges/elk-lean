import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.spore.options.SpanningTreeCostFunction`

Port of `options/spanning_tree_cost_function.rs` (elk-rs) and `SpanningTreeCostFunction.java`. The
Java file only declares the constants; the cost computation (`GraphCostFunction`) lives in
`Elk.Alg.Spore.P2ProcessingOrder.CostFunction`.
-/
namespace Elk.Alg.Spore.Options

/-- `org.eclipse.elk.alg.spore.options.SpanningTreeCostFunction`: the cost function used in the
creation of the spanning tree.
* `CENTER_DISTANCE`: euclidean distance between the center points of the two nodes of a `TEdge`;
* `CIRCLE_UNDERLAP`: distance between the circumcircles of the two graph elements of a `TEdge`;
* `RECTANGLE_UNDERLAP`: underlap between the rectangles of the two graph elements of a `TEdge`;
* `INVERTED_OVERLAP`: overlap removal by Nachmanson et al. ("Node Overlap Removal by Growing a
  Tree"), `-overlap` if the nodes overlap, otherwise the shortest distance;
* `MINIMUM_ROOT_DISTANCE`: minimum of the euclidean distances between the nodes of an edge and the
  root of the spanning tree. -/
elk_enum SpanningTreeCostFunction :=
  centerDistance circleUnderlap rectangleUnderlap invertedOverlap minimumRootDistance

end Elk.Alg.Spore.Options
