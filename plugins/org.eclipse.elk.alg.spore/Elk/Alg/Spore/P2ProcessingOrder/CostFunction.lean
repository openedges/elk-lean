import Std.Data.HashMap
import Elk.Core.Math.ElkMath
import Elk.Alg.Common.Geometry.ICostFunction
import Elk.Alg.Common.Utils.Utils
import Elk.Alg.Spore.Graph.Graph
/-!
# `GraphCostFunction` / `InvertedCostFunction`

Port of `p2processingorder/cost_function.rs` (elk-rs): the `ICostFunction` selected by
`Graph.costFunction` (Java: the `SpanningTreeCostFunction` lambdas of `MinSTPhase`/`Graph`), and
the negating wrapper used by `MaxSTPhase`.

Rust details kept: the node lookup table maps `originalVertex ↦ node` (later vertices overwrite
earlier ones), `MINIMUM_ROOT_DISTANCE` uses the preferred root's `vertex` (not `originalVertex`),
`CIRCLE_UNDERLAP` measures the distance to the rectangle's top-left *position* (not its center),
and every cost that needs a node falls back to the center distance when a vertex is unknown.
-/
namespace Elk.Alg.Spore.P2ProcessingOrder

open Elk.Core.Util Elk.Core.Math Elk.Alg.Common Elk.Alg.Common.Spore Elk.Alg.Common.Utils
open Elk.Alg.Spore.Graph Elk.Alg.Spore.Options

namespace GraphCostFunction

/-- `GraphCostFunction::new(graph)` and `cost(edge)`: the cost function of `graph.costFunction`. -/
def new (graph : Graph) : ICostFunction :=
  let nodes : Std.HashMap KVector Node := graph.vertices.foldl
    (fun m node => m.insert node.originalVertex node) {}
  let preferredRoot : Option KVector := graph.preferredRoot.map (·.vertex)
  let costFunction := graph.costFunction
  fun edge =>
    match costFunction with
    | .centerDistance => edge.u.distance edge.v
    | .minimumRootDistance =>
      match preferredRoot with
      | none => edge.u.distance edge.v
      | some root => fmin (edge.u.distance root) (edge.v.distance root)
    | .circleUnderlap =>
      match nodes.get? edge.u, nodes.get? edge.v with
      | some n1, some n2 =>
        edge.u.distance edge.v - edge.u.distance n1.rect.position - edge.v.distance n2.rect.position
      | _, _ => edge.u.distance edge.v
    | .rectangleUnderlap =>
      match nodes.get? edge.u, nodes.get? edge.v with
      | some n1, some n2 => n1.underlap n2
      | _, _ => edge.u.distance edge.v
    | .invertedOverlap =>
      match nodes.get? edge.u, nodes.get? edge.v with
      | some n1, some n2 =>
        let dist := ElkMath.shortestDistance n1.rect n2.rect
        let s := n2.rect.center.distance n1.rect.center
        (if dist >= 0.0 then dist else -(Utils.overlap n1.rect n2.rect - 1.0) * s)
      | _, _ => edge.u.distance edge.v

end GraphCostFunction

namespace InvertedCostFunction

/-- `InvertedCostFunction::new(inner)` and `cost(edge)`: `-inner.cost(edge)`. -/
def new (inner : ICostFunction) : ICostFunction := fun edge => -(inner edge)

end InvertedCostFunction

end Elk.Alg.Spore.P2ProcessingOrder
