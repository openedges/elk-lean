import Elk.Alg.Common.NetworkSimplex.NNode
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.common.networksimplex.NEdge` (elk-rs `n_edge.rs`)

An edge of the network simplex graph: a source and a target `NNode`, a weight
and a minimum length (`delta`).

`NEdgeBuilder.create` and `NEdge.reverse` modify the incident nodes and are
therefore defined in `Elk.Alg.Common.NetworkSimplex.NGraph`.
-/

namespace Elk.Alg.Common.NetworkSimplex

/-- `NEdge`: an edge in the graph processed by the `NetworkSimplex` algorithm. -/
structure NEdge (ο : Type) where
  /-- `NEdge.id`: a public id, unused internally. -/
  id : Int := 0
  /-- `NEdge.internalId`: internally set and used id to index arrays. -/
  internalId : Nat := 0
  /-- `NEdge.origin`: an object from which this edge is derived. -/
  origin : Option ο := none
  /-- `NEdge.source` (Rust `Weak<Mutex<NNode>>`). -/
  source : NNodeId := default
  /-- `NEdge.target` (Rust `Weak<Mutex<NNode>>`). -/
  target : NNodeId := default
  /-- `NEdge.weight`. -/
  weight : Float := fl0p0
  /-- `NEdge.delta`: the minimum length of this edge. -/
  delta : Int := 1
  /-- `NEdge.treeEdge`: whether the edge is part of the spanning tree (never
  written by the elk-rs algorithm, which keeps a dense cache instead). -/
  treeEdge : Bool := false
  deriving Repr

instance {ο : Type} : Inhabited (NEdge ο) := ⟨{}⟩

namespace NEdge

/-- `NEdge.getOther(NNode)` / Rust `NEdge::other` without the failure case:
the opposite node of `some`, or `none` if `some` is neither source nor target. -/
@[inline] def other? {ο : Type} (e : NEdge ο) (some : NNodeId) : Option NNodeId :=
  if some == e.source then .some e.target
  else if some == e.target then .some e.source
  else none

/-- `NEdge.getOther(NNode)` / Rust `NEdge::other`: the opposite node of `some`.
Throws `IllegalArgumentException` (the Java exception; Rust panics with
"Node not part of edge") if `some` is neither source nor target. -/
def other {ο : Type} (e : NEdge ο) (some : NNodeId) : IO NNodeId :=
  match e.other? some with
  | .some n => pure n
  | none => throw (IO.userError "java.lang.IllegalArgumentException: Node not part of edge")

end NEdge

/-- `NEdge.NEdgeBuilder`: builder for `NEdge`s
(`NEdge.of().weight(..).delta(..).source(..).target(..).create()`). -/
structure NEdgeBuilder (ο : Type) where
  /-- The edge being constructed (its `source`/`target` are taken from `source?`/`target?`). -/
  edge : NEdge ο := {}
  /-- The source node, once set (Rust `Option<NNodeRef>`). -/
  source? : Option NNodeId := none
  /-- The target node, once set. -/
  target? : Option NNodeId := none

/-- `NEdge.of()`: a builder to create a new edge. -/
@[inline] def NEdge.of {ο : Type} : NEdgeBuilder ο := {}

/-- Rust `NEdge::of_origin(origin)`: a builder with the origin set. (The Java
`NEdge.of(Object)` ignores its argument; the Rust port, followed here, sets it.) -/
@[inline] def NEdge.ofOrigin {ο : Type} (origin : ο) : NEdgeBuilder ο := { edge := { origin := some origin } }

namespace NEdgeBuilder

/-- `NEdgeBuilder.id(int)`: sets the id field. -/
@[inline] def id {ο : Type} (b : NEdgeBuilder ο) (id : Int) : NEdgeBuilder ο :=
  { b with edge := { b.edge with id := id } }

/-- `NEdgeBuilder.origin(Object)`: sets the origin field. -/
@[inline] def origin {ο : Type} (b : NEdgeBuilder ο) (origin : ο) : NEdgeBuilder ο :=
  { b with edge := { b.edge with origin := some origin } }

/-- `NEdgeBuilder.weight(double)`: sets the weight of the edge. -/
@[inline] def weight {ο : Type} (b : NEdgeBuilder ο) (weight : Float) : NEdgeBuilder ο :=
  { b with edge := { b.edge with weight := weight } }

/-- `NEdgeBuilder.delta(int)`: sets the minimal length of the edge. -/
@[inline] def delta {ο : Type} (b : NEdgeBuilder ο) (delta : Int) : NEdgeBuilder ο :=
  { b with edge := { b.edge with delta := delta } }

/-- `NEdgeBuilder.source(NNode)`: sets the source node. -/
@[inline] def source {ο : Type} (b : NEdgeBuilder ο) (source : NNodeId) : NEdgeBuilder ο :=
  { b with source? := some source }

/-- `NEdgeBuilder.target(NNode)`: sets the target node. -/
@[inline] def target {ο : Type} (b : NEdgeBuilder ο) (target : NNodeId) : NEdgeBuilder ο :=
  { b with target? := some target }

end NEdgeBuilder

end Elk.Alg.Common.NetworkSimplex
