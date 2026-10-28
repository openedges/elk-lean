import Elk.Core.Math.KVector
/-!
# `org.eclipse.elk.alg.common.TEdge`

An undirected edge modeled as two vectors (`TEdge.java`, elk-rs `t_edge.rs`).

Equality is unordered: `(u, v) == (v, u)` (`KVector.equals`: `==` on both coordinates). The Java
`hashCode()` is `u.hashCode() + v.hashCode()` (order independent, `int` wrap); ELK keeps the edges in
`HashSet<TEdge>`s whose iteration order is a function of these hashes, reproduced with
`Elk.Core.Util.JavaHashSet` (elk-rs used `std` hash sets with a random iteration order).
-/
namespace Elk.Alg.Common

open Elk.Core.Util Elk.Core.Math

/-- `org.eclipse.elk.alg.common.TEdge` (Rust `TEdge`). -/
structure TEdge where
  /-- Vertex u. -/
  u : KVector
  /-- Vertex v. -/
  v : KVector
  deriving Repr, Inhabited

namespace TEdge

/-- `new TEdge(u, v)`. -/
@[inline] def new (u v : KVector) : TEdge := ⟨u, v⟩

/-- Java `equals`: unordered endpoint equality (`KVector ==`). -/
instance : BEq TEdge :=
  ⟨fun a b => (a.u == b.u && a.v == b.v) || (a.u == b.v && a.v == b.u)⟩

/-- Java `hashCode()`: `Objects.hashCode(u) + Objects.hashCode(v)`. -/
instance : JavaHashCode TEdge where
  javaHashCode e := JavaHashCode.javaHashCode e.u + JavaHashCode.javaHashCode e.v
  javaSame a b := a.u.sameBits b.u && a.v.sameBits b.v

instance : ToString TEdge := ⟨fun e => s!"{e.u}->{e.v}"⟩

end TEdge

end Elk.Alg.Common
