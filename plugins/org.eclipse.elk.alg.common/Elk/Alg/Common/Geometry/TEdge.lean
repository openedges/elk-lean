import Elk.Core.Math.KVector
/-!
# `org.eclipse.elk.alg.common.TEdge`

An undirected edge modeled as two vectors (elk-rs `t_edge.rs`).

Equality is unordered: `(u, v) == (v, u)`. The hash is computed over the
endpoints ordered lexicographically (`cmp_kvector`: `partial_cmp` on `x`, then
`y`), so it is consistent with the unordered equality.

Rust keeps edges in `HashSet<TEdge>` (std `RandomState`, i.e. a per-process
random iteration order). The Lean port uses insertion-ordered, duplicate-free
`Array TEdge` values instead (`insertUnique`), see `BowyerWatsonTriangulation`.
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

/-- `TEdge::new(u, v)`. -/
@[inline] def new (u v : KVector) : TEdge := ⟨u, v⟩

/-- Rust `cmp_kvector`: `x` then `y`, `partial_cmp().unwrap_or(Equal)`. -/
def cmpKVector (a b : KVector) : Ordering :=
  match Float.comparePartial a.x b.x with
  | .eq => Float.comparePartial a.y b.y
  | o => o

/-- Rust `TEdge::ordered_endpoints`: the endpoints with the lexicographically smaller one
first (`u` first on ties). -/
def orderedEndpoints (e : TEdge) : KVector × KVector :=
  if cmpKVector e.u e.v == .gt then (e.v, e.u) else (e.u, e.v)

/-- Rust `PartialEq for TEdge`: unordered endpoint equality (`KVector ==`). -/
instance : BEq TEdge :=
  ⟨fun a b => (a.u == b.u && a.v == b.v) || (a.u == b.v && a.v == b.u)⟩

/-- Rust `Hash for TEdge`: hash of the ordered endpoints. -/
instance : Hashable TEdge :=
  ⟨fun e => let (f, s) := e.orderedEndpoints; mixHash (hash f) (hash s)⟩

/-- Identity of an edge inside a Rust `HashSet<TEdge>`: equal hash (bitwise equal ordered
endpoints, `f64::to_bits`) and `==`. Used to reproduce set insertion (duplicate
detection) exactly, including the `-0.0`/`0.0` distinction of the hash. -/
def sameSetKey (a b : TEdge) : Bool :=
  let (a1, a2) := a.orderedEndpoints
  let (b1, b2) := b.orderedEndpoints
  a1.x.toBits == b1.x.toBits && a1.y.toBits == b1.y.toBits &&
    a2.x.toBits == b2.x.toBits && a2.y.toBits == b2.y.toBits && a == b

/-- `HashSet<TEdge>::insert` on an insertion-ordered, duplicate-free array: appends `e`
unless an element with the same set key (`sameSetKey`) is already present. -/
def insertUnique (es : Array TEdge) (e : TEdge) : Array TEdge :=
  if es.any (sameSetKey · e) then es else es.push e

/-- `HashSet<TEdge>::extend`: `insertUnique` for every element of `more`, in order. -/
def extendUnique (es more : Array TEdge) : Array TEdge := more.foldl insertUnique es

instance : ToString TEdge := ⟨fun e => s!"{e.u}->{e.v}"⟩

end TEdge

end Elk.Alg.Common
