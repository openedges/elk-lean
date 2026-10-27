import Elk.Graph
/-!
# `org.eclipse.elk.alg.mrtree.graph.TGraphElement`

Port of `graph/t_graph_element.rs` (elk-rs): the base of all tree graph elements, an integer
identifier (`id`, Rust `i32`, default 0) plus a property holder. As described in `PORTING.md`
section 14, the tree graph is an arena (`Elk.Alg.MrTree.Graph.TArena`) whose elements are referenced
by the typed ids declared here; Rust's `Arc<Mutex<_>>`/`Weak` references and `Arc::ptr_eq` become ids
and `==`. The property holder only carries the public layout options (copied from the `ElkGraph`);
the internal properties are typed fields (see `Elk.Alg.MrTree.Options.InternalProperties`).
-/
namespace Elk.Alg.MrTree.Graph

open Elk.Graph

/-- Index of a `TGraph` in `TArena.graphs`. -/
structure TGraphId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of a `TNode` in `TArena.nodes`. -/
structure TNodeId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of a `TEdge` in `TArena.edges`. -/
structure TEdgeId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of a `TLabel` in `TArena.labels`. -/
structure TLabelId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

instance : ToString TGraphId := ⟨fun i => s!"TG{i.idx}"⟩
instance : ToString TNodeId := ⟨fun i => s!"TN{i.idx}"⟩
instance : ToString TEdgeId := ⟨fun i => s!"TE{i.idx}"⟩
instance : ToString TLabelId := ⟨fun i => s!"TL{i.idx}"⟩

/-- `org.eclipse.elk.alg.mrtree.graph.TGraphElement`: identifier and public properties. -/
structure TGraphElement where
  /-- `id` (Rust `i32`). -/
  id : Int := 0
  /-- The `MapPropertyHolder` (public layout options only). -/
  props : PropertyMap := {}
  deriving Inhabited

end Elk.Alg.MrTree.Graph
