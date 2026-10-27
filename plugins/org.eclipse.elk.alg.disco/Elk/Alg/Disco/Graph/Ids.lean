import Elk.Core.Util.FastFloat
/-!
# Arena identifiers of the DisCo graph (`org.eclipse.elk.alg.disco.graph`)

The Rust port holds `DCElement`s and `DCComponent`s in `Arc<Mutex<_>>` with `Weak` back
references (`DCElement.component`). The Lean port stores them in the arrays of `DCGraph` and
references them by typed index (PORTING.md, section 14): `Arc::ptr_eq` becomes `==` on the ids.
-/
namespace Elk.Alg.Disco.Graph

/-- Index of a `DCElement` in `DCGraph.elements`. -/
structure DCElementId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

/-- Index of a `DCComponent` in `DCGraph.components`. -/
structure DCComponentId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

end Elk.Alg.Disco.Graph
