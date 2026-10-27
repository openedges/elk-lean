import Elk.Core.Util.FastFloat
/-!
# `org.eclipse.elk.alg.common.utils.UniqueTriple`

A triple of values (elk-rs `utils/unique_triple.rs`). "Unique" refers to Java's
identity semantics: neither Java nor Rust define value equality, so no `BEq`
instance is provided.
-/
namespace Elk.Alg.Common.Utils

/-- `org.eclipse.elk.alg.common.utils.UniqueTriple<F, S, T>`. -/
structure UniqueTriple (φ σ τ : Type) where
  /-- The first element. -/
  first : φ
  /-- The second element. -/
  second : σ
  /-- The third element. -/
  third : τ
  deriving Repr, Inhabited

namespace UniqueTriple

/-- `UniqueTriple::new(first, second, third)`. -/
@[inline] def new {φ σ τ : Type} (first : φ) (second : σ) (third : τ) : UniqueTriple φ σ τ :=
  ⟨first, second, third⟩

/-- Rust `Display`: `(first, second, third)`. -/
instance {φ σ τ : Type} [ToString φ] [ToString σ] [ToString τ] : ToString (UniqueTriple φ σ τ) :=
  ⟨fun t => s!"({t.first}, {t.second}, {t.third})"⟩

end UniqueTriple

end Elk.Alg.Common.Utils
