import Elk.Alg.Common.Polyomino.Structures.Polyomino
/-!
# `org.eclipse.elk.alg.common.polyomino` successor functions (`BiFunction` / elk-rs `successor.rs`)

A successor function maps the current candidate offset `(x, y)` and the polyomino to place
to the next candidate offset. The Rust trait takes `&mut self`; the only stateful
implementation (`SuccessorQuadrantsGeneric`) merely caches a value derived from the
polyomino, so the Lean successor functions are pure closures.
-/
namespace Elk.Alg.Common.Polyomino

/-- `SuccessorFunction<P>`: `apply(coords, poly)`. -/
abbrev SuccessorFunction (P : Type) := Int × Int → P → Int × Int

end Elk.Alg.Common.Polyomino
