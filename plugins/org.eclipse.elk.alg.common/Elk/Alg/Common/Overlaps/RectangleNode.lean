import Elk.Core.Math.ElkRectangle
/-!
# `org.eclipse.elk.alg.common.overlaps.RectangleStripOverlapRemover.RectangleNode`

Java inner class of `RectangleStripOverlapRemover` (elk-rs `overlaps/mod.rs`
`RectangleNode`), in its own file because Lean modules cannot be cyclic.

Rust keeps a raw pointer to the caller's rectangle (`original_rectangle`);
the Lean port stores the index of that rectangle in the remover's
`originalRectangles` array instead (`originalIndex`).
-/
namespace Elk.Alg.Common.Overlaps

open Elk.Core.Math

/-- `RectangleNode`: a rectangle in the remover's internal coordinate system (overlaps
are removed along the y axis) and the nodes it overlaps with along the x axis. -/
structure RectangleNode where
  /-- Index of the original rectangle (Rust `original_rectangle` pointer). -/
  originalIndex : Nat
  /-- The transformed rectangle. -/
  rectangle : ElkRectangle
  /-- Indices (into the remover's sorted `rectangleNodes`) of the overlapping nodes. -/
  overlappingNodes : Array Nat := #[]
  deriving Repr, Inhabited

end Elk.Alg.Common.Overlaps
