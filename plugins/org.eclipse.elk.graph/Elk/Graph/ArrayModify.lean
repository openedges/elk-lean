/-!
# `Array.modifyIn`: `Array.modify` with in-place element updates

`Array.modify` clears the array slot before it applies the update, so that the element is unshared
and a `{ v with … }` update can reuse its object. With Lean 4.35, when the update is a straight-line
lambda inlined into `modify` (the usual `modifyNode n fun nd => { nd with … }`), the compiler reads
the element's fields and tests its exclusivity *before* the slot is cleared, while the array still
references the element: the reuse always fails and every update allocates a fresh object (and
frees the old one). `modifyIn` re-checks the bounds after clearing the slot and applies the update
inside that branch, which keeps the clear before the test (verified on the generated C: the
`lean_array_fset` of the dummy precedes `lean_is_exclusive`; see `PLAN.md` 7.1). Updates that
branch themselves were already compiled in the right order; non-inlined updaters as well.
-/
namespace Array

/-- `Array.modify` whose update runs on the unshared element even when it is inlined (see the
module doc). The index must be in range, like `modify` the array is unchanged otherwise. -/
@[inline] def modifyIn {α : Type} [Inhabited α] (a : Array α) (i : Nat) (f : α → α) : Array α :=
  if h : i < a.size then
    let v := a[i]
    let a := a.set i default
    -- the bounds re-check is the barrier: the update's field reads and exclusivity test stay
    -- below the slot clear
    if h' : i < a.size then a.set i (f v) else a
  else a

end Array
