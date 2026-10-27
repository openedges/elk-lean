/-!
# `org.eclipse.elk.alg.common.Tree`

A tree of `α` (elk-rs `tree.rs`): a node value and the list of subtrees.
Value based: "mutating" operations return the new tree. Subtrees are addressed
by paths of child indices (`getAt?`, `modifyAt`), which replace the Rust
pointer identity (`std::ptr::eq`) used by the consumers.
-/
namespace Elk.Alg.Common

/-- `org.eclipse.elk.alg.common.Tree<T>` (Rust `Tree<T>`). -/
structure Tree (α : Type) where
  /-- The contained node. -/
  node : α
  /-- The subtrees. -/
  children : Array (Tree α) := #[]
  deriving Inhabited

namespace Tree

variable {α : Type}

/-- `Tree::new(node)`: a leaf. -/
@[inline] def new (node : α) : Tree α := { node }

/-- A child is smaller than its parent (termination helper for the recursive traversals). -/
theorem sizeOf_lt_of_mem [SizeOf α] {t c : Tree α} (h : c ∈ t.children) : sizeOf c < sizeOf t := by
  have := Array.sizeOf_lt_of_mem h
  cases t
  simp_all
  omega

/-- Rust `Tree::add_child_to(parent, child)`: appends `child` below the first node equal to
`parent` in depth-first pre-order (the node itself first, then the subtrees in order).
Returns the new tree and whether a parent was found. -/
def addChildTo [BEq α] (t : Tree α) (parent child : α) : Tree α × Bool := Id.run do
  if t.node == parent then
    return ({ t with children := t.children.push (Tree.new child) }, true)
  let mut cs : Array (Tree α) := #[]
  let mut found := false
  for _h : c in t.children do
    if found then
      cs := cs.push c
    else
      let r := addChildTo c parent child
      cs := cs.push r.1
      found := r.2
  return ({ t with children := cs }, found)
termination_by t
decreasing_by exact sizeOf_lt_of_mem ‹_›

/-- Rust derived `PartialEq for Tree<T>`: structural equality. -/
def beq [BEq α] (a b : Tree α) : Bool := Id.run do
  if !(a.node == b.node) || a.children.size != b.children.size then return false
  let mut i := 0
  for h : x in a.children do
    match b.children[i]? with
    | some y => if !beq x y then return false
    | none => return false
    i := i + 1
  return true
termination_by a
decreasing_by exact sizeOf_lt_of_mem ‹_›

instance [BEq α] : BEq (Tree α) := ⟨beq⟩

/-- Number of nodes in the tree. -/
def size (t : Tree α) : Nat := t.children.foldl (fun acc c => acc + size c) 1
termination_by t
decreasing_by exact sizeOf_lt_of_mem ‹_›

/-- Node values in depth-first pre-order. -/
def preorder (t : Tree α) : Array α := Id.run do
  let mut out := #[t.node]
  for _h : c in t.children do
    out := out ++ preorder c
  return out
termination_by t
decreasing_by exact sizeOf_lt_of_mem ‹_›

/-- The subtree at `path` (child indices from the root), if any. -/
def getAt? (t : Tree α) : List Nat → Option (Tree α)
  | [] => some t
  | i :: rest =>
    match t.children[i]? with
    | some c => getAt? c rest
    | none => none

/-- Applies `f` to the subtree at `path` (child indices from the root); no-op if the path
does not exist. -/
def modifyAt (t : Tree α) (path : List Nat) (f : Tree α → Tree α) : Tree α :=
  match path with
  | [] => f t
  | i :: rest =>
    if h : i < t.children.size then
      { t with children := t.children.set i (modifyAt t.children[i] rest f) }
    else t

end Tree

end Elk.Alg.Common
