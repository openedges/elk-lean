import Elk.Graph
/-!
# Typed ids of the layered graph arena

All elements of all (nested) `LGraph`s of one layered run live in one `LGraphArena`
(see `PORTING.md` §15); these ids index its arrays. They replace the Rust
`Arc<Mutex<LNode>>`/`Weak` references (`Arc::ptr_eq` → `==`).
-/
namespace Elk.Alg.Layered.Graph

/-- Index of an `LGraph` in the arena. -/
structure LGraphId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of an `LNode` in the arena. -/
structure LNodeId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of an `LPort` in the arena. -/
structure LPortId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of an `LEdge` in the arena. -/
structure LEdgeId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of an `LLabel` in the arena. -/
structure LLabelId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

/-- Index of a `Layer` in the arena. -/
structure LayerId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Ord

instance : ToString LGraphId := ⟨fun i => s!"G{i.idx}"⟩
instance : ToString LNodeId := ⟨fun i => s!"N{i.idx}"⟩
instance : ToString LPortId := ⟨fun i => s!"P{i.idx}"⟩
instance : ToString LEdgeId := ⟨fun i => s!"E{i.idx}"⟩
instance : ToString LLabelId := ⟨fun i => s!"L{i.idx}"⟩
instance : ToString LayerId := ⟨fun i => s!"Layer{i.idx}"⟩

end Elk.Alg.Layered.Graph
