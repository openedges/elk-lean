namespace Elk.Graph
structure NodeId where
  idx : Nat
  deriving BEq, Hashable, Repr, Inhabited
end Elk.Graph
