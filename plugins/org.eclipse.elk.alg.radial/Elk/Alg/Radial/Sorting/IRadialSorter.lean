import Elk.Graph
import Elk.Alg.Radial.InternalProperties
/-!
# `org.eclipse.elk.alg.radial.sorting.IRadialSorter`

Port of `i_radial_sorter.rs` (elk-rs). The Rust trait objects are stateful (`&mut self`); the
Lean sorters are records of closures that capture their mutable state in an `IO.Ref` created
by the factory (`SortingStrategy.create`), so a sorter handle can be shared by the recursive
compaction code like a `Box<dyn IRadialSorter>`.
-/
namespace Elk.Alg.Radial.Sorting

open Elk.Graph

/-- `IRadialSorter`. -/
structure IRadialSorter where
  /-- `sort(nodes)`: returns the sorted nodes. -/
  sort : Array NodeId → RadialM (Array NodeId)
  /-- `initialize(root)` (`initialize` is a Lean keyword). -/
  init : NodeId → RadialM Unit
  /-- `sort_for_parent(nodes, parent, root, is_root_level)`: sorts the successors of a parent
  directly. The default (the trait default of Rust) is `init(root)` (Rust `initialize`) followed by `sort`. -/
  sortForParent : Array NodeId → NodeId → NodeId → Bool → RadialM (Array NodeId) :=
    fun nodes _ root _ => do
      init root
      sort nodes

end Elk.Alg.Radial.Sorting
