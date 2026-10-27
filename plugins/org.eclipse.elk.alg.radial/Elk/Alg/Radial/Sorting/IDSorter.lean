import Elk.Graph
import Elk.Core.Util.Sort
import Elk.Alg.Radial.Options.RadialOptions
import Elk.Alg.Radial.Sorting.IRadialSorter
/-!
# `org.eclipse.elk.alg.radial.sorting.IDSorter`

Port of `id_sorter.rs` (elk-rs): sorts nodes (stably) by their `ORDER_ID` property (`0` if
unset). `initialize` does nothing.
-/
namespace Elk.Alg.Radial.Sorting

open Elk.Graph Elk.Core.Util Elk.Alg.Radial.Options

namespace IDSorter

/-- `order_id(node)`: the `ORDER_ID` property (default `0`). -/
def orderId (node : NodeId) : ElkM Int :=
  ElkM.getNodePropD node RadialOptions.ORDER_ID 0

/-- `sort(nodes)`: stable sort by `ORDER_ID` (`sort_by_key`). -/
def sort (nodes : Array NodeId) : ElkM (Array NodeId) := do
  let mut keyed : Array (Int × NodeId) := #[]
  for node in nodes do
    keyed := keyed.push (← orderId node, node)
  return (stableSort keyed (fun a b => compare a.1 b.1)).map (·.2)

/-- The `IRadialSorter` of this class. -/
def sorter : IRadialSorter where
  sort nodes := sort nodes
  init _ := pure ()

end IDSorter

end Elk.Alg.Radial.Sorting
