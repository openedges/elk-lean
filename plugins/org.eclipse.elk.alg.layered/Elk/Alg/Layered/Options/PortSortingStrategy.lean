import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.PortSortingStrategy`

Port of `options/port_sorting_strategy.rs` (elk-rs) and `PortSortingStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.PortSortingStrategy`: Strategy with which a node's ports
are ordered by the `PortListSorter`. Only relevant if the node's `PortConstraints` are
`PortConstraints#FIXED_SIDE`. -/
elk_enum PortSortingStrategy := inputOrder portDegree

end Elk.Alg.Layered.Options
