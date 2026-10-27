import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.spore.options.RootSelection`

Port of `options/root_selection.rs` (elk-rs) and `RootSelection.java`.
-/
namespace Elk.Alg.Spore.Options

/-- `org.eclipse.elk.alg.spore.options.RootSelection`: the method used to select a root node for the
construction of a spanning tree: the node with the preferred identifier (`FIXED`) or the node
closest to the center of the graph (`CENTER_NODE`). -/
elk_enum RootSelection := fixed centerNode

end Elk.Alg.Spore.Options
