import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.mrtree.options.GraphProperties`

Port of `options/graph_properties.rs` (elk-rs) and `GraphProperties.java` (same constants, same ordinal order).
-/
namespace Elk.Alg.MrTree.Options

/-- `org.eclipse.elk.alg.mrtree.options.GraphProperties`: properties of the graph that can be used to skip processing steps (an `EnumSet` option). -/
elk_enum GraphProperties := selfLoops

end Elk.Alg.MrTree.Options
