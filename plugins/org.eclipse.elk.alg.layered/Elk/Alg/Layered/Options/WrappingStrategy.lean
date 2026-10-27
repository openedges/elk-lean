import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.WrappingStrategy`

Port of `options/wrapping_strategy.rs` (elk-rs) and `WrappingStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.WrappingStrategy`: Specifies the desired strategy to wrap
graphs in order to improve their presentation within a drawing area of a certain aspect ratio. I.e.
the graph is split into several chunks to better utilize the given area. -/
elk_enum WrappingStrategy := off singleEdge multiEdge

end Elk.Alg.Layered.Options
