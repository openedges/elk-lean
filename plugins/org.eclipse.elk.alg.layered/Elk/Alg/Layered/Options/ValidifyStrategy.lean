import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.ValidifyStrategy`

Port of `options/validify_strategy.rs` (elk-rs) and `ValidifyStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.ValidifyStrategy`: The cuts calculated by a
`ICutIndexCalculator` are not necessarily valid (when using `WrappingStrategy#SINGLE_EDGE`). The
specified 'validify' takes care of transforming forbidden cuts into valid ones. -/
elk_enum ValidifyStrategy := no greedy lookBack

end Elk.Alg.Layered.Options
