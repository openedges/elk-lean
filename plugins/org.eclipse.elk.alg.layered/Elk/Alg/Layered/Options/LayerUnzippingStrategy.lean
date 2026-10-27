import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.LayerUnzippingStrategy`

Port of `options/layer_unzipping_strategy.rs` (elk-rs) and `LayerUnzippingStrategy.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.LayerUnzippingStrategy`: Strategies for unzipping layers
i.e. splitting up nodes into multiple layers to create more compact drawings. -/
elk_enum LayerUnzippingStrategy := none alternating

end Elk.Alg.Layered.Options
