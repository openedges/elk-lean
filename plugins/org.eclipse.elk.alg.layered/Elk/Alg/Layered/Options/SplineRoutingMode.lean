import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.SplineRoutingMode`

Port of `options/spline_routing_mode.rs` (elk-rs) and `SplineRoutingMode.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.SplineRoutingMode`: Specifies the strategy to be used for
creating spline edge routes. -/
elk_enum SplineRoutingMode := conservative conservativeSoft sloppy

end Elk.Alg.Layered.Options
