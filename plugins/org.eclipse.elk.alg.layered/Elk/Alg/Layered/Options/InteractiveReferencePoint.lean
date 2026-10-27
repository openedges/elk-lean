import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.InteractiveReferencePoint`

Port of `options/interactive_reference_point.rs` (elk-rs) and `InteractiveReferencePoint.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.InteractiveReferencePoint`: Describes what interactive
layout phases should take as reference point for comparison of node positions. -/
elk_enum InteractiveReferencePoint := center topLeft

end Elk.Alg.Layered.Options
