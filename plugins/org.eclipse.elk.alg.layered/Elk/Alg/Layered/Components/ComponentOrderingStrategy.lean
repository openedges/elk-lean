import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.components.ComponentOrderingStrategy`

Port of `components/component_ordering_strategy.rs` (elk-rs) and `ComponentOrderingStrategy.java`.
-/
namespace Elk.Alg.Layered.Components

/-- `org.eclipse.elk.alg.layered.components.ComponentOrderingStrategy`: Strategy to order components
by model order. -/
elk_enum ComponentOrderingStrategy := none insidePortSideGroups groupModelOrder modelOrder

end Elk.Alg.Layered.Components
