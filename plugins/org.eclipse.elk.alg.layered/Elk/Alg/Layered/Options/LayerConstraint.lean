import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.LayerConstraint`

Port of `options/layer_constraint.rs` (elk-rs) and `LayerConstraint.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.LayerConstraint`: Enumeration of layer constraint types.
May be set on nodes to constrain in which layer they may appear. -/
elk_enum LayerConstraint := none first firstSeparate last lastSeparate

end Elk.Alg.Layered.Options
