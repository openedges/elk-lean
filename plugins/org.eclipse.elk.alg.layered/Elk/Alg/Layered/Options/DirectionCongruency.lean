import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.layered.options.DirectionCongruency`

Port of `options/direction_congruency.rs` (elk-rs) and `DirectionCongruency.java`.
-/
namespace Elk.Alg.Layered.Options

/-- `org.eclipse.elk.alg.layered.options.DirectionCongruency`: Enumeration that allows to specify
how drawings of the same graph with different layout directions compare to each other: either a
natural reading direction is preserved or the drawings are rotated versions of each other. -/
elk_enum DirectionCongruency := readingDirection rotation

end Elk.Alg.Layered.Options
