import Elk.Graph.Enum
/-!
# `org.eclipse.elk.core.options.SizeConstraint`

Deviation: the Java static `minimumSize()` is named `minimumSizeSet` here
because `SizeConstraint.minimumSize` is already the enum constant `MINIMUM_SIZE`.
-/
namespace Elk.Core.Options

/-- `org.eclipse.elk.core.options.SizeConstraint`. -/
elk_enum SizeConstraint := ports portLabels nodeLabels minimumSize

namespace SizeConstraint

/-- `SizeConstraint.fixed()`: the empty set. -/
def fixed : EnumSet SizeConstraint := EnumSet.noneOf

/-- `SizeConstraint.minimumSize()` (renamed, see module doc). -/
def minimumSizeSet : EnumSet SizeConstraint := EnumSet.of #[.minimumSize]

/-- `SizeConstraint.minimumSizeWithPorts()`. -/
def minimumSizeWithPorts : EnumSet SizeConstraint := EnumSet.of #[.ports, .minimumSize]

/-- `SizeConstraint.free()`: all constants. -/
def free : EnumSet SizeConstraint := EnumSet.allOf

end SizeConstraint

end Elk.Core.Options
