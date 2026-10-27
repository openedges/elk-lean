import Elk.Graph.Enum
/-!
# `org.eclipse.elk.core.options.PortAlignment`

`END` is a Lean keyword, so the constant is spelled `«end»`.
-/
namespace Elk.Core.Options

/-- `org.eclipse.elk.core.options.PortAlignment`. -/
elk_enum PortAlignment := distributed justified begin center («end» "END")

end Elk.Core.Options
