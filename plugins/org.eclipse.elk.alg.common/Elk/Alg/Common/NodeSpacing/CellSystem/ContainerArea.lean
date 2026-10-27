import Elk.Graph.Enum
/-!
# `org.eclipse.elk.alg.common.nodespacing.cellsystem.ContainerArea`

The three areas of a container cell along one axis (elk-rs `cellsystem::ContainerArea`).
`END` is a Lean keyword, so the constant is spelled `«end»`.
-/
namespace Elk.Alg.Common.NodeSpacing.CellSystem

/-- `ContainerArea`: `BEGIN`, `CENTER`, `END` (the ordinal is the slot index in container cells). -/
elk_enum ContainerArea := begin center («end» "END")

namespace ContainerArea

/-- `ContainerArea.values()` (elk-rs `ContainerArea::VALUES`). -/
def values : Array ContainerArea := #[.begin, .center, .«end»]

/-- elk-rs `ContainerArea::index()` = Java `ordinal()`. -/
@[inline] def index (a : ContainerArea) : Nat := Elk.ElkEnum.ordinal a

end ContainerArea

end Elk.Alg.Common.NodeSpacing.CellSystem
