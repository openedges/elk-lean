import Elk.Graph.Enum
/-!
# `org.eclipse.elk.core.options.SizeOptions`
-/
namespace Elk.Core.Options

/-- `org.eclipse.elk.core.options.SizeOptions`. -/
elk_enum SizeOptions :=
  defaultMinimumSize minimumSizeAccountsForPadding computePadding outsideNodeLabelsOverhang
  portsOverhang uniformPortSpacing spaceEfficientPortLabels forceTabularNodeLabels asymmetrical

namespace SizeOptions

/-- `SizeOptions.valueOf(index)` by ordinal (`none` when out of range instead of a panic). -/
def valueOf (index : Nat) : Option SizeOptions := ElkEnum.ofOrdinal? index

end SizeOptions

end Elk.Core.Options
