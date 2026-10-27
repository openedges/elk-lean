import Elk.Graph.Enum
/-!
# `org.eclipse.elk.core.options.PortLabelPlacement`

Deviation: the Java statics `inside()` / `outside()` are named `insideSet` /
`outsideSet` here because `PortLabelPlacement.inside` / `.outside` are the enum constants.
-/
namespace Elk.Core.Options

/-- `org.eclipse.elk.core.options.PortLabelPlacement`. -/
elk_enum PortLabelPlacement :=
  outside inside nextToPortIfPossible alwaysSameSide alwaysOtherSameSide spaceEfficient

namespace PortLabelPlacement

/-- `PortLabelPlacement.fixed()`: the empty set. -/
def fixed : EnumSet PortLabelPlacement := EnumSet.noneOf

/-- `PortLabelPlacement.inside()` (renamed, see module doc). -/
def insideSet : EnumSet PortLabelPlacement := EnumSet.of #[.inside]

/-- `PortLabelPlacement.outside()` (renamed, see module doc). -/
def outsideSet : EnumSet PortLabelPlacement := EnumSet.of #[.outside]

/-- `PortLabelPlacement.isFixed(placement)`. -/
def isFixed (placement : EnumSet PortLabelPlacement) : Bool :=
  !placement.contains .inside && !placement.contains .outside

/-- Number of candidates contained in `set` (private helper of `isValid`). -/
private def countMembers (set : EnumSet PortLabelPlacement) (candidates : Array PortLabelPlacement) : Nat :=
  (candidates.filter fun c => set.contains c).size

/-- `PortLabelPlacement.isValid(placement)`. -/
def isValid (placement : EnumSet PortLabelPlacement) : Bool :=
  if countMembers placement #[.inside, .outside] > 1 then false
  else if countMembers placement #[.alwaysSameSide, .alwaysOtherSameSide, .spaceEfficient] > 1 then false
  else true

end PortLabelPlacement

end Elk.Core.Options
