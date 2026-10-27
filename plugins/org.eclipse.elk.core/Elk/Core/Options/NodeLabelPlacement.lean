import Elk.Graph.Enum
/-!
# `org.eclipse.elk.core.options.NodeLabelPlacement`
-/
namespace Elk.Core.Options

/-- `org.eclipse.elk.core.options.NodeLabelPlacement`. -/
elk_enum NodeLabelPlacement := hLeft hCenter hRight vTop vCenter vBottom inside outside hPriority

namespace NodeLabelPlacement

/-- `NodeLabelPlacement.valueOf(index)` by ordinal (`none` when out of range instead of a panic). -/
def valueOf (index : Nat) : Option NodeLabelPlacement := ElkEnum.ofOrdinal? index

/-- `NodeLabelPlacement.fixed()`: the empty set. -/
def fixed : EnumSet NodeLabelPlacement := EnumSet.noneOf

/-- `NodeLabelPlacement.insideTopLeft()`. -/
def insideTopLeft : EnumSet NodeLabelPlacement := EnumSet.of #[.inside, .vTop, .hLeft]
/-- `NodeLabelPlacement.insideTopCenter()`. -/
def insideTopCenter : EnumSet NodeLabelPlacement := EnumSet.of #[.inside, .vTop, .hCenter]
/-- `NodeLabelPlacement.insideTopRight()`. -/
def insideTopRight : EnumSet NodeLabelPlacement := EnumSet.of #[.inside, .vTop, .hRight]
/-- `NodeLabelPlacement.insideCenter()`. -/
def insideCenter : EnumSet NodeLabelPlacement := EnumSet.of #[.inside, .vCenter, .hCenter]
/-- `NodeLabelPlacement.insideBottomLeft()`. -/
def insideBottomLeft : EnumSet NodeLabelPlacement := EnumSet.of #[.inside, .vBottom, .hLeft]
/-- `NodeLabelPlacement.insideBottomCenter()`. -/
def insideBottomCenter : EnumSet NodeLabelPlacement := EnumSet.of #[.inside, .vBottom, .hCenter]
/-- `NodeLabelPlacement.insideBottomRight()`. -/
def insideBottomRight : EnumSet NodeLabelPlacement := EnumSet.of #[.inside, .vBottom, .hRight]
/-- `NodeLabelPlacement.outsideTopLeft()`. -/
def outsideTopLeft : EnumSet NodeLabelPlacement := EnumSet.of #[.outside, .vTop, .hLeft]
/-- `NodeLabelPlacement.outsideTopCenter()`. -/
def outsideTopCenter : EnumSet NodeLabelPlacement := EnumSet.of #[.outside, .vTop, .hCenter]
/-- `NodeLabelPlacement.outsideTopRight()`. -/
def outsideTopRight : EnumSet NodeLabelPlacement := EnumSet.of #[.outside, .vTop, .hRight]
/-- `NodeLabelPlacement.outsideBottomLeft()`. -/
def outsideBottomLeft : EnumSet NodeLabelPlacement := EnumSet.of #[.outside, .vBottom, .hLeft]
/-- `NodeLabelPlacement.outsideBottomCenter()`. -/
def outsideBottomCenter : EnumSet NodeLabelPlacement := EnumSet.of #[.outside, .vBottom, .hCenter]
/-- `NodeLabelPlacement.outsideBottomRight()`. -/
def outsideBottomRight : EnumSet NodeLabelPlacement := EnumSet.of #[.outside, .vBottom, .hRight]

/-- Number of candidates contained in `set` (private helper of `isValid`). -/
private def countMembers (set : EnumSet NodeLabelPlacement) (candidates : Array NodeLabelPlacement) : Nat :=
  (candidates.filter fun c => set.contains c).size

/-- `NodeLabelPlacement.isValid(placement)`: at most one of inside/outside, one horizontal
and one vertical constant. -/
def isValid (placement : EnumSet NodeLabelPlacement) : Bool :=
  if countMembers placement #[.inside, .outside] > 1 then false
  else if countMembers placement #[.hLeft, .hCenter, .hRight] > 1 then false
  else if countMembers placement #[.vTop, .vCenter, .vBottom] > 1 then false
  else true

end NodeLabelPlacement

end Elk.Core.Options
