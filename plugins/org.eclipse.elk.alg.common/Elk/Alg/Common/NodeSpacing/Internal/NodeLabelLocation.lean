import Elk.Core.Options.NodeLabelPlacement
import Elk.Core.Options.PortSide
import Elk.Alg.Common.NodeSpacing.CellSystem.ContainerArea
import Elk.Alg.Common.NodeSpacing.CellSystem.HorizontalLabelAlignment
import Elk.Alg.Common.NodeSpacing.CellSystem.VerticalLabelAlignment
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.NodeLabelLocation`

All possible node label locations with their alignments, container cell coordinates and the
`NodeLabelPlacement` sets that map to them (elk-rs `internal::NodeLabelLocation`). The Java
`null` values of `UNDEFINED` are `none`.
-/
namespace Elk.Alg.Common.NodeSpacing.Internal

open Elk Elk.Core.Options Elk.Alg.Common.NodeSpacing.CellSystem

/-- `NodeLabelLocation`: the 21 defined locations in Java declaration order plus `UNDEFINED`. -/
elk_enum NodeLabelLocation :=
  (outTL "OUT_T_L") (outTC "OUT_T_C") (outTR "OUT_T_R")
  (outBL "OUT_B_L") (outBC "OUT_B_C") (outBR "OUT_B_R")
  (outLT "OUT_L_T") (outLC "OUT_L_C") (outLB "OUT_L_B")
  (outRT "OUT_R_T") (outRC "OUT_R_C") (outRB "OUT_R_B")
  (inTL "IN_T_L") (inTC "IN_T_C") (inTR "IN_T_R")
  (inCL "IN_C_L") (inCC "IN_C_C") (inCR "IN_C_R")
  (inBL "IN_B_L") (inBC "IN_B_C") (inBR "IN_B_R")
  undefined

namespace NodeLabelLocation

/-- elk-rs `NodeLabelLocation::all_defined()`: every location except `UNDEFINED`, in order. -/
def allDefined : Array NodeLabelLocation := #[
  .outTL, .outTC, .outTR, .outBL, .outBC, .outBR,
  .outLT, .outLC, .outLB, .outRT, .outRC, .outRB,
  .inTL, .inTC, .inTR, .inCL, .inCC, .inCR, .inBL, .inBC, .inBR]

/-- `getHorizontalAlignment()` (`none` for `UNDEFINED`). -/
def horizontalAlignment : NodeLabelLocation → Option HorizontalLabelAlignment
  | .outTL | .outBL | .outRT | .outRC | .outRB | .inTL | .inCL | .inBL => some .left
  | .outTC | .outBC | .inTC | .inCC | .inBC => some .center
  | .outTR | .outBR | .outLT | .outLC | .outLB | .inTR | .inCR | .inBR => some .right
  | .undefined => none

/-- `getVerticalAlignment()` (`none` for `UNDEFINED`). -/
def verticalAlignment : NodeLabelLocation → Option VerticalLabelAlignment
  | .outBL | .outBC | .outBR | .outLT | .outRT | .inTL | .inTC | .inTR => some .top
  | .outLC | .outRC | .inCL | .inCC | .inCR => some .center
  | .outTL | .outTC | .outTR | .outLB | .outRB | .inBL | .inBC | .inBR => some .bottom
  | .undefined => none

/-- `getContainerRow()`: the row in a container cell (`none` for `UNDEFINED`). -/
def containerRow : NodeLabelLocation → Option ContainerArea
  | .outTL | .outTC | .outTR | .outLT | .outRT | .inTL | .inTC | .inTR => some .begin
  | .outLC | .outRC | .inCL | .inCC | .inCR => some .center
  | .outBL | .outBC | .outBR | .outLB | .outRB | .inBL | .inBC | .inBR => some .«end»
  | .undefined => none

/-- `getContainerColumn()`: the column in a container cell (`none` for `UNDEFINED`). -/
def containerColumn : NodeLabelLocation → Option ContainerArea
  | .outTL | .outBL | .outLT | .outLC | .outLB | .inTL | .inCL | .inBL => some .begin
  | .outTC | .outBC | .inTC | .inCC | .inBC => some .center
  | .outTR | .outBR | .outRT | .outRC | .outRB | .inTR | .inCR | .inBR => some .«end»
  | .undefined => none

/-- The `NodeLabelPlacement` sets assigned to the location (Java `assignedPlacements`). -/
def assignedPlacements : NodeLabelLocation → Array (EnumSet NodeLabelPlacement)
  | .outTL => #[EnumSet.of #[.outside, .vTop, .hLeft]]
  | .outTC => #[EnumSet.of #[.outside, .vTop, .hCenter], EnumSet.of #[.outside, .vTop, .hCenter, .hPriority]]
  | .outTR => #[EnumSet.of #[.outside, .vTop, .hRight]]
  | .outBL => #[EnumSet.of #[.outside, .vBottom, .hLeft]]
  | .outBC => #[EnumSet.of #[.outside, .vBottom, .hCenter],
      EnumSet.of #[.outside, .vBottom, .hCenter, .hPriority]]
  | .outBR => #[EnumSet.of #[.outside, .vBottom, .hRight]]
  | .outLT => #[EnumSet.of #[.outside, .hLeft, .vTop, .hPriority]]
  | .outLC => #[EnumSet.of #[.outside, .hLeft, .vCenter], EnumSet.of #[.outside, .hLeft, .vCenter, .hPriority]]
  | .outLB => #[EnumSet.of #[.outside, .hLeft, .vBottom, .hPriority]]
  | .outRT => #[EnumSet.of #[.outside, .hRight, .vTop, .hPriority]]
  | .outRC => #[EnumSet.of #[.outside, .hRight, .vCenter], EnumSet.of #[.outside, .hRight, .vCenter, .hPriority]]
  | .outRB => #[EnumSet.of #[.outside, .hRight, .vBottom, .hPriority]]
  | .inTL => #[EnumSet.of #[.inside, .vTop, .hLeft], EnumSet.of #[.inside, .vTop, .hLeft, .hPriority]]
  | .inTC => #[EnumSet.of #[.inside, .vTop, .hCenter], EnumSet.of #[.inside, .vTop, .hCenter, .hPriority]]
  | .inTR => #[EnumSet.of #[.inside, .vTop, .hRight], EnumSet.of #[.inside, .vTop, .hRight, .hPriority]]
  | .inCL => #[EnumSet.of #[.inside, .vCenter, .hLeft], EnumSet.of #[.inside, .vCenter, .hLeft, .hPriority]]
  | .inCC => #[EnumSet.of #[.inside, .vCenter, .hCenter], EnumSet.of #[.inside, .vCenter, .hCenter, .hPriority]]
  | .inCR => #[EnumSet.of #[.inside, .vCenter, .hRight], EnumSet.of #[.inside, .vCenter, .hRight, .hPriority]]
  | .inBL => #[EnumSet.of #[.inside, .vBottom, .hLeft], EnumSet.of #[.inside, .vBottom, .hLeft, .hPriority]]
  | .inBC => #[EnumSet.of #[.inside, .vBottom, .hCenter], EnumSet.of #[.inside, .vBottom, .hCenter, .hPriority]]
  | .inBR => #[EnumSet.of #[.inside, .vBottom, .hRight], EnumSet.of #[.inside, .vBottom, .hRight, .hPriority]]
  | .undefined => #[]

/-- `NodeLabelLocation.fromNodeLabelPlacement(labelPlacement)`: the first location (in
declaration order) one of whose assigned placement sets equals the given set exactly;
`UNDEFINED` if there is none. -/
def fromNodeLabelPlacement (placement : EnumSet NodeLabelPlacement) : NodeLabelLocation := Id.run do
  for location in allDefined do
    for assigned in location.assignedPlacements do
      if placement == assigned then return location
  return .undefined

/-- `isInsideLocation()`. -/
def isInsideLocation : NodeLabelLocation → Bool
  | .inTL | .inTC | .inTR | .inCL | .inCC | .inCR | .inBL | .inBC | .inBR => true
  | _ => false

/-- `getOutsideSide()`: the node side of an outside location, `UNDEFINED` for inside locations
and `UNDEFINED`. -/
def outsideSide : NodeLabelLocation → PortSide
  | .outTL | .outTC | .outTR => .north
  | .outBL | .outBC | .outBR => .south
  | .outLT | .outLC | .outLB => .west
  | .outRT | .outRC | .outRB => .east
  | _ => .undefined

end NodeLabelLocation

end Elk.Alg.Common.NodeSpacing.Internal
