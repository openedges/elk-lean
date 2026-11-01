import Elk.Core.Util.Java
import Elk.Alg.Common.NodeSpacing.Internal.Algorithm.HorizontalPortPlacementSizeCalculator
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.alg.common.nodespacing.internal.algorithm.VerticalPortPlacementSizeCalculator`

Calculates the space required to set up the vertical (eastern and western) port placements
(elk-rs `internal::algorithm::VerticalPortPlacementSizeCalculator`, PHASE 3 of the node size
calculation). The result is written to the side's inside port label cell: its top/bottom padding
and the height of its minimum content area. With `SizeConstraint.PORT_LABELS`, the port margins
are set up first so that they include the space needed by the port labels.

Inside port label cells: Java has one `AtomicCell` per side, shared by
`NodeContext.insidePortLabelCells` and the node container's middle row (`BEGIN` = WEST,
`END` = EAST). elk-rs holds two copies and updates both; in the Lean arena both refer to the same
cell, which is updated once (`updateInsidePortLabelCells`).

Deviations from Java (following elk-rs): see `HorizontalPortPlacementSizeCalculator` (fixed
ratios read `PortContext.portRatioOrPosition`, margins set up once, `fmax`). The first label's
height is the size recorded in the label cell (Java re-reads `label.getSize()`; label sizes do not
change during the calculation).
-/

namespace Elk.Alg.Common.NodeSpacing.Internal.Algorithm

open Elk Elk.Core.Math Elk.Core.Util Elk.Core.Options
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal

namespace VerticalPortPlacementSizeCalculator

variable {N P L : Type}

open HorizontalPortPlacementSizeCalculator (minSizeRequiredToRespectSpacing)

/-- Applies `f` to the side's inside port label cell (Java `insidePortLabelCells.get(portSide)`)
and to the atomic cell in the middle row's `BEGIN` (WEST) / `END` (EAST) area. elk-rs updates
both of its copies; when both ids denote the same arena cell (the normal case) the update is
applied once. Other sides are ignored. -/
@[inline] private def updateInsidePortLabelCells (ctx : NodeContext N P L) (portSide : PortSide)
    (f : CellArena L → CellId → CellArena L) : NodeContext N P L :=
  let area? : Option ContainerArea := match portSide with
    | .east => some .«end»
    | .west => some .begin
    | _ => none
  match area? with
  | none => ctx
  | some area =>
    let insideCell := ctx.insidePortLabelCell portSide
    let containerCell := (ctx.cells.getCell ctx.nodeContainerMiddleRow area).filter ctx.cells.isAtomic
    -- the arena is taken out of the context first so that it is updated in place
    ctx.modifyCells fun cells =>
      let cells := match insideCell with
        | some c => f cells c
        | none => cells
      match containerCell with
      | some c => if insideCell == some c then cells else f cells c
      | none => cells

/-! ### Fixed position -/

/-- `calculateVerticalNodeSizeRequiredByFixedPosPorts(nodeContext, portSide)`: the cell's content
height is the bottommost port border; the top padding is removed. -/
private def calculateVerticalNodeSizeRequiredByFixedPosPorts (ctx : NodeContext N P L) (portSide : PortSide) :
    NodeContext N P L :=
  let bottommostPortBorder := (ctx.portContextsOf portSide).foldl
    (fun m pc => fmax m (pc.portPosition.y + pc.portSize.y)) 0.0
  -- Set the cell size and remove the top padding
  updateInsidePortLabelCells ctx portSide fun cs c =>
    (cs.modifyPadding c fun p => { p with top := 0.0 }).modifyMinimumContentAreaSize c
      fun s => { s with y := bottommostPortBorder }

/-! ### Port margins -/

/-- The body of the `computeVerticalPortMargins` loop for one port context: the new port
margin. -/
private def verticalPortMargin (cells : CellArena L) (isFixed : Bool) (portLabelSpacingV : Float)
    (portLabelsTreatAsGroup : Bool) (pc : PortContext P L) : ElkMargin := Id.run do
  let mut margin := pc.portMargin
  let labelHeight := match pc.portLabelCell with
    | some c => cells.minimumHeight c
    | none => fl0p0
  if labelHeight > fl0p0 then
    if pc.labelsNextToPort then
      -- The label is placed next to the port
      let portHeight := pc.portSize.y
      if labelHeight > portHeight then
        let labels := match pc.portLabelCell with
          | some c => cells.labels c
          | none => #[]
        if portLabelsTreatAsGroup || labels.size == 1 then
          -- Center all labels
          let overhang := (labelHeight - portHeight) / fl2p0
          margin := { margin with top := overhang, bottom := overhang }
        else
          -- Simulate centering the first port label
          let firstLabelHeight := (labels[0]?.map (·.2.y)).getD fl0p0
          let firstLabelOverhang := (firstLabelHeight - portHeight) / fl2p0
          margin := { margin with top := fmax fl0p0 firstLabelOverhang }
          margin := { margin with bottom := labelHeight - firstLabelOverhang - portHeight }
    else
      -- Label placed below the port
      margin := { margin with bottom := portLabelSpacingV + labelHeight }
  else if isFixed then
    -- Fixed labels are not in the label cell: use their bounds
    let labelsBounds := pc.getLabelsBounds
    if labelsBounds.y < fl0p0 then
      margin := { margin with top := -labelsBounds.y }
    if labelsBounds.y + labelsBounds.height > pc.portSize.y then
      margin := { margin with bottom := labelsBounds.y + labelsBounds.height - pc.portSize.y }
  return margin

/-- `computeVerticalPortMargins(nodeContext, portSide, portLabelsOutside)`: sets the vertical
margins of the side's ports to include the space of their labels. Labels next to the port are
centered as a group (or if there is a single label); otherwise the first label is centered on
the port and the others hang below. Labels not next to the port are placed below it; fixed
labels are measured by their bounds. -/
private def computeVerticalPortMargins (ctx : NodeContext N P L) (portSide : PortSide)
    (_portLabelsOutside : Bool) : NodeContext N P L :=
  let isFixed := PortLabelPlacement.isFixed ctx.portLabelsPlacement
  let portLabelSpacingV := ctx.portLabelSpacingVertical
  let portLabelsTreatAsGroup := ctx.portLabelsTreatAsGroup
  let cells := ctx.cells
  ctx.modifyPortContextsOf portSide fun pcs => pcs.map fun pc =>
    let m := verticalPortMargin cells isFixed portLabelSpacingV portLabelsTreatAsGroup pc
    pc.withPortMargin m

/-- `unifyPortMargins(portContexts)`: sets every top/bottom margin to the maximum one. -/
private def unifyPortMargins (pcs : Array (PortContext P L)) : Array (PortContext P L) :=
  let maxTop := pcs.foldl (fun m pc => fmax m pc.portMargin.top) 0.0
  let maxBottom := pcs.foldl (fun m pc => fmax m pc.portMargin.bottom) 0.0
  pcs.map (·.withMarginTopBottom maxTop maxBottom)

/-- Sets the top margin of the first and the bottom margin of the last context to `0`. -/
private def clearOuterMargins (pcs : Array (PortContext P L)) : Array (PortContext P L) :=
  if pcs.isEmpty then pcs
  else
    let pcs := pcs.modify 0 (·.withMarginTop fl0p0)
    pcs.modify (pcs.size - 1) (·.withMarginBottom fl0p0)

/-- `setupPortMargins(nodeContext, portSide)`: port margins including the label space, subject to
the outside / space-efficient / uniform port spacing options. -/
private def setupPortMargins (ctx : NodeContext N P L) (portSide : PortSide) : NodeContext N P L :=
  let portLabelsOutside := ctx.portLabelsPlacement.contains .outside
  let alwaysSameSide := ctx.portLabelsPlacement.contains .alwaysSameSide
  let alwaysSameSideAbove := ctx.portLabelsPlacement.contains .alwaysOtherSameSide
  let spaceEfficient := ctx.portLabelsPlacement.contains .spaceEfficient
  let uniformPortSpacing := ctx.sizeOptions.contains .uniformPortSpacing
  let portCount := (ctx.portContextsOf portSide).size
  let spaceEfficientPortLabels := !alwaysSameSide && !alwaysSameSideAbove && (spaceEfficient || portCount == 2)
  -- Set the vertical port margins
  let ctx := computeVerticalPortMargins ctx portSide portLabelsOutside
  let ctx := if portLabelsOutside then
      ctx.modifyPortContextsOf portSide fun pcs =>
        -- The topmost port doesn't need a top margin, the bottommost doesn't need a bottom margin
        let pcs := clearOuterMargins pcs
        -- Space-efficient: the topmost port doesn't need a bottom margin if its label is not next to it
        match pcs[0]? with
        | some first =>
          if spaceEfficientPortLabels && !first.labelsNextToPort then
            pcs.modify 0 (·.withMarginBottom fl0p0)
          else pcs
        | none => pcs
    else ctx
  if uniformPortSpacing then
    ctx.modifyPortContextsOf portSide fun pcs =>
      let pcs := unifyPortMargins pcs
      if portLabelsOutside then clearOuterMargins pcs else pcs
  else ctx

/-- `portHeightPlusPortPortSpacing(nodeContext, portSide)`: the sum of the port heights
including their margins, with a port-port spacing between consecutive ports. -/
private def portHeightPlusPortPortSpacing (ctx : NodeContext N P L) (portSide : PortSide) : Float := Id.run do
  let pcs := ctx.portContextsOf portSide
  let mut result := 0.0
  let mut i := 0
  for pc in pcs do
    result := result + (pc.portMargin.top + pc.portSize.y + pc.portMargin.bottom)
    if i + 1 < pcs.size then
      result := result + ctx.portPortSpacing
    i := i + 1
  return result

/-! ### Fixed ratio and free placement -/

/-- `calculateVerticalNodeSizeRequiredByFixedRatioPorts(nodeContext, portSide)`: the minimum
height such that consecutive ports (and the surrounding port margins) keep their spacing at the
ports' position ratios; the top padding is removed. Without ports, the top/bottom padding is
cleared. -/
private def calculateVerticalNodeSizeRequiredByFixedRatioPorts (ctx : NodeContext N P L) (portSide : PortSide) :
    NodeContext N P L := Id.run do
  if (ctx.portContextsOf portSide).isEmpty then
    return updateInsidePortLabelCells ctx portSide fun cs c =>
      cs.modifyPadding c fun p => { p with top := fl0p0, bottom := fl0p0 }
  let portLabelsInside := ctx.portLabelsPlacement.contains .inside
  let mut ctx := ctx
  if ctx.sizeConstraints.contains .portLabels then
    ctx := setupPortMargins ctx portSide
  let mut minHeight := fl0p0
  let surroundingTop := ctx.surroundingPortMargins.top
  let surroundingBottom := ctx.surroundingPortMargins.bottom
  let portPortSpacing := ctx.portPortSpacing
  -- (ratio, height, bottom margin) of the previous port
  let mut previous : Option (Float × Float × Float) := none
  for pc in ctx.portContextsOf portSide do
    let ratio := pc.portRatioOrPosition
    match previous with
    | some (prevRatio, prevHeight, prevMarginBottom) =>
      let requiredSpace := prevHeight + prevMarginBottom + portPortSpacing + pc.portMargin.top
      minHeight := fmax minHeight (minSizeRequiredToRespectSpacing requiredSpace prevRatio ratio)
    | none =>
      -- First port: respect the top surrounding port margin
      if surroundingTop > fl0p0 then
        minHeight := fmax minHeight (minSizeRequiredToRespectSpacing (surroundingTop + pc.portMargin.top) fl0p0 ratio)
    previous := some (ratio, pc.portSize.y, pc.portMargin.bottom)
  -- Bottom surrounding port margin
  if let some (prevRatio, prevHeight, prevMarginBottom) := previous then
    if surroundingBottom > fl0p0 then
      let mut requiredSpace := prevHeight + surroundingBottom
      if portLabelsInside then
        requiredSpace := requiredSpace + prevMarginBottom
      minHeight := fmax minHeight (minSizeRequiredToRespectSpacing requiredSpace prevRatio fl1p0)
  -- Set the cell size and remove the top padding
  return updateInsidePortLabelCells ctx portSide fun cs c =>
    (cs.modifyPadding c fun p => { p with top := fl0p0 }).modifyMinimumContentAreaSize c
      fun s => { s with y := minHeight }

/-- `calculateVerticalNodeSizeRequiredByFreePorts(nodeContext, portSide)`: the padding is the
surrounding port margin, the content height the sum of the port heights and margins plus the
port-port spacings (and two more spacings for `DISTRIBUTED` alignment). Without ports, the
top/bottom padding is cleared. -/
private def calculateVerticalNodeSizeRequiredByFreePorts (ctx : NodeContext N P L) (portSide : PortSide) :
    NodeContext N P L := Id.run do
  if (ctx.portContextsOf portSide).isEmpty then
    return updateInsidePortLabelCells ctx portSide fun cs c =>
      cs.modifyPadding c fun p => { p with top := fl0p0, bottom := fl0p0 }
  -- Set the padding to match the surrounding port space
  let surrTop := ctx.surroundingPortMargins.top
  let surrBottom := ctx.surroundingPortMargins.bottom
  let mut ctx := updateInsidePortLabelCells ctx portSide fun cs c =>
    cs.modifyPadding c fun p => { p with top := surrTop, bottom := surrBottom }
  if ctx.sizeConstraints.contains .portLabels then
    ctx := setupPortMargins ctx portSide
  let mut height := portHeightPlusPortPortSpacing ctx portSide
  if ctx.getPortAlignment portSide == .distributed then
    height := height + fl2p0 * ctx.portPortSpacing
  -- Set the cell size
  return updateInsidePortLabelCells ctx portSide fun cs c =>
    cs.modifyMinimumContentAreaSize c fun s => { s with y := height }

/-- `calculateVerticalPortPlacementSize(nodeContext)`: the space required by the eastern and
western ports. -/
def calculateVerticalPortPlacementSize (ctx : NodeContext N P L) : NodeContext N P L :=
  match ctx.portConstraints with
  | .fixedPos =>
    calculateVerticalNodeSizeRequiredByFixedPosPorts
      (calculateVerticalNodeSizeRequiredByFixedPosPorts ctx .east) .west
  | .fixedRatio =>
    calculateVerticalNodeSizeRequiredByFixedRatioPorts
      (calculateVerticalNodeSizeRequiredByFixedRatioPorts ctx .east) .west
  | _ =>
    calculateVerticalNodeSizeRequiredByFreePorts
      (calculateVerticalNodeSizeRequiredByFreePorts ctx .east) .west

end VerticalPortPlacementSizeCalculator

end Elk.Alg.Common.NodeSpacing.Internal.Algorithm
