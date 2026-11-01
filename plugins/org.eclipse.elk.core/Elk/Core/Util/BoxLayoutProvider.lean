import Elk.Core.Util.ElkUtil
import Elk.Graph.Impl.EMapPropertyHolderImpl
import Elk.Core.Util.Sort
import Elk.Core.LayoutProvider
import Elk.Core.Options
import Elk.Graph.ArrayModify
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.core.util.BoxLayoutProvider`

Packs the children of a node into rows (`SIMPLE`) or recursively grouped
boxes (`GROUP_DEC`, `GROUP_INC`, `GROUP_MIXED`). Groups form a tree held in
an arena (`BoxM` state) instead of `Rc<RefCell<Group>>`.
-/

namespace Elk.Core.Util

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Options

namespace BoxLayoutProvider

def DEF_ASPECT_RATIO : Float := 1.3

/-- `Group`: a node or a group of groups, with the groups whose size follows
this one's (`bottom`, `right`). -/
structure Group where
  node : Option NodeId := none
  groups : Array Nat := #[]
  size : KVector := {}
  bottom : Array Nat := #[]
  right : Array Nat := #[]
  deriving Inhabited

abbrev BoxM := StateT (Array Group) ElkM

@[inline] private def getGroup (i : Nat) : BoxM Group := do return (← get)[i]!
@[inline] private def modGroup (i : Nat) (f : Group → Group) : BoxM Unit := modify (·.modifyIn i f)

private def newNodeGroup (n : NodeId) : BoxM Nat := do
  ElkM.modifyNode n fun nd => { nd with x := fl0p0, y := fl0p0 }
  let gs ← get
  set (gs.push { node := some n })
  return gs.size

private def newGroups (children : Array Nat) : BoxM Nat := do
  let gs ← get
  set (gs.push { groups := children })
  return gs.size

private def groupWidth (i : Nat) : BoxM Float := do
  let gr ← getGroup i
  match gr.node with
  | some n => return (← ElkM.getNode n).width
  | none => return gr.size.x

private def groupHeight (i : Nat) : BoxM Float := do
  let gr ← getGroup i
  match gr.node with
  | some n => return (← ElkM.getNode n).height
  | none => return gr.size.y

private def groupArea (i : Nat) : BoxM Float := do return (← groupWidth i) * (← groupHeight i)

private partial def groupSetWidth (i : Nat) (width : Float) : BoxM Unit := do
  let current ← groupWidth i
  let gr ← getGroup i
  match gr.node with
  | some n => ElkM.modifyNode n fun nd => { nd with width := width }
  | none =>
    let delta := width - current
    for r in gr.right do
      groupSetWidth r ((← groupWidth r) + delta)

private partial def groupSetHeight (i : Nat) (height : Float) : BoxM Unit := do
  let current ← groupHeight i
  let gr ← getGroup i
  match gr.node with
  | some n => ElkM.modifyNode n fun nd => { nd with height := height }
  | none =>
    let delta := height - current
    for b in gr.bottom do
      groupSetHeight b ((← groupHeight b) + delta)

private partial def groupTranslate (i : Nat) (x y : Float) : BoxM Unit := do
  let gr ← getGroup i
  match gr.node with
  | some n => ElkM.modifyNode n fun nd => { nd with x := nd.x + x, y := nd.y + y }
  | none => for inner in gr.groups do groupTranslate inner x y

private partial def groupTranslateInnerNodes (i : Nat) (x y : Float) : BoxM Unit := do
  let gr ← getGroup i
  match gr.node with
  | some n => ElkUtil.translateNode n x y
  | none => for inner in gr.groups do groupTranslateInnerNodes inner x y

private def areaStdDevGroups (groups : Array Nat) (mean : Float) : BoxM Float := do
  let mut variance := 0.0
  for gi in groups do
    let a ← groupArea gi
    variance := variance + (a - mean) * (a - mean)
  return Float.sqrt (variance / (groups.size.toFloat - 1.0))

/-- `placeInnerBoxes`. -/
partial def placeInnerBoxes (group : Nat) (minSpacing : Float) (padding : ElkPadding)
    (minTotalWidth minTotalHeight : Float) (expandNodes : Bool) (aspectRatio : Float) : BoxM KVector := do
  let groups := (← getGroup group).groups
  let mut maxRowWidth := fl0p0
  let mut totalArea := fl0p0
  for gi in groups do
    if let some n := (← getGroup gi).node then
      let _ ← ElkUtil.resizeNode n
    let w ← groupWidth gi
    let h ← groupHeight gi
    maxRowWidth := fmax maxRowWidth w
    totalArea := totalArea + w * h
  let mean := totalArea / groups.size.toFloat
  let stddev ← areaStdDevGroups groups mean
  let sdInfluence := fl1p0
  totalArea := totalArea + groups.size.toFloat * sdInfluence * stddev
  maxRowWidth := fmax maxRowWidth (Float.sqrt (totalArea * aspectRatio)) + padding.left
  let mut xpos := padding.left
  let mut ypos := padding.top
  let mut highestBox := fl0p0
  let mut broadestRow := padding.left + padding.right
  let mut rowIndices : Array Nat := #[0]
  let mut rowHeights : Array Float := #[]
  let mut last : Option Nat := none
  let mut bottoms : Array Nat := #[]
  for h : index in [0:groups.size] do
    let gi := groups[index]
    let w ← groupWidth gi
    let hgt ← groupHeight gi
    if xpos + w > maxRowWidth then
      if expandNodes then
        rowHeights := rowHeights.push highestBox
        rowIndices := rowIndices.push index
        if let some lastGroup := last then
          modGroup group fun gr => { gr with right := gr.right.push lastGroup }
          last := none
        bottoms := #[]
      xpos := padding.left
      ypos := ypos + (highestBox + minSpacing)
      highestBox := fl0p0
      broadestRow := fmax broadestRow (padding.left + padding.right + w)
    bottoms := bottoms.push gi
    groupTranslate gi xpos ypos
    broadestRow := fmax broadestRow (xpos + w + padding.right)
    highestBox := fmax highestBox hgt
    xpos := xpos + (w + minSpacing)
    last := some gi
  let bottomsFinal := bottoms
  modGroup group fun gr => { gr with bottom := gr.bottom ++ bottomsFinal }
  if let some lastBottom := bottoms.back? then
    modGroup group fun gr => { gr with right := gr.right.push lastBottom }
  broadestRow := fmax broadestRow minTotalWidth
  let mut totalHeight := ypos + highestBox + padding.bottom
  if totalHeight < minTotalHeight then
    highestBox := highestBox + (minTotalHeight - totalHeight)
    totalHeight := minTotalHeight
  if expandNodes then
    xpos := padding.left
    rowIndices := rowIndices.push groups.size
    rowHeights := rowHeights.push highestBox
    let mut rowIdxPos := 0
    let mut rowHeightPos := 0
    let mut nextRowIndex := rowIndices[rowIdxPos]?.getD groups.size
    rowIdxPos := rowIdxPos + 1
    let mut rowHeight := fl0p0
    for h : index in [0:groups.size] do
      if index == nextRowIndex then
        xpos := padding.left
        rowHeight := rowHeights[rowHeightPos]?.getD fl0p0
        rowHeightPos := rowHeightPos + 1
        nextRowIndex := rowIndices[rowIdxPos]?.getD groups.size
        rowIdxPos := rowIdxPos + 1
      let gi := groups[index]
      groupSetHeight gi rowHeight
      if index + 1 == nextRowIndex then
        let newWidth := broadestRow - xpos - padding.right
        let oldWidth ← groupWidth gi
        groupSetWidth gi newWidth
        groupTranslateInnerNodes gi ((newWidth - oldWidth) / fl2p0) fl0p0
      xpos := xpos + ((← groupWidth gi) + minSpacing)
  return ⟨broadestRow, totalHeight⟩

/-- `mergeAndPlaceDec`. -/
partial def mergeAndPlaceDec (groups : Array Nat) (objSpacing minWidth minHeight : Float) (expandNodes : Bool) : BoxM (Array Nat) := do
  let mut keyed : Array (Nat × Float) := #[]
  for gi in groups do keyed := keyed.push (gi, ← groupArea gi)
  let sorted := stableSort keyed (fun a b => Float.comparePartial b.2 a.2)
  let mut queue := sorted.map (·.1)
  let mut head := 0
  let mut toBePlaced : Array Nat := #[]
  let mut maybeGroup : Array Nat := #[]
  let mut boxToBeat : Option Nat := none
  let mut collectedArea := fl0p0
  while head < queue.size do
    let gi := queue[head]!
    head := head + 1
    let boxArea ← groupArea gi
    let beatArea ← match boxToBeat with
      | some b => groupArea b
      | none => pure fl0p0
    if boxToBeat.isNone || beatArea / fl2p0 < boxArea then
      boxToBeat := some gi
      toBePlaced := toBePlaced.push gi
    else
      collectedArea := collectedArea + boxArea
      maybeGroup := maybeGroup.push gi
      if maybeGroup.size > 1 && (collectedArea > beatArea / fl2p0 || head >= queue.size) then
        let inner ← newGroups maybeGroup
        let beat := boxToBeat.get!
        let innerAspectRatio := (← groupWidth beat) / (← groupHeight beat)
        let groupSize ← placeInnerBoxes inner objSpacing {} minWidth minHeight expandNodes innerAspectRatio
        modGroup inner fun gr => { gr with size := groupSize }
        boxToBeat := some inner
        toBePlaced := toBePlaced.push inner
        collectedArea := fl0p0
        maybeGroup := #[]
  return toBePlaced ++ maybeGroup

/-- `mergeAndPlaceMixed` (min-heap by (area, seq) emulated with a sorted array). -/
partial def mergeAndPlaceMixed (groups : Array Nat) (objSpacing minWidth minHeight : Float) (expandNodes : Bool) : BoxM (Array Nat) := do
  let mut cumArea : Array Float := Array.replicate groups.size fl0p0
  let mut heap : Array (Float × Nat × Nat) := #[]   -- (area, seq, group), ascending
  let insert (h : Array (Float × Nat × Nat)) (e : Float × Nat × Nat) : Array (Float × Nat × Nat) := Id.run do
    let mut i := 0
    while i < h.size && (h[i]!.1 < e.1 || (h[i]!.1 == e.1 && h[i]!.2.1 < e.2.1)) do i := i + 1
    return h.insertIdx! i e
  let mut seq := 0
  for gi in groups do
    heap := insert heap (← groupArea gi, seq, gi)
    seq := seq + 1
  let mut index := 0
  let mut toBePlaced : Array Nat := #[]
  while !heap.isEmpty do
    let (boxArea, _, boxGroup) := heap[0]!
    if index > 1 && boxArea / fl2p0 > cumArea[0]! then
      let mut anIndex := 0
      while anIndex < toBePlaced.size - 1 && boxArea / fl2p0 > cumArea[anIndex]! do anIndex := anIndex + 1
      let selected := toBePlaced.extract 0 (anIndex + 1)
      let inner ← newGroups selected
      let innerAspectRatio := (← groupWidth boxGroup) / (← groupHeight boxGroup)
      let groupSize ← placeInnerBoxes inner objSpacing {} minWidth minHeight expandNodes innerAspectRatio
      modGroup inner fun gr => { gr with size := groupSize }
      heap := insert heap (← groupArea inner, seq, inner)
      seq := seq + 1
      for gi in toBePlaced.extract (anIndex + 1) toBePlaced.size do
        heap := insert heap (← groupArea gi, seq, gi)
        seq := seq + 1
      toBePlaced := #[]
      index := 0
      cumArea := Array.replicate groups.size fl0p0
    else
      let (area, _, gi) := heap[0]!
      heap := heap.eraseIdx! 0
      if index > 0 then cumArea := cumArea.set! index cumArea[index - 1]!
      cumArea := cumArea.set! index (cumArea[index]! + area)
      index := index + 1
      toBePlaced := toBePlaced.push gi
  return toBePlaced

/-- `mergeAndPlaceInc`. -/
partial def mergeAndPlaceInc (groups : Array Nat) (objSpacing minWidth minHeight : Float) (expandNodes : Bool) : BoxM (Array Nat) := do
  let mut keyed : Array (Nat × Float) := #[]
  for gi in groups do keyed := keyed.push (gi, ← groupArea gi)
  let sorted := (stableSort keyed (fun a b => Float.comparePartial a.2 b.2)).map (·.1)
  let mut toBePlaced : Array Nat := #[]
  let mut commonArea := fl0p0
  for gi in sorted do
    let area ← groupArea gi
    if !toBePlaced.isEmpty && area > commonArea * fl2p0 then
      let merged ← newGroups toBePlaced
      let innerAspectRatio := (← groupWidth gi) / (← groupHeight gi)
      let groupSize ← placeInnerBoxes merged objSpacing {} minWidth minHeight expandNodes innerAspectRatio
      modGroup merged fun gr => { gr with size := groupSize }
      toBePlaced := #[merged, gi]
      commonArea := (← groupArea merged) + area
    else
      commonArea := commonArea + area
      toBePlaced := toBePlaced.push gi
  return toBePlaced

/-- `placeBoxesGrouping`. -/
def placeBoxesGrouping (parent : NodeId) (objSpacing : Float) (padding : ElkPadding) (expandNodes : Bool) : ElkM Unit := do
  let node ← ElkM.getNode parent
  let minSize0 := node.props.getD BoxLayouterOptions.NODE_SIZE_MINIMUM {}
  let minSize : KVector := ⟨fmax (minSize0.x - padding.left - padding.right) 0.0, fmax (minSize0.y - padding.top - padding.bottom) 0.0⟩
  let mut aspectRatio := node.props.getD BoxLayouterOptions.ASPECT_RATIO DEF_ASPECT_RATIO
  if aspectRatio <= 0.0 then aspectRatio := DEF_ASPECT_RATIO
  let mode := node.props.getD BoxLayouterOptions.BOX_PACKING_MODE .simple
  let ar := aspectRatio
  let (parentSize, _) ← (do
      let mut groups : Array Nat := #[]
      for c in node.children do groups := groups.push (← newNodeGroup c)
      let toBePlaced ← match mode with
        | .groupInc => mergeAndPlaceInc groups objSpacing minSize.x minSize.y expandNodes
        | .groupDec => mergeAndPlaceDec groups objSpacing minSize.x minSize.y expandNodes
        | _ => mergeAndPlaceMixed groups objSpacing minSize.x minSize.y expandNodes
      let finalGroup ← newGroups toBePlaced
      placeInnerBoxes finalGroup objSpacing padding minSize.x minSize.y expandNodes ar : BoxM KVector).run #[]
  let _ ← ElkUtil.resizeNodeWith parent parentSize.x parentSize.y false true

/-- `sortBoxes`: priority descending, (interactive: y then x), then area ascending. -/
def sortBoxes (parent : NodeId) (interactive : Bool) : ElkM (Array NodeId) := do
  let g ← get
  let children := (g.node parent).children
  let key (n : NodeId) : Int × Float × Float × Float :=
    let nd := g.node n
    (nd.props.getD BoxLayouterOptions.PRIORITY 0, nd.y, nd.x, nd.width * nd.height)
  let keyed := children.map fun n => (n, key n)
  let sorted := stableSort keyed fun a b =>
    let (p1, y1, x1, a1) := a.2
    let (p2, y2, x2, a2) := b.2
    if p1 > p2 then .lt else if p1 < p2 then .gt
    else
      let interactiveCmp := if interactive then
        match Float.comparePartial y1 y2 with
        | .eq => Float.comparePartial x1 x2
        | c => c
        else .eq
      match interactiveCmp with
      | .eq => Float.comparePartial a1 a2
      | c => c
  return sorted.map (·.1)

private def areaStdDev (boxes : Array NodeId) (mean : Float) : ElkM Float := do
  let g ← get
  let mut variance := 0.0
  for b in boxes do
    let nd := g.node b
    let area := nd.width * nd.height
    variance := variance + (area - mean) * (area - mean)
  return Float.sqrt (variance / (boxes.size.toFloat - 1.0))

/-- `placeBoxes(sortedBoxes, ...)`. -/
def placeBoxesSorted (sortedBoxes : Array NodeId) (minSpacing : Float) (padding : ElkPadding)
    (minTotalWidth minTotalHeight : Float) (expandNodes : Bool) (aspectRatio : Float) : ElkM KVector := do
  let mut maxRowWidth := fl0p0
  let mut totalArea := fl0p0
  for b in sortedBoxes do
    let _ ← ElkUtil.resizeNode b
    let nd ← ElkM.getNode b
    maxRowWidth := fmax maxRowWidth nd.width
    totalArea := totalArea + nd.width * nd.height
  let mean := totalArea / sortedBoxes.size.toFloat
  let stddev ← areaStdDev sortedBoxes mean
  totalArea := totalArea + sortedBoxes.size.toFloat * stddev
  totalArea := totalArea + Float.sqrt totalArea * (padding.bottom + padding.top)
  totalArea := totalArea + Float.sqrt totalArea * padding.right
  maxRowWidth := fmax maxRowWidth (Float.sqrt (totalArea * aspectRatio)) + padding.left
  let mut xpos := padding.left
  let mut ypos := padding.top
  let mut highestBox := fl0p0
  let mut broadestRow := padding.left + padding.right
  let mut rowIndices : Array Nat := #[0]
  let mut rowHeights : Array Float := #[]
  for h : index in [0:sortedBoxes.size] do
    let b := sortedBoxes[index]
    let nd ← ElkM.getNode b
    if xpos + nd.width > maxRowWidth then
      if expandNodes then
        rowHeights := rowHeights.push highestBox
        rowIndices := rowIndices.push index
      xpos := padding.left
      ypos := ypos + (highestBox + minSpacing)
      highestBox := fl0p0
      broadestRow := fmax broadestRow (padding.left + padding.right + nd.width)
    let xp := xpos
    let yp := ypos
    ElkM.modifyNode b fun x => { x with x := xp, y := yp }
    broadestRow := fmax broadestRow (xpos + nd.width + padding.right)
    highestBox := fmax highestBox nd.height
    xpos := xpos + (nd.width + minSpacing)
  broadestRow := fmax broadestRow minTotalWidth
  let mut totalHeight := ypos + highestBox + padding.bottom
  if totalHeight < minTotalHeight then
    highestBox := highestBox + (minTotalHeight - totalHeight)
    totalHeight := minTotalHeight
  if expandNodes then
    xpos := padding.left
    rowIndices := rowIndices.push sortedBoxes.size
    rowHeights := rowHeights.push highestBox
    let mut rowIdxPos := 0
    let mut rowHeightPos := 0
    let mut nextRowIndex := rowIndices[rowIdxPos]?.getD sortedBoxes.size
    rowIdxPos := rowIdxPos + 1
    let mut rowHeight := fl0p0
    for h : index in [0:sortedBoxes.size] do
      if index == nextRowIndex then
        xpos := padding.left
        rowHeight := rowHeights[rowHeightPos]?.getD fl0p0
        rowHeightPos := rowHeightPos + 1
        nextRowIndex := rowIndices[rowIdxPos]?.getD sortedBoxes.size
        rowIdxPos := rowIdxPos + 1
      let b := sortedBoxes[index]
      let oldHeight := (← ElkM.getNode b).height
      let rh := rowHeight
      ElkM.modifyNode b fun x => { x with height := rh }
      let newHeight := rowHeight
      if index + 1 == nextRowIndex then
        let newWidth := broadestRow - xpos - padding.right
        let oldWidth := (← ElkM.getNode b).width
        ElkM.modifyNode b fun x => { x with width := newWidth }
        ElkUtil.translateNodeWithSizes b ⟨newWidth, newHeight⟩ ⟨oldWidth, oldHeight⟩
      xpos := xpos + ((← ElkM.getNode b).width + minSpacing)
  return ⟨broadestRow, totalHeight⟩

/-- `placeBoxes` (SIMPLE mode). -/
def placeBoxes (parent : NodeId) (objSpacing : Float) (padding : ElkPadding) (expandNodes interactive : Bool) : ElkM Unit := do
  let sorted ← sortBoxes parent interactive
  let minSize := ElkUtil.effectiveMinSizeConstraintFor (← get) parent
  let mut aspectRatio := (← ElkM.getNode parent).props.getD BoxLayouterOptions.ASPECT_RATIO DEF_ASPECT_RATIO
  if aspectRatio <= 0.0 then aspectRatio := DEF_ASPECT_RATIO
  let parentSize ← placeBoxesSorted sorted objSpacing padding minSize.x minSize.y expandNodes aspectRatio
  let _ ← ElkUtil.resizeNodeWith parent parentSize.x parentSize.y false true

/-- `BoxLayoutProvider.layout`. -/
def layout (layoutNode : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "Box layout" 2.0
  let node ← ElkM.getNode layoutNode
  let objSpacing := node.props.getD BoxLayouterOptions.SPACING_NODE_NODE 0.0
  -- Java `getProperty` stores the cloned default padding on the node (`EMapPropertyHolderImpl`)
  let padding := (← ElkM.getNodePropSticky layoutNode BoxLayouterOptions.PADDING).getD {}
  let expandNodes := node.props.getD BoxLayouterOptions.EXPAND_NODES false
  let interactive := node.props.getD BoxLayouterOptions.INTERACTIVE false
  let packingMode := node.props.getD BoxLayouterOptions.BOX_PACKING_MODE .simple
  match packingMode with
  | .simple => placeBoxes layoutNode objSpacing padding expandNodes interactive
  | _ => placeBoxesGrouping layoutNode objSpacing padding expandNodes
  monitor.done

def provider : LayoutProvider := { id := BoxLayouterOptions.ALGORITHM_ID, layout := layout }

end BoxLayoutProvider

end Elk.Core.Util
