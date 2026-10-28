import Std.Data.HashSet
import Elk.Alg.Layered.LayeredPhases
import Elk.Alg.Layered.Graph.LGraphUtil
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
/-!
# `org.eclipse.elk.alg.layered.intermediate.LabelDummySwitcher`

Port of elk-rs `intermediate/label_dummy_switcher.rs` (Java `LabelDummySwitcher`): "Processor that
tries to move label dummy nodes into an "optimal" layer their long edges crosses. This is done by
switching the order of long edge dummies and label dummies. There are different strategies
(`CenterEdgeLabelPlacementStrategy`) available to determine the target layer." The long edge dummies
preceding a label dummy get `LONG_EDGE_BEFORE_LABEL_DUMMY = true` so that hyperedge merging keeps the
labels apart.

Slot: before phase 4 (after crossing minimization; the node order inside the layers is kept).

`INCLUDE_LABEL` is not an `InternalProperties` constant: in Java/Rust it is an ordinary property of
the label's property map (and it is copied to the ElkGraph by `ElkGraphLayoutTransferrer`), so the
Lean port keeps it in `LLabel.props` / `ElkLabel.props` instead of a typed `LLabelInternals` field.
`assignLayer` sets it to `true` on every label represented by a placed label dummy.

Processing (Rust): layer ids are set to the layer indices; the label dummies (layer order, node
order) are grouped by their effective strategy (the graph's
`EDGE_LABELS_CENTER_LABEL_PLACEMENT_STRATEGY`, overridden by the first represented label that stores
one). If a non-empty group uses label size information, the layer widths (widest `NORMAL` node,
`0` in vertical layouts) are computed once. Then the groups are processed in the `STRATEGIES` order
(`MEDIAN_LAYER, TAIL_LAYER, HEAD_LAYER, SPACE_EFFICIENT_LAYER, WIDEST_LAYER, CENTER_LAYER`, which is
also the ordinal order), first those that do not use label sizes, then the others.

Rust details kept: `assign_to_wider_layer` compares with the layer's `size.x`; in
`find_potentially_widest_layer` the *last* matching unassigned label counts; the space-efficient
labels are sorted by descending width with `total_cmp` (stable); the chains of long edge dummies are
followed with a visited set (no endless loops on cyclic chains); the minimum space between layers is
`max(2 * SPACING_EDGE_NODE_BETWEEN_LAYERS, SPACING_NODE_NODE_BETWEEN_LAYERS)` of the processed graph.
The `ELK_TRACE_LABEL_DUMMY_SWITCHER` debug output is omitted.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.Layered.Intermediate

open Elk.Graph Elk.Core Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options LayeredM

namespace LabelDummySwitcher

/-- `LabelDummySwitcher.INCLUDE_LABEL` (elk-rs `INCLUDE_LABEL`): "A property to communicate
with the analyses that can be run on a graph." Id `edgelabelcenterednessanalysis.includelabel`,
default `false`; set to `true` on the labels represented by a label dummy whose layer was
assigned by the switcher. -/
def INCLUDE_LABEL : Property Bool :=
  Property.withDefault "edgelabelcenterednessanalysis.includelabel" false

/-- Rust `STRATEGIES` (= the ordinal order of `CenterEdgeLabelPlacementStrategy`). -/
def STRATEGIES : Array CenterEdgeLabelPlacementStrategy :=
  #[.medianLayer, .tailLayer, .headLayer, .spaceEfficientLayer, .widestLayer, .centerLayer]

/-- Rust `LabelDummyInfo`: a label dummy with the long edge dummies of its edge to the left and right
and the range of layers it may be placed in. -/
structure LabelDummyInfo where
  labelDummy : LNodeId
  placementStrategy : CenterEdgeLabelPlacementStrategy
  leftLongEdgeDummies : Array LNodeId := #[]
  rightLongEdgeDummies : Array LNodeId := #[]
  leftmostLayerId : Nat := 0
  rightmostLayerId : Nat := 0
  deriving Inhabited

/-- Rust `LabelDummySwitcher` fields (reset after every run). -/
structure State where
  /-- `layer_widths`, indexed by layer id. -/
  layerWidths : Array Float := #[]
  /-- `layers`: the graph's layers (copy taken at the start). -/
  layers : Array LayerId := #[]
  /-- `min_space_between_layers`. -/
  minSpaceBetweenLayers : Float := fl0p0

/-- Processor-local monad. -/
abbrev SwitcherM := StateT State LayeredM

/-- Rust `node_layer_id(node)`: the id of the node's layer (`as usize`). -/
def nodeLayerId (node : LNodeId) : LayeredM (Option Nat) := do
  match (← getNode node).layer with
  | some l => return some (← getLayer l).id.toNat
  | none => return none

/-- Rust `previous_long_edge_node(node)`: source node of the node's first incoming edge. -/
def previousLongEdgeNode (node : LNodeId) : LayeredM (Option LNodeId) := do
  let incoming ← withArena (·.nodeIncomingEdges node)
  let some edge := incoming[0]? | return none
  let some source := (← getEdge edge).source | return none
  return (← getPort source).owner

/-- Rust `next` in `gather_right_long_edge_dummies`: target node of the node's first outgoing edge. -/
def nextLongEdgeNode (node : LNodeId) : LayeredM (Option LNodeId) := do
  let outgoing ← withArena (·.nodeOutgoingEdges node)
  let some edge := outgoing[0]? | return none
  let some target := (← getEdge edge).target | return none
  return (← getPort target).owner

/-- Rust `LabelDummyInfo::gather_left_long_edge_dummies`: the `LONG_EDGE` predecessors, leftmost first. -/
def gatherLeftLongEdgeDummies (labelDummy : LNodeId) : LayeredM (Array LNodeId) := do
  let mut result : Array LNodeId := #[]
  let mut source := labelDummy
  let mut visited : Std.HashSet LNodeId := {}
  while true do
    let some next ← previousLongEdgeNode source | break
    if visited.contains next then break
    visited := visited.insert next
    if (← getNode next).type == .longEdge then
      result := result.push next
      source := next
    else break
  return result.reverse

/-- Rust `LabelDummyInfo::gather_right_long_edge_dummies`: the `LONG_EDGE` successors, in order. -/
def gatherRightLongEdgeDummies (labelDummy : LNodeId) : LayeredM (Array LNodeId) := do
  let mut result : Array LNodeId := #[]
  let mut target := labelDummy
  let mut visited : Std.HashSet LNodeId := {}
  while true do
    let some next ← nextLongEdgeNode target | break
    if visited.contains next then break
    visited := visited.insert next
    if (← getNode next).type == .longEdge then
      result := result.push next
      target := next
    else break
  return result

/-- Rust `LabelDummyInfo::new(label_dummy, default_strategy)`. -/
def LabelDummyInfo.create (labelDummy : LNodeId) (defaultStrategy : CenterEdgeLabelPlacementStrategy) :
    LayeredM LabelDummyInfo := do
  let left ← gatherLeftLongEdgeDummies labelDummy
  let right ← gatherRightLongEdgeDummies labelDummy
  let ownLayer ← nodeLayerId labelDummy
  let leftFirst ← match left[0]? with
    | some n => nodeLayerId n
    | none => pure none
  let leftmost := (leftFirst.orElse fun _ => ownLayer).getD 0
  let rightLast ← match right.back? with
    | some n => nodeLayerId n
    | none => pure none
  let rightmost := (rightLast.orElse fun _ => ownLayer).getD leftmost
  let mut strategy := defaultStrategy
  for label in (← getNode labelDummy).internal.representedLabels do
    let lb ← getLabel label
    let override := if lb.props.has LayeredOptions.EDGE_LABELS_CENTER_LABEL_PLACEMENT_STRATEGY then
      lb.props.get LayeredOptions.EDGE_LABELS_CENTER_LABEL_PLACEMENT_STRATEGY else none
    if let some s := override then
      strategy := s
      break
  return { labelDummy := labelDummy, placementStrategy := strategy, leftLongEdgeDummies := left,
           rightLongEdgeDummies := right, leftmostLayerId := leftmost, rightmostLayerId := rightmost }

/-- Rust `total_dummy_count`: `rightmost - leftmost + 1` (saturating). -/
def LabelDummyInfo.totalDummyCount (info : LabelDummyInfo) : Nat :=
  info.rightmostLayerId - info.leftmostLayerId + 1

/-- Rust `ith_dummy_node(index)`: left dummies, the label dummy, right dummies (`none` out of range,
where Rust would panic). -/
def LabelDummyInfo.ithDummyNode (info : LabelDummyInfo) (index : Nat) : Option LNodeId :=
  if index < info.leftLongEdgeDummies.size then info.leftLongEdgeDummies[index]?
  else if index == info.leftLongEdgeDummies.size then some info.labelDummy
  else info.rightLongEdgeDummies[index - info.leftLongEdgeDummies.size - 1]?

/-- Rust `label_dummy_width`: the label dummy's current width. -/
def LabelDummyInfo.width (info : LabelDummyInfo) : LayeredM Float := do
  return (← getNode info.labelDummy).size.x

/-- Rust `assign_ids_to_layers`: layer `id` = index. -/
def assignIdsToLayers (graph : LGraphId) : LayeredM Unit := do
  let layers := (← getGraph graph).layers
  for h : i in [0:layers.size] do
    modifyLayer layers[i] fun l => { l with id := (i : Int) }

/-- Rust `gather_label_dummy_infos`: per strategy ordinal the infos of its label dummies. -/
def gatherLabelDummyInfos (graph : LGraphId) (defaultStrategy : CenterEdgeLabelPlacementStrategy) :
    LayeredM (Array (Array LabelDummyInfo)) := do
  let mut infos : Array (Array LabelDummyInfo) := Array.replicate STRATEGIES.size #[]
  let layers := (← getGraph graph).layers
  for layer in layers do
    let nodes := (← getLayer layer).nodes
    for node in nodes do
      if (← getNode node).type != .label then continue
      let info ← LabelDummyInfo.create node defaultStrategy
      infos := infos.modify (ElkEnum.ordinal info.placementStrategy) (·.push info)
  return infos

/-- Layer width by layer id (`0` when out of range, Rust `get(..).unwrap_or(0.0)`). -/
private def widthAt (s : State) (i : Nat) : Float := s.layerWidths[i]?.getD 0.0

/-- Rust `calculate_layer_widths(direction)`. -/
def calculateLayerWidths (direction : Direction) : SwitcherM Unit := do
  for layer in (← get).layers do
    let layerId := (← getLayer layer).id
    if layerId >= 0 then
      let width ← LGraphUtil.findMaxNonDummyNodeWidth layer direction false
      modify fun s => { s with layerWidths := s.layerWidths.modify layerId.toNat fun _ => width }

/-- Rust `find_widest_layer_target_id`: the first layer of the range with the largest width. -/
def findWidestLayerTargetId (info : LabelDummyInfo) : SwitcherM Nat := do
  let s ← get
  let mut widestLayer := info.leftmostLayerId
  for index in [info.leftmostLayerId + 1:info.rightmostLayerId + 1] do
    if widthAt s index > widthAt s widestLayer then widestLayer := index
  return widestLayer

/-- Rust `compute_layer_width_sums`: accumulated widths (each plus the minimum layer spacing) of the
layers of the left dummies, the label dummy and the right dummies. -/
def computeLayerWidthSums (info : LabelDummyInfo) : SwitcherM (Array Float) := do
  let s ← get
  let minSpace := s.minSpaceBetweenLayers
  let mut sums : Array Float := Array.replicate info.totalDummyCount 0.0
  let mut currentSum := -minSpace
  let mut index := 0
  for leftDummy in info.leftLongEdgeDummies do
    let layerId := (← nodeLayerId leftDummy).getD 0
    currentSum := currentSum + (widthAt s layerId + minSpace)
    sums := sums.setIfInBounds index currentSum
    index := index + 1
  let labelLayerId := (← nodeLayerId info.labelDummy).getD 0
  currentSum := currentSum + (widthAt s labelLayerId + minSpace)
  if index < sums.size then
    sums := sums.setIfInBounds index currentSum
    index := index + 1
  for rightDummy in info.rightLongEdgeDummies do
    let layerId := (← nodeLayerId rightDummy).getD 0
    currentSum := currentSum + (widthAt s layerId + minSpace)
    if index < sums.size then
      sums := sums.setIfInBounds index currentSum
      index := index + 1
  return sums

/-- Rust `find_center_layer_target_id`: the first layer at which the accumulated width reaches half
of the total. -/
def findCenterLayerTargetId (info : LabelDummyInfo) : SwitcherM Nat := do
  let sums ← computeLayerWidthSums info
  let threshold := sums.back?.getD 0.0 / 2.0
  for h : i in [0:sums.size] do
    if sums[i] >= threshold then return info.leftmostLayerId + i
  return info.leftmostLayerId + info.leftLongEdgeDummies.size

/-- Rust `find_median_layer_target_id`: the lower median of the layer range. -/
def findMedianLayerTargetId (info : LabelDummyInfo) : Nat :=
  info.leftmostLayerId + (info.totalDummyCount - 1) / 2

/-- Rust `is_part_of_reversed_edge`: the first incoming or the first outgoing edge is `REVERSED`. -/
def isPartOfReversedEdge (info : LabelDummyInfo) : LayeredM Bool := do
  let incoming ← withArena (·.nodeIncomingEdges info.labelDummy)
  let outgoing ← withArena (·.nodeOutgoingEdges info.labelDummy)
  let incomingReversed ← match incoming[0]? with
    | some e => pure (← getEdge e).internal.reversed
    | none => pure false
  let outgoingReversed ← match outgoing[0]? with
    | some e => pure (← getEdge e).internal.reversed
    | none => pure false
  return incomingReversed || outgoingReversed

/-- Rust `find_end_layer_target_id(info, head_layer)`: the rightmost layer for head labels of
non-reversed edges (and tail labels of reversed ones), else the leftmost. -/
def findEndLayerTargetId (info : LabelDummyInfo) (headLayer : Bool) : LayeredM Nat := do
  let reversed ← isPartOfReversedEdge info
  if (headLayer && !reversed) || (!headLayer && reversed) then return info.rightmostLayerId
  return info.leftmostLayerId

/-- Rust `set_end_layer_node_alignment`: `ALIGNMENT = RIGHT` for head labels of non-reversed edges
(and tail labels of reversed ones), else `LEFT`. -/
def setEndLayerNodeAlignment (info : LabelDummyInfo) : LayeredM Unit := do
  let isHeadLabel := info.placementStrategy == .headLayer
  let reversed ← isPartOfReversedEdge info
  let alignment := if (isHeadLabel && !reversed) || (!isHeadLabel && reversed) then Alignment.right else Alignment.left
  setNodeProp info.labelDummy LayeredOptions.ALIGNMENT alignment

/-- Rust `swap_nodes(label_dummy, long_edge_dummy)`: exchanges the layers and positions of the two
dummies and reroutes their edges (first input/output port of each). -/
def swapNodes (labelDummy longEdgeDummy : LNodeId) : LayeredM Unit := do
  let some layer1 := (← getNode labelDummy).layer | return
  let some layer2 := (← getNode longEdgeDummy).layer | return
  let some dummy1Pos := (← getLayer layer1).nodes.findIdx? (· == labelDummy) | return
  let some dummy2Pos := (← getLayer layer2).nodes.findIdx? (· == longEdgeDummy) | return
  let input1 := (← withArena (·.nodePortsByType labelDummy .input))[0]?
  let output1 := (← withArena (·.nodePortsByType labelDummy .output))[0]?
  let input2 := (← withArena (·.nodePortsByType longEdgeDummy .input))[0]?
  let output2 := (← withArena (·.nodePortsByType longEdgeDummy .output))[0]?
  let (some input1, some output1, some input2, some output2) := (input1, output1, input2, output2) | return
  let incomingEdges1 := (← getPort input1).incomingEdges
  let outgoingEdges1 := (← getPort output1).outgoingEdges
  let incomingEdges2 := (← getPort input2).incomingEdges
  let outgoingEdges2 := (← getPort output2).outgoingEdges
  setNodeLayerAtIndex labelDummy dummy2Pos (some layer2)
  for edge in incomingEdges2 do setEdgeTarget edge (some input1)
  for edge in outgoingEdges2 do setEdgeSource edge (some output1)
  setNodeLayerAtIndex longEdgeDummy dummy1Pos (some layer1)
  for edge in incomingEdges1 do setEdgeTarget edge (some input2)
  for edge in outgoingEdges1 do setEdgeSource edge (some output2)

/-- Rust `assign_layer(info, target_layer_index)`: swaps the label dummy into the target layer if
needed, widens the layer's recorded width to the dummy width and marks the represented labels with
`INCLUDE_LABEL`. -/
def assignLayer (info : LabelDummyInfo) (targetLayerIndex : Nat) : SwitcherM Unit := do
  let currentLayerIndex := info.leftmostLayerId + info.leftLongEdgeDummies.size
  if targetLayerIndex != currentLayerIndex then
    -- `ith_dummy_node` is always defined for targets inside the label's layer range
    if let some swapNode := info.ithDummyNode (targetLayerIndex - info.leftmostLayerId) then
      swapNodes info.labelDummy swapNode
  let newLayerId := (← nodeLayerId info.labelDummy).getD targetLayerIndex
  let dummyWidth ← info.width
  modify fun s =>
    { s with layerWidths := s.layerWidths.modify newLayerId fun w => if dummyWidth > w then dummyWidth else w }
  for label in (← getNode info.labelDummy).internal.representedLabels do
    setLabelProp label INCLUDE_LABEL true

/-- Rust `assign_to_wider_layer`: the first layer of the range whose `size.x` is at least the dummy
width. -/
def assignToWiderLayer (info : LabelDummyInfo) : SwitcherM Bool := do
  let dummyWidth ← info.width
  for layerIndex in [info.leftmostLayerId:info.rightmostLayerId + 1] do
    if let some layer := (← get).layers[layerIndex]? then
      let layerWidth := (← getLayer layer).size.x
      if layerWidth >= dummyWidth then
        assignLayer info layerIndex
        return true
  return false

/-- Rust `perform_trivial_assignments`: single-layer labels and labels that fit into an already wide
enough layer are assigned; the others are returned. -/
def performTrivialAssignments (infos : Array LabelDummyInfo) : SwitcherM (Array LabelDummyInfo) := do
  let mut remaining : Array LabelDummyInfo := #[]
  for info in infos do
    if info.leftmostLayerId == info.rightmostLayerId then
      assignLayer info info.leftmostLayerId
    else if !(← assignToWiderLayer info) then
      remaining := remaining.push info
  return remaining

/-- Rust `find_potentially_widest_layer(infos, label_index)`: a layer already at least as wide as the
label, else the layer that becomes the widest when the last later label that may go there is counted
(leftmost on ties). -/
def findPotentiallyWidestLayer (infos : Array LabelDummyInfo) (labelIndex : Nat) : SwitcherM Nat := do
  let s ← get
  let info := infos[labelIndex]!
  let labelDummyWidth ← info.width
  let mut widestLayerIndex := info.leftmostLayerId
  let mut widestLayerWidth : Float := 0.0
  for layer in [info.leftmostLayerId:info.rightmostLayerId + 1] do
    if labelDummyWidth <= widthAt s layer then return layer
    let mut potentialWidth := widthAt s layer
    let mut largestUnassigned : Option LabelDummyInfo := none
    for candidate in infos[labelIndex + 1:] do
      if candidate.leftmostLayerId <= layer && candidate.rightmostLayerId >= layer then
        largestUnassigned := some candidate
    if let some candidate := largestUnassigned then
      potentialWidth := fmax potentialWidth (← candidate.width)
    if potentialWidth > widestLayerWidth then
      widestLayerIndex := layer
      widestLayerWidth := potentialWidth
  return widestLayerIndex

/-- Rust `compute_space_efficient_assignment`. -/
def computeSpaceEfficientAssignment (infos : Array LabelDummyInfo) : SwitcherM Unit := do
  let nonTrivial ← performTrivialAssignments infos
  if nonTrivial.isEmpty then return
  let mut keyed : Array (Float × LabelDummyInfo) := Array.mkEmpty nonTrivial.size
  for info in nonTrivial do
    keyed := keyed.push ((← info.width), info)
  let sorted := (stableSort keyed fun a b => Float.compareTotal b.1 a.1).map (·.2)
  for h : labelIndex in [0:sorted.size] do
    let target ← findPotentiallyWidestLayer sorted labelIndex
    assignLayer sorted[labelIndex] target

/-- Rust `do_update_long_edge_label_dummy_info(label_dummy, previous_long_edge_node, true)`
(`update_long_edge_source_label_dummy_info`): marks the preceding long edge dummies with
`LONG_EDGE_BEFORE_LABEL_DUMMY`. -/
def updateLongEdgeSourceLabelDummyInfo (info : LabelDummyInfo) : LayeredM Unit := do
  let some first ← previousLongEdgeNode info.labelDummy | return
  let mut longEdgeDummy := first
  let mut visited : Std.HashSet LNodeId := {}
  while (← getNode longEdgeDummy).type == .longEdge do
    if visited.contains longEdgeDummy then break
    visited := visited.insert longEdgeDummy
    modifyNode longEdgeDummy fun n => { n with internal := { n.internal with longEdgeBeforeLabelDummy := true } }
    let some next ← previousLongEdgeNode longEdgeDummy | break
    longEdgeDummy := next

/-- Rust `process_strategy(infos)`: the space-efficient group is assigned as a whole; every other
label dummy is moved to its strategy's target layer. -/
def processStrategy (infos : Array LabelDummyInfo) : SwitcherM Unit := do
  let some first := infos[0]? | return
  if first.placementStrategy == .spaceEfficientLayer then
    computeSpaceEfficientAssignment infos
    return
  for info in infos do
    match info.placementStrategy with
    | .centerLayer => assignLayer info (← findCenterLayerTargetId info)
    | .medianLayer => assignLayer info (findMedianLayerTargetId info)
    | .widestLayer => assignLayer info (← findWidestLayerTargetId info)
    | .headLayer =>
      setEndLayerNodeAlignment info
      assignLayer info (← findEndLayerTargetId info true)
    | .tailLayer =>
      setEndLayerNodeAlignment info
      assignLayer info (← findEndLayerTargetId info false)
    | .spaceEfficientLayer => pure ()
    updateLongEdgeSourceLabelDummyInfo info

/-- `process(layeredGraph, monitor)`. -/
def process (graph : LGraphId) (monitor : ProgressMonitor) : LayeredM Unit := do
  let _ ← monitor.begin "Label dummy switching" 1.0
  let gr ← getGraph graph
  let defaultStrategy := gr.props.getD LayeredOptions.EDGE_LABELS_CENTER_LABEL_PLACEMENT_STRATEGY
    CenterEdgeLabelPlacementStrategy.medianLayer
  let direction := gr.props.getD LayeredOptions.DIRECTION Direction.undefined
  let layers := gr.layers
  let edgeNodeSpacing := gr.props.getD LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS 0.0 * 2.0
  let nodeNodeSpacing := gr.props.getD LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS 0.0
  assignIdsToLayers graph
  let infos ← gatherLabelDummyInfos graph defaultStrategy
  let run : SwitcherM Unit := do
    for strategy in STRATEGIES do
      if strategy.usesLabelSizeInformation then
        if !(infos[ElkEnum.ordinal strategy]?.getD #[]).isEmpty then
          calculateLayerWidths direction
          break
    for strategy in STRATEGIES do
      if !strategy.usesLabelSizeInformation then
        processStrategy (infos[ElkEnum.ordinal strategy]?.getD #[])
    for strategy in STRATEGIES do
      if strategy.usesLabelSizeInformation then
        processStrategy (infos[ElkEnum.ordinal strategy]?.getD #[])
  let _ ← run.run { layerWidths := Array.replicate layers.size 0.0, layers := layers,
                    minSpaceBetweenLayers := fmax edgeNodeSpacing nodeNodeSpacing }
  monitor.done

/-- The `LabelDummySwitcher` processor. -/
def processor : LayeredProcessor := { name := "LabelDummySwitcher", process := process }

end LabelDummySwitcher

builtin_initialize registerLabelDummySwitcher : Unit ←
  IntermediateProcessorStrategy.register .labelDummySwitcher LabelDummySwitcher.processor

end Elk.Alg.Layered.Intermediate
