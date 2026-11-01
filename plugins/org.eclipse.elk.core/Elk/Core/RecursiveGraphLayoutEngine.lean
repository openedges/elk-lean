import Elk.Graph.Impl.EMapPropertyHolderImpl
import Elk.Core.Util
import Elk.Core.Data
import Elk.Core.Validation
import Elk.Core.LayoutProvider
import Elk.Core.Options
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# `org.eclipse.elk.core.RecursiveGraphLayoutEngine`

Lays out a compound graph bottom-up: resolves the algorithm of every node
(`LayoutAlgorithmResolver`; no option or graph validation, like ELK Java), then calls the
registered `LayoutProvider` for every hierarchy level, honouring
`elk.hierarchyHandling` (INCLUDE_CHILDREN), inside self loops and top-down layout.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl150p0 : Float := 150.0
private def fl1p414 : Float := 1.414

namespace Elk.Core

open Elk.Graph Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Core.Data Elk.Core.Validation

namespace RecursiveGraphLayoutEngine

/-- `getResolvedAlgorithm`: the `LayoutAlgorithmData` of `elk.resolvedAlgorithm`. -/
def getResolvedAlgorithm (n : NodeId) : ElkM (Option LayoutAlgorithmData) := do
  match (← ElkM.getNode n).props.get CoreOptions.RESOLVED_ALGORITHM with
  | some id => LayoutMetaDataService.getAlgorithmData id
  | none => return none

/-- `evaluateHierarchyHandlingInheritance`: resolves `INHERIT` from the parent. -/
def evaluateHierarchyHandlingInheritance (n : NodeId) : ElkM Unit := do
  let node ← ElkM.getNode n
  let handling := node.props.getD CoreOptions.HIERARCHY_HANDLING .inherit
  if handling == .inherit then
    match node.parent with
    | some p =>
      let parentHandling := (← ElkM.getNode p).props.getD CoreOptions.HIERARCHY_HANDLING .separateChildren
      ElkM.setNodeProp n CoreOptions.HIERARCHY_HANDLING parentHandling
    | none => ElkM.setNodeProp n CoreOptions.HIERARCHY_HANDLING .separateChildren

/-- `gatherInsideSelfLoops`: self loops routed inside the node. -/
def gatherInsideSelfLoops (n : NodeId) : ElkM (Array EdgeId) := do
  let g ← get
  let node := g.node n
  if !(node.props.getD CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE false) then return #[]
  let mut result : Array EdgeId := #[]
  for e in ElkGraphUtil.allOutgoingEdges g n do
    if !ElkGraphUtil.isSelfloop g e then continue
    if (g.edge e).props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false then result := result.push e
  return result

/-- `postProcessInsideSelfLoops`: moves the loops' coordinates to the node's parent space. -/
def postProcessInsideSelfLoops (loops : Array EdgeId) : ElkM Unit := do
  for e in loops do
    let g ← get
    let edge := g.edge e
    let some node := (edge.sources[0]?).bind (ElkGraphUtil.connectableShapeToNode g) | continue
    let nd := g.node node
    let (xo, yo) := (nd.x, nd.y)
    for s in edge.sections do
      ElkM.modifySection s fun sec => { sec with
        startX := sec.startX + xo, startY := sec.startY + yo, endX := sec.endX + xo, endY := sec.endY + yo,
        bendPoints := KVectorChain.offsetValues sec.bendPoints xo yo }
    if let some jps := edge.props.get? CoreOptions.JUNCTION_POINTS then
      ElkM.modifyEdge e fun x => { x with props := x.props.set CoreOptions.JUNCTION_POINTS (KVectorChain.offsetValues jps xo yo) }

/-- `countNodesRecursively`. -/
partial def countNodesRecursively (g : ElkGraph) (n : NodeId) (countAncestors : Bool) : Nat :=
  let children := (g.node n).children
  let count := children.foldl (fun acc c =>
    if (g.node c).children.isEmpty then acc else acc + countNodesRecursively g c false) children.size
  if countAncestors then
    let rec anc (cur : Option NodeId) (acc : Nat) : Nat :=
      match cur with
      | none => acc
      | some p => anc (g.node p).parent (acc + (g.node p).children.size)
    anc (g.node n).parent count
  else count

/-- `countNodesWithHierarchy`: nodes laid out together under INCLUDE_CHILDREN. -/
partial def countNodesWithHierarchy (parent : NodeId) : ElkM Nat := do
  let children := (← ElkM.getNode parent).children
  let mut count := children.size
  for child in children do
    let handling := (← ElkM.getNode child).props.getD CoreOptions.HIERARCHY_HANDLING .separateChildren
    if handling == .separateChildren then continue
    let parentAlgo ← getResolvedAlgorithm parent
    let childAlgo ← getResolvedAlgorithm child
    let sameAlgo := match parentAlgo, childAlgo with
      | some a, some b => a == b
      | _, _ => false
    if sameAlgo && !(← ElkM.getNode child).children.isEmpty then
      count := count + (← countNodesWithHierarchy child)
  return count

/-- `executeAlgorithm`: runs the provider registered for the algorithm. -/
def executeAlgorithm (layoutNode : NodeId) (data : LayoutAlgorithmData) (monitor : ProgressMonitor) : ElkM Unit := do
  let some provider ← LayoutProvider.create data.id
    | throwUnsupportedConfiguration s!"Layout algorithm '{data.id}' is not available in this build."
  provider.layout layoutNode monitor

private def setNodeDimensionsMin (n : NodeId) (size : KVector) : ElkM Unit :=
  ElkM.modifyNode n fun nd => { nd with width := fmax nd.width size.x, height := fmax nd.height size.y }

private def setNodeDimensionsWithPadding (n : NodeId) (size : KVector) (padding : ElkPadding) : ElkM Unit :=
  ElkM.modifyNode n fun nd => { nd with
    width := fmax nd.width (size.x + padding.left + padding.right),
    height := fmax nd.height (size.y + padding.top + padding.bottom) }

/-- `applyTopdownLayout`. -/
def applyTopdownLayout (layoutNode : NodeId) (children : Array NodeId) (data : LayoutAlgorithmData)
    (nodeCount : Nat) (monitor : ProgressMonitor) : ElkM Unit := do
  let topdownMonitor ← monitor.subTask fl1p0
  let _ ← topdownMonitor.begin "Topdown Layout" fl1p0
  let some nodeType := (← ElkM.getNode layoutNode).props.get CoreOptions.TOPDOWN_NODE_TYPE
    | throwUnsupportedConfiguration "Top-down layout node type has not been assigned."
  if nodeType == .hierarchicalNode || nodeType == .rootNode then
    for child in children do
      -- Java `childNode.getProperty(CoreOptions.PADDING)` for every child: the core default (12) is
      -- stored on the child when unset (cloneable default), so the child's own algorithm later
      -- reads 12 even if it redeclares the padding (e.g. `RectPackingOptions.PADDING` = 15)
      let padding := (← ElkM.getNodePropSticky child CoreOptions.PADDING).getD {}
      let childNode ← ElkM.getNode child
      if childNode.children.isEmpty then continue
      let mut handled := false
      if let some localData ← getResolvedAlgorithm child then
        if let some provider ← LayoutProvider.create localData.id then
          if let some predict := provider.predictedGraphSize then
            if childNode.props.get CoreOptions.TOPDOWN_NODE_TYPE == some .hierarchicalNode then
              throwUnsupportedConfiguration "Topdown layout providers should only be used on parallel nodes."
            let required ← predict child
            setNodeDimensionsMin child required
            handled := true
      if handled then continue
      match childNode.props.get CoreOptions.TOPDOWN_SIZE_APPROXIMATOR with
      | some approximator =>
        let size := (TopdownSizeApproximator.getSize approximator (← get) child).getD {}
        setNodeDimensionsWithPadding child size padding
      | none =>
        let width := childNode.props.getD CoreOptions.TOPDOWN_HIERARCHICAL_NODE_WIDTH fl150p0
        let aspectRatio := childNode.props.getD CoreOptions.TOPDOWN_HIERARCHICAL_NODE_ASPECT_RATIO fl1p414
        setNodeDimensionsWithPadding child ⟨width, width / aspectRatio⟩ padding
  -- Java `layoutNode.getProperty(CoreOptions.PADDING)` before the algorithm runs: stores the core
  -- default (12) when unset, which the algorithm's own padding read then sees
  let padding := (← ElkM.getNodePropSticky layoutNode CoreOptions.PADDING).getD {}
  let node ← ElkM.getNode layoutNode
  let childAreaAvailableWidth := node.width - (padding.left + padding.right)
  let childAreaAvailableHeight := node.height - (padding.top + padding.bottom)
  topdownMonitor.log s!"Available Child Area: ({Float.toRustDisplay childAreaAvailableWidth}|{Float.toRustDisplay childAreaAvailableHeight})"
  ElkM.setNodeProp layoutNode CoreOptions.ASPECT_RATIO (childAreaAvailableWidth / childAreaAvailableHeight)
  let fixedGraphSize := node.props.getD CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE false
  let originalSize := (node.width, node.height)
  let subMonitor ← monitor.subTask nodeCount.toFloat
  executeAlgorithm layoutNode data subMonitor
  if fixedGraphSize then
    ElkM.modifyNode layoutNode fun nd => { nd with width := originalSize.1, height := originalSize.2 }
  if nodeType == .rootNode then
    ElkUtil.computeChildAreaDimensions layoutNode
    let node ← ElkM.getNode layoutNode
    let caw := node.props.getD CoreOptions.CHILD_AREA_WIDTH fl0p0
    let cah := node.props.getD CoreOptions.CHILD_AREA_HEIGHT fl0p0
    ElkM.modifyNode layoutNode fun nd => { nd with
      width := padding.left + caw + padding.right, height := padding.top + cah + padding.bottom }
  let algorithmId := (← ElkM.getNode layoutNode).props.getD CoreOptions.ALGORITHM ""
  topdownMonitor.log s!"Executed layout algorithm: {algorithmId} on node"
  if nodeType == .hierarchicalNode then
    if childAreaAvailableWidth < fl0p0 || childAreaAvailableHeight < fl0p0 then
      throwUnsupportedConfiguration "The size defined by the parent parallel node is too small for the space provided by the paddings of the child hierarchical node."
    let node ← ElkM.getNode layoutNode
    if !(node.props.has CoreOptions.CHILD_AREA_WIDTH || node.props.has CoreOptions.CHILD_AREA_HEIGHT) then
      ElkUtil.computeChildAreaDimensions layoutNode
    let node ← ElkM.getNode layoutNode
    let desiredW := node.props.getD CoreOptions.CHILD_AREA_WIDTH fl0p0
    let desiredH := node.props.getD CoreOptions.CHILD_AREA_HEIGHT fl0p0
    topdownMonitor.log s!"Desired Child Area: ({Float.toRustDisplay desiredW}|{Float.toRustDisplay desiredH})"
    let scaleFactorX := childAreaAvailableWidth / desiredW
    let scaleFactorY := childAreaAvailableHeight / desiredH
    let scaleCap := node.props.getD CoreOptions.TOPDOWN_SCALE_CAP fl1p0
    let scaleFactor := fmin (fmin scaleFactorX scaleFactorY) scaleCap
    ElkM.setNodeProp layoutNode CoreOptions.TOPDOWN_SCALE_FACTOR scaleFactor
    topdownMonitor.log s!"Local Scale Factor (X|Y): ({Float.toRustDisplay scaleFactorX}|{Float.toRustDisplay scaleFactorY})"
    let contentAlignment := node.props.getD CoreOptions.CONTENT_ALIGNMENT ContentAlignment.topLeft
    let mut alignmentShiftX := fl0p0
    let mut alignmentShiftY := fl0p0
    if scaleFactor < scaleFactorX then
      if contentAlignment.contains .hCenter then
        alignmentShiftX := (childAreaAvailableWidth / fl2p0 - (desiredW * scaleFactor) / fl2p0) / scaleFactor
      else if contentAlignment.contains .hRight then
        alignmentShiftX := (childAreaAvailableWidth - desiredW * scaleFactor) / scaleFactor
    if scaleFactor < scaleFactorY then
      if contentAlignment.contains .vCenter then
        alignmentShiftY := (childAreaAvailableHeight / fl2p0 - (desiredH * scaleFactor) / fl2p0) / scaleFactor
      else if contentAlignment.contains .vBottom then
        alignmentShiftY := (childAreaAvailableHeight - desiredH * scaleFactor) / scaleFactor
    let xShift := alignmentShiftX + (padding.left / scaleFactor - padding.left)
    let yShift := alignmentShiftY + (padding.top / scaleFactor - padding.top)
    topdownMonitor.log s!"Shift: ({Float.toRustDisplay xShift}|{Float.toRustDisplay yShift})"
    for child in children do
      ElkM.modifyNode child fun nd => { nd with x := nd.x + xShift, y := nd.y + yShift }
    let edges := (← ElkM.getNode layoutNode).containedEdges
    for e in edges do
      let edge ← ElkM.getEdge e
      for s in edge.sections do
        ElkM.modifySection s fun sec => { sec with
          startX := sec.startX + xShift, startY := sec.startY + yShift,
          endX := sec.endX + xShift, endY := sec.endY + yShift,
          bendPoints := KVectorChain.offsetValues sec.bendPoints xShift yShift }
      for l in edge.labels do
        ElkM.modifyLabel l fun lb => { lb with x := lb.x + xShift, y := lb.y + yShift }
      if let some jps := edge.props.get? CoreOptions.JUNCTION_POINTS then
        ElkM.modifyEdge e fun x => { x with props := x.props.set CoreOptions.JUNCTION_POINTS (KVectorChain.offsetValues jps xShift yShift) }
  topdownMonitor.done

/-- `layoutRecursively`: returns the inside self loops the parent must handle. -/
partial def layoutRecursively (layoutNode : NodeId) (monitor : ProgressMonitor) : ElkM (Array EdgeId) := do
  if ← monitor.isCanceled then return #[]
  let node ← ElkM.getNode layoutNode
  if node.props.getD CoreOptions.NO_LAYOUT false then return #[]
  let children := node.children
  let insideSelfLoops ← gatherInsideSelfLoops layoutNode
  let hasInsideSelfLoops := !insideSelfLoops.isEmpty
  let hasChildren := !children.isEmpty
  if !hasChildren && !hasInsideSelfLoops then return #[]
  let some algorithmData ← getResolvedAlgorithm layoutNode
    | throwUnsupportedConfiguration "Resolved algorithm is not set; apply a LayoutAlgorithmResolver before computing layout."
  let supportsInsideSelfLoops := algorithmData.supportsFeature .insideSelfLoops
  if !hasChildren && hasInsideSelfLoops && !supportsInsideSelfLoops then return #[]
  evaluateHierarchyHandlingInheritance layoutNode
  let hierarchyHandling := (← ElkM.getNode layoutNode).props.getD CoreOptions.HIERARCHY_HANDLING .inherit
  let includeChildren := hierarchyHandling == .includeChildren
    && (algorithmData.supportsFeature .compound || algorithmData.supportsFeature .clusters)
  let topdownLayout := (← ElkM.getNode layoutNode).props.getD CoreOptions.TOPDOWN_LAYOUT false
  if includeChildren && topdownLayout then
    throwUnsupportedConfiguration "Topdown layout cannot be used together with hierarchy handling."
  let mut childrenInsideSelfLoops : Array EdgeId := #[]
  let mut nodeCount := 0
  if includeChildren then
    nodeCount ← countNodesWithHierarchy layoutNode
    let mut queue : Array NodeId := children
    let mut head := 0
    while head < queue.size do
      let n := queue[head]!
      head := head + 1
      evaluateHierarchyHandlingInheritance n
      let nd ← ElkM.getNode n
      let stopHierarchy := nd.props.getD CoreOptions.HIERARCHY_HANDLING .separateChildren == .separateChildren
      -- Java `!algorithmData.equals(node.getProperty(RESOLVED_ALGORITHM))`: a `NO_LAYOUT` node has no
      -- resolved algorithm (`LayoutAlgorithmResolver` skips it), so one with `ALGORITHM` is separate
      let algorithmSwitch := nd.props.has CoreOptions.ALGORITHM &&
        ((← getResolvedAlgorithm n).map (· != algorithmData)).getD true
      if stopHierarchy || algorithmSwitch then
        let subMonitor ← monitor.subTask fl1p0
        let childLoops ← layoutRecursively n subMonitor
        childrenInsideSelfLoops := childrenInsideSelfLoops ++ childLoops
        ElkM.setNodeProp n CoreOptions.HIERARCHY_HANDLING .separateChildren
        ElkUtil.applyConfiguredNodeScaling n
      else
        for gc in nd.children do queue := queue.push gc
  else
    nodeCount := children.size
    if topdownLayout then
      applyTopdownLayout layoutNode children algorithmData nodeCount monitor
    for child in children do
      let subMonitor ← monitor.subTask fl1p0
      let childLoops ← layoutRecursively child subMonitor
      childrenInsideSelfLoops := childrenInsideSelfLoops ++ childLoops
      ElkUtil.applyConfiguredNodeScaling child
  if ← monitor.isCanceled then return #[]
  for e in childrenInsideSelfLoops do
    ElkM.modifyEdge e fun x => { x with props := x.props.set CoreOptions.NO_LAYOUT true }
  if !topdownLayout then
    let subMonitor ← monitor.subTask nodeCount.toFloat
    executeAlgorithm layoutNode algorithmData subMonitor
  postProcessInsideSelfLoops childrenInsideSelfLoops
  return if hasInsideSelfLoops && supportsInsideSelfLoops then insideSelfLoops else #[]

/-- `RecursiveGraphLayoutEngine.layout(layoutGraph, progressMonitor)`: replaces deprecated options,
resolves the algorithms (`LayoutAlgorithmResolver`) and lays the graph out. Like ELK Java, the
engine runs no `LayoutOptionValidator` / `GraphValidator`: option bounds (`lowerBound` /
`upperBound` of the option metadata) and the graph structure are not checked, and
`elk.validateOptions` / `elk.validateGraph` are only read by Java's Eclipse `DiagramLayoutEngine`
(agent DIS). An out-of-range value reaches the algorithm, which lays the graph out or fails with
its own exception (e.g. force `iterations = 0` lays out, a rectpacking `desiredPosition` below
`-1` fails with `ArrayIndexOutOfBoundsException`). elk-rs (and elk-lean before DIS) applied both
validators here, `validateOptions` being on by default, and rejected such inputs with a
`GraphValidationException`. The validators stay available (`Elk.Core.Validation`) for explicit
use. -/
def layout (root : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  LayoutMetaDataService.ensureInitialized
  let nodeCount := countNodesRecursively (← get) root true
  let _ ← monitor.begin "Recursive Graph Layout" nodeCount.toFloat
  ElkUtil.applyVisitors root #[DeprecatedLayoutOptionReplacer.new]
  let resolver ← LayoutAlgorithmResolver.new
  ElkUtil.applyVisitors root #[resolver.toVisitor]
  if let some err := (← resolver.errors)[0]? then throw (IO.userError err)
  let _ ← layoutRecursively root monitor
  monitor.done

end RecursiveGraphLayoutEngine

end Elk.Core
