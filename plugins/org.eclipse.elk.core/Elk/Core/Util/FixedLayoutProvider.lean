import Elk.Core.Util.ElkUtil
import Elk.Core.LayoutProvider
import Elk.Core.Options
/-!
# `org.eclipse.elk.core.util.FixedLayoutProvider`

Keeps the layout given by `elk.position` / `elk.bendPoints` and only resizes
the parent (unless `nodeSize.fixedGraphSize`).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0

namespace Elk.Core.Util

open Elk.Graph Elk.Core Elk.Core.Math Elk.Core.Options

namespace FixedLayoutProvider

/-- `firstEndpointParent`: parent node of the first source/target. -/
private def firstEndpointParent (g : ElkGraph) (e : EdgeId) (isSource : Bool) : Option NodeId :=
  let edge := g.edge e
  let shape := if isSource then edge.sources[0]? else edge.targets[0]?
  (shape.bind (ElkGraphUtil.connectableShapeToNode g)).bind fun n => (g.node n).parent

/-- `generateJunctionPoints`. `ElkUtil.determineJunctionPoints` rejects an edge without exactly
one section with an `IllegalArgumentException` (Java; elk-rs panics with the same message), e.g.
an edge without authored bend points under orthogonal routing. -/
private def generateJunctionPoints (e : EdgeId) : ElkM Unit := do
  let g ← get
  let jps ← match ElkUtil.determineJunctionPoints g e with
    | .ok c => pure c
    | .error msg => throwIllegalArgument msg
  ElkM.modifyEdge e fun x =>
    { x with props := if jps.isEmpty then x.props.remove CoreOptions.JUNCTION_POINTS else x.props.set CoreOptions.JUNCTION_POINTS jps }

/-- `processEdge`: applies authored bend points and returns the maximal coordinates. -/
private def processEdge (e : EdgeId) : ElkM KVector := do
  let g ← get
  let sourceParent := firstEndpointParent g e true
  let targetParent := firstEndpointParent g e false
  let sameHierarchy := sourceParent == targetParent
  let mut maxv : KVector := {}
  if let some bendPoints := (g.edge e).props.get? FixedLayouterOptions.BEND_POINTS then
    if bendPoints.size >= 2 then
      let sections := (g.edge e).sections
      let sec ← (do
        if sections.isEmpty then
          ElkM.createSection (some e)
        else
          -- Java "throw[s] away all except for the last one" with `ListIterator.remove()` before
          -- any `next()`: `java.lang.IllegalStateException` (elk-rs keeps the last section)
          if sections.size > 1 then throw (IO.userError "java.lang.IllegalStateException")
          pure sections[0]!)
      ElkUtil.applyVectorChain bendPoints sec
  if sameHierarchy then
    let edge ← ElkM.getEdge e
    for s in edge.sections do
      for b in (← ElkM.getSection s).bendPoints do
        maxv := ⟨fmax maxv.x b.x, fmax maxv.y b.y⟩
  let labels := (← ElkM.getEdge e).labels
  for l in labels do
    if let some pos := (← ElkM.getLabel l).props.get? FixedLayouterOptions.POSITION then
      ElkM.modifyLabel l fun lb => { lb with x := pos.x, y := pos.y }
    if sameHierarchy then
      let lb ← ElkM.getLabel l
      maxv := ⟨fmax maxv.x (lb.x + lb.width), fmax maxv.y (lb.y + lb.height)⟩
  return maxv

/-- `FixedLayoutProvider.layout`. -/
def layout (layoutGraph : NodeId) (monitor : ProgressMonitor) : ElkM Unit := do
  let _ ← monitor.begin "Fixed Layout" fl1p0
  let edgeRouting := (← ElkM.getNode layoutGraph).props.getD CoreOptions.EDGE_ROUTING .undefined
  let mut maxx := fl0p0
  let mut maxy := fl0p0
  let children := (← ElkM.getNode layoutGraph).children
  for n in children do
    if let some pos := (← ElkM.getNode n).props.get? FixedLayouterOptions.POSITION then
      ElkM.modifyNode n fun nd => { nd with x := pos.x, y := pos.y }
      let constraints := (← ElkM.getNode n).props.getD FixedLayouterOptions.NODE_SIZE_CONSTRAINTS EnumSet.empty
      if constraints.contains .minimumSize then
        if let some minSize := (← ElkM.getNode n).props.get FixedLayouterOptions.NODE_SIZE_MINIMUM then
          if minSize.x > fl0p0 && minSize.y > fl0p0 then
            let _ ← ElkUtil.resizeNodeWith n minSize.x minSize.y true true
    let node ← ElkM.getNode n
    let (nodeX, nodeY) := (node.x, node.y)
    maxx := fmax maxx (node.x + node.width)
    maxy := fmax maxy (node.y + node.height)
    for l in node.labels do
      if let some pos := (← ElkM.getLabel l).props.get? FixedLayouterOptions.POSITION then
        ElkM.modifyLabel l fun lb => { lb with x := pos.x, y := pos.y }
      let lb ← ElkM.getLabel l
      maxx := fmax maxx (nodeX + lb.x + lb.width)
      maxy := fmax maxy (nodeY + lb.y + lb.height)
    for p in node.ports do
      if let some pos := (← ElkM.getPort p).props.get? FixedLayouterOptions.POSITION then
        ElkM.modifyPort p fun pt => { pt with x := pos.x, y := pos.y }
      let port ← ElkM.getPort p
      let absX := nodeX + port.x
      let absY := nodeY + port.y
      maxx := fmax maxx (absX + port.width)
      maxy := fmax maxy (absY + port.height)
      for l in port.labels do
        if let some pos := (← ElkM.getLabel l).props.get? FixedLayouterOptions.POSITION then
          ElkM.modifyLabel l fun lb => { lb with x := pos.x, y := pos.y }
        let lb ← ElkM.getLabel l
        maxx := fmax maxx (absX + lb.x + lb.width)
        maxy := fmax maxy (absY + lb.y + lb.height)
    for e in ElkGraphUtil.allOutgoingEdges (← get) n do
      let maxv ← processEdge e
      maxx := fmax maxx maxv.x
      maxy := fmax maxy maxv.y
    for e in ElkGraphUtil.allIncomingEdges (← get) n do
      if let some sourceParent := firstEndpointParent (← get) e true then
        if sourceParent != layoutGraph then
          let maxv ← processEdge e
          maxx := fmax maxx maxv.x
          maxy := fmax maxy maxv.y
  if edgeRouting == .orthogonal then
    for n in (← ElkM.getNode layoutGraph).children do
      for e in ElkGraphUtil.allOutgoingEdges (← get) n do
        generateJunctionPoints e
  let fixedGraphSize := (← ElkM.getNode layoutGraph).props.getD FixedLayouterOptions.NODE_SIZE_FIXED_GRAPH_SIZE false
  if !fixedGraphSize then
    let padding := (← ElkM.getNode layoutGraph).props.getD FixedLayouterOptions.PADDING {}
    let _ ← ElkUtil.resizeNodeWith layoutGraph (maxx + padding.left + padding.right) (maxy + padding.top + padding.bottom) true true
  monitor.done

def provider : LayoutProvider := { id := FixedLayouterOptions.ALGORITHM_ID, layout := layout }

end FixedLayoutProvider

end Elk.Core.Util
