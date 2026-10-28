import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
import Elk.Core.Util.ProgressMonitor
import Elk.Alg.MrTree.Graph.TArena
import Elk.Alg.MrTree.Options.MrTreeOptions
import Elk.Alg.MrTree.Intermediate.GraphBoundsProcessor
/-!
# `org.eclipse.elk.alg.mrtree.ComponentsProcessor`

Port of `components_processor.rs` (elk-rs).

`split` (only if `SEPARATE_CONNECTED_COMPONENTS`, `unwrap_or(true)`; otherwise the graph itself is the
only component): an undirected adjacency over the node list (nodes found through a map from the
integer node `id` to the list index, the last index winning for duplicate ids) is searched breadth
first from every unvisited node in list order. Each component is a new graph with the properties of
the input graph (public options and internal properties), its nodes in BFS order and the edges of the
input graph (in input order, deduplicated) whose both end points lie in the component. With more than
one component the nodes of every component are renumbered `0, 1, …`. An empty graph has no component.

`pack`: no component gives a new empty graph; one component is only normalised
(`apply_padding_and_normalize_positions`). Otherwise every component gets `PRIORITY` (the sum of its
nodes' priorities), `BB_UPLEFT`/`BB_LOWRIGHT` (bounding box of the node boxes); the components are
sorted stably by decreasing priority, then increasing box area (`partial_cmp`); the result graph takes
the properties of the first sorted component; the components are placed in rows of width
`max(widest box, sqrt(total area) * ASPECT_RATIO)` separated by `SPACING_NODE_NODE`; finally the
`GraphBoundsProcessor` runs on the result and the result is normalised.

`move_graph` adds the offset *minus* the source's `BB_UPLEFT` (so the box origin is subtracted twice
when packing, as in Rust) to the nodes and the bend points, and appends nodes and (deduplicated) edges
to the destination. `apply_padding_and_normalize_positions` sets `BB_UPLEFT := (0, 0)` and moves the
graph by `(padding.left - GRAPH_XMIN, padding.top - GRAPH_YMIN)` into a throw-away graph, which the
Lean port omits (`moveGraph` with no destination); the moved graph keeps its node and edge lists.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0

namespace Elk.Alg.MrTree

open Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options
open Elk.Alg.MrTree.Intermediate

namespace ComponentsProcessor

/-- `ComponentsProcessor::split(graph)`: the connected components (see the module doc). -/
def split (graph : TGraphId) : MrTreeM (Array TGraphId) := do
  let g ← MrTreeM.getGraph graph
  let separate := (g.props.get MrTreeOptions.SEPARATE_CONNECTED_COMPONENTS).getD true
  if !separate then return #[graph]
  let nodes := g.nodes
  let edges := g.edges
  let a ← get
  let mut idToIndex : Std.HashMap Int Nat := {}
  for idx in [0:nodes.size] do
    idToIndex := idToIndex.insert (a.node nodes[idx]!).id idx
  let mut adjacency : Array (Array Nat) := Array.replicate nodes.size #[]
  for e in edges do
    let (some s, some t) := ((a.edge e).source, (a.edge e).target) | continue
    if let (some si, some ti) := (idToIndex[(a.node s).id]?, idToIndex[(a.node t).id]?) then
      adjacency := adjacency.modify si (·.push ti)
      adjacency := adjacency.modify ti (·.push si)
  let mut visited : Array Bool := Array.replicate nodes.size false
  let mut components : Array TGraphId := #[]
  for startIdx in [0:nodes.size] do
    if visited[startIdx]! then continue
    let mut queue : Array Nat := #[startIdx]
    let mut head := 0
    let mut compIndices : Array Nat := #[]
    visited := visited.set! startIdx true
    while head < queue.size do
      let idx := queue[head]!
      head := head + 1
      compIndices := compIndices.push idx
      for neighbor in adjacency[idx]! do
        if !visited[neighbor]! then
          visited := visited.set! neighbor true
          queue := queue.push neighbor
    let compNodes := compIndices.map (nodes[·]!)
    let compSet : Std.HashSet TNodeId := compNodes.foldl (·.insert ·) {}
    let mut compEdges : Array TEdgeId := #[]
    let mut seenEdges : Std.HashSet TEdgeId := {}
    for e in edges do
      let (some s, some t) := ((a.edge e).source, (a.edge e).target) | continue
      if compSet.contains s && compSet.contains t && !seenEdges.contains e then
        seenEdges := seenEdges.insert e
        compEdges := compEdges.push e
    let comp ← MrTreeM.createGraph
    MrTreeM.modifyGraph comp fun c =>
      { c.copyProperties g with nodes := c.nodes ++ compNodes, edges := c.edges ++ compEdges }
    components := components.push comp
  if components.size > 1 then
    for comp in components do
      let compNodes := (← MrTreeM.getGraph comp).nodes
      for i in [0:compNodes.size] do
        MrTreeM.modifyNode compNodes[i]! fun n => { n with id := (i : Int) }
  return components

/-- `move_graph(dest, source, offsetx, offsety)`: moves the nodes and bend points of `source` by the
offset minus the source's `BB_UPLEFT` and appends them to `dest` (if any). -/
def moveGraph (dest : Option TGraphId) (source : TGraphId) (offsetx offsety : Float) : MrTreeM Unit := do
  let src ← MrTreeM.getGraph source
  let sourceMin := src.internal.bbUpleft.getD {}
  let graphOffset : KVector := KVector.sub ⟨offsetx, offsety⟩ sourceMin
  for node in src.nodes do
    MrTreeM.modifyNode node fun n => { n with position := n.position + graphOffset }
    if let some d := dest then MrTreeM.modifyGraph d fun x => { x with nodes := x.nodes.push node }
  let mut seenEdges : Std.HashSet TEdgeId := {}
  for edge in src.edges do
    if seenEdges.contains edge then continue
    seenEdges := seenEdges.insert edge
    MrTreeM.modifyEdge edge fun e => { e with bendPoints := e.bendPoints.map (· + graphOffset) }
    if let some d := dest then MrTreeM.modifyGraph d fun x => { x with edges := x.edges.push edge }

/-- `apply_padding_and_normalize_positions(graph)`. -/
def applyPaddingAndNormalizePositions (graph : TGraphId) : MrTreeM Unit := do
  let padding := ((← MrTreeM.getGraph graph).props.get MrTreeOptions.PADDING).getD {}
  MrTreeM.modifyGraph graph fun g => { g with internal.bbUpleft := some ⟨fl0p0, fl0p0⟩ }
  let g ← MrTreeM.getGraph graph
  let offsetX := padding.left - g.internal.graphXmin
  let offsetY := padding.top - g.internal.graphYmin
  moveGraph none graph offsetX offsetY

/-- `component_sort_values(graph)`: `(PRIORITY, box area)`. -/
private def componentSortValues (g : TGraph) : Int × Float :=
  let priority := (g.props.get MrTreeOptions.PRIORITY).getD 0
  let size := KVector.sub (g.internal.bbLowright.getD {}) (g.internal.bbUpleft.getD {})
  (priority, size.x * size.y)

/-- `ComponentsProcessor::pack(components)`: the packed graph (see the module doc). -/
def pack (components : Array TGraphId) : MrTreeM TGraphId := do
  if components.isEmpty then return ← MrTreeM.createGraph
  if components.size == 1 then
    applyPaddingAndNormalizePositions components[0]!
    return components[0]!
  for graph in components do
    let mut priority : Int := 0
    let mut minx := Float.maxValue
    let mut miny := Float.maxValue
    let mut maxx := Float.minValue
    let mut maxy := Float.minValue
    for node in (← MrTreeM.getGraph graph).nodes do
      let n ← MrTreeM.getNode node
      priority := priority + (n.props.get MrTreeOptions.PRIORITY).getD 0
      minx := fmin minx n.position.x
      miny := fmin miny n.position.y
      maxx := fmax maxx (n.position.x + n.size.x)
      maxy := fmax maxy (n.position.y + n.size.y)
    MrTreeM.modifyGraph graph fun g =>
      { g with props := g.props.set MrTreeOptions.PRIORITY priority,
               internal.bbUpleft := some ⟨minx, miny⟩, internal.bbLowright := some ⟨maxx, maxy⟩ }
  let a ← get
  let sorted := stableSort components fun x y =>
    let (prioA, sizeA) := componentSortValues (a.graph x)
    let (prioB, sizeB) := componentSortValues (a.graph y)
    match compare prioB prioA with
    | .eq => Float.comparePartial sizeA sizeB
    | o => o
  let first := a.graph sorted[0]!
  let result ← MrTreeM.createGraph
  MrTreeM.modifyGraph result (·.copyProperties first)
  let a ← get
  let mut maxRowWidth : Float := fl0p0
  let mut totalArea : Float := fl0p0
  for graph in sorted do
    let g := a.graph graph
    let diff := KVector.sub (g.internal.bbLowright.getD {}) (g.internal.bbUpleft.getD {})
    maxRowWidth := fmax maxRowWidth diff.x
    totalArea := totalArea + diff.x * diff.y
  let resultProps := (a.graph result).props
  let aspect := (resultProps.get MrTreeOptions.ASPECT_RATIO).getD fl1p0
  maxRowWidth := fmax maxRowWidth (totalArea.sqrt * aspect)
  let spacing := (resultProps.get MrTreeOptions.SPACING_NODE_NODE).getD fl0p0
  let mut xpos := fl0p0
  let mut ypos := fl0p0
  let mut highestBox := fl0p0
  for graph in sorted do
    let g ← MrTreeM.getGraph graph
    let min := g.internal.bbUpleft.getD {}
    let size := KVector.sub (g.internal.bbLowright.getD {}) min
    if xpos + size.x > maxRowWidth then
      xpos := fl0p0
      -- Rust `ypos += highest_box + spacing` (the sum first)
      ypos := ypos + (highestBox + spacing)
      highestBox := fl0p0
    moveGraph (some result) graph (xpos - min.x) (ypos - min.y)
    highestBox := fmax highestBox size.y
    -- Rust `xpos += size.x + spacing`
    xpos := xpos + (size.x + spacing)
  GraphBoundsProcessor.process result ProgressMonitor.null
  applyPaddingAndNormalizePositions result
  return result

end ComponentsProcessor

end Elk.Alg.MrTree
