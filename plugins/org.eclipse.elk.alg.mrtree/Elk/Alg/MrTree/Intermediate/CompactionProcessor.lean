import Std.Data.HashMap
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
import Elk.Alg.MrTree.Graph.TArena
import Elk.Alg.MrTree.Options.MrTreeOptions
import Elk.Alg.MrTree.TreeUtil
/-!
# `org.eclipse.elk.alg.mrtree.intermediate.CompactionProcessor`

Port of `intermediate/compaction_processor.rs` (elk-rs). Only active if `COMPACTION` is set. It

1. computes the extent of every tree level along the layout axis (`set_up_levels`; strict `<`/`>`
   comparisons starting at `(f64::MAX, -f64::MAX)`),
2. computes the compaction constraints by a sweep perpendicular to the layout direction over the
   node boxes enlarged by a quarter of the node spacing (`compute_node_constraints`; `SUPER_ROOT`
   nodes excluded, sweep points sorted stably by their projection on the perpendicular direction,
   the active list sorted by the projection of the node positions on the layout direction),
3. visits the non-root nodes in the (stable) order of the projection of their position on the
   layout direction and moves each one right behind its lowest dependent node (`COMPACT_CONSTRAINTS`)
   and its lowest parent (`TreeUtil.getLowestParent`); with `EDGE_ROUTING_MODE = AVOID_OVERLAP` the
   node snaps to the start of a level (`COMPACT_LEVEL_ASCENSION`, new `TREE_LEVEL`).

Like Rust, the sort keys, the root flags and the sizes of the main loop are read before the loop,
while the positions of dependent nodes and parents are read when they are needed (they may have
been moved earlier in the loop). The Rust pointer-keyed hash maps become id-keyed maps or direct
arena reads (the cached positions do not change while the constraints are computed).

Deviation: Rust converts `TREE_LEVEL` with `as usize` in `set_up_levels`; a negative level would wrap
to a huge index. The Lean port clamps it to 0 (`Int.toNat`), like `LevelCoordinatesProcessor`.
-/
namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.MrTree Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options

namespace CompactionProcessor

/-- `set_up_levels(graph, direction)`: `(start, end)` of every tree level along the layout axis. -/
def setUpLevels (a : TArena) (graph : TGraphId) (direction : Direction) : Array (Float × Float) :=
  Id.run do
    let mut levels : Array (Float × Float) := #[]
    for node in (a.graph graph).nodes do
      let n := a.node node
      let level := ((n.props.get MrTreeOptions.TREE_LEVEL).getD 0).toNat
      while level >= levels.size do
        levels := levels.push (Float.maxValue, -Float.maxValue)
      let (first, second) := levels[level]!
      let (lo, hi) := if direction.isHorizontal then (n.position.x, n.position.x + n.size.x)
        else (n.position.y, n.position.y + n.size.y)
      let first := if lo < first then lo else first
      let second := if hi > second then hi else second
      levels := levels.set! level (first, second)
    return levels

/-- `insert_sorted_cached`: inserts the node before the first active node whose position projects
further onto `dirVec`. -/
private def insertSorted (a : TArena) (active : Array TNodeId) (node : TNodeId) (dirVec : KVector) :
    Array TNodeId :=
  let nodeProj := dirVec.dotProduct (a.node node).position
  let index := (active.findIdx? fun other => nodeProj < dirVec.dotProduct (a.node other).position).getD active.size
  active.insertIdx! index node

/-- `left_neighbor(active, node)`. -/
private def leftNeighbor (active : Array TNodeId) (node : TNodeId) : Option TNodeId :=
  match active.idxOf? node with
  | some i => if i == 0 then none else active[i - 1]?
  | none => none

/-- `right_neighbor(active, node)`. -/
private def rightNeighbor (active : Array TNodeId) (node : TNodeId) : Option TNodeId :=
  match active.idxOf? node with
  | some i => if i + 1 >= active.size then none else active[i + 1]?
  | none => none

/-- `push_constraint(node, constraint)`: appends to `COMPACT_CONSTRAINTS`. -/
private def pushConstraint (node constraint : TNodeId) : MrTreeM Unit :=
  MrTreeM.modifyNode node fun n =>
    { n with internal.compactConstraints := n.internal.compactConstraints.push constraint }

/-- Substring test (`str::contains`). -/
private def containsStr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- `compute_node_constraints(graph, node_node_spacing)`. -/
def computeNodeConstraints (graph : TGraphId) (nodeNodeSpacing : Float) : MrTreeM Unit := do
  let a ← get
  let g := a.graph graph
  let direction := (g.props.get MrTreeOptions.DIRECTION).getD .undefined
  let rightDir : Direction := if direction.isHorizontal then .down else .right
  let actualNodes := g.nodes.filter fun n =>
    !(((a.node n).label.map fun l => containsStr l "SUPER_ROOT").getD false)
  let mut points : Array (TNodeId × KVector × Bool) := #[]
  for node in actualNodes do
    let n := a.node node
    points := points.push (node, n.position.subValues nodeNodeSpacing nodeNodeSpacing, true)
    points := points.push (node, n.position.addValues (n.size.x + nodeNodeSpacing) (n.size.y + nodeNodeSpacing), false)
  let rightVec := TreeUtil.getDirectionVector rightDir
  let sortedPoints := stableSort points fun p q =>
    Float.comparePartial (rightVec.dotProduct p.2.1) (rightVec.dotProduct q.2.1)
  let dirVec := TreeUtil.getDirectionVector direction
  let mut active : Array TNodeId := #[]
  let mut candidates : Std.HashMap TNodeId TNodeId := {}
  for (node, _, isStart) in sortedPoints do
    if isStart then
      active := insertSorted a active node dirVec
      if let some left := leftNeighbor active node then
        candidates := candidates.insert node left
      if let some r := rightNeighbor active node then
        candidates := candidates.insert r node
    else
      if let some left := leftNeighbor active node then
        if candidates[node]? == some left then pushConstraint node left
      if let some r := rightNeighbor active node then
        if candidates[r]? == some node then pushConstraint r node
      active := active.filter (· != node)

/-- `get_lowest_dependent_node(node, direction)`: the compaction constraint that reaches furthest in
the layout direction (the first one on ties). -/
def getLowestDependentNode (a : TArena) (node : TNodeId) (direction : Direction) : Option TNodeId :=
  Id.run do
    let constraints := (a.node node).internal.compactConstraints
    if constraints.isEmpty then return none
    if constraints.size == 1 then return constraints[0]?
    let mut best : Option TNodeId := none
    let mut bestValue := 0.0
    for candidate in constraints do
      let c := a.node candidate
      let value := match direction with
        | .left => c.position.x
        | .right => c.position.x + c.size.x
        | .up => c.position.y
        | _ => c.position.y + c.size.y
      let isBetter : Bool := match best with
        | none => true
        | some _ =>
          ((direction == .left || direction == .up) && value < bestValue) ||
          ((direction == .right || direction == .down || direction == .undefined) && value > bestValue)
      if isBetter then
        bestValue := value
        best := some candidate
    return best

/-- The new start coordinate (and end coordinate) of a node of `size` behind a node box
(`pos`, `size'`) in the layout direction. -/
private def behind (direction : Direction) (spacing : Float) (size pos otherSize : KVector) : Float × Float :=
  match direction with
  | .left => let p := pos.x - spacing - size.x; (p, p + size.x)
  | .right => let p := pos.x + otherSize.x + spacing; (p, p + size.x)
  | .up => let p := pos.y - spacing - size.y; (p, p + size.y)
  | _ => let p := pos.y + otherSize.y + spacing; (p, p + size.y)

/-- `CompactionProcessor::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Process compaction" 1.0
  let g ← MrTreeM.getGraph graph
  let enabled := (g.props.get MrTreeOptions.COMPACTION).getD false
  let direction := (g.props.get MrTreeOptions.DIRECTION).getD .undefined
  let nodeNodeSpacing := (g.props.get MrTreeOptions.SPACING_NODE_NODE).getD 0.0
  let routingMode := (g.props.get MrTreeOptions.EDGE_ROUTING_MODE).getD .avoidOverlap
  if !enabled then
    monitor.done
    return
  let levels := setUpLevels (← get) graph direction
  computeNodeConstraints graph (nodeNodeSpacing / 4.0)
  let a ← get
  let nodes := (a.graph graph).nodes
  let dirVec := TreeUtil.getDirectionVector direction
  -- sort keys, sizes and root flags are read before the loop
  let keyed := nodes.map fun n =>
    let x := a.node n
    (n, dirVec.dotProduct x.position, x.size, x.internal.root)
  let sorted := stableSort keyed fun p q => Float.comparePartial p.2.1 q.2.1
  for (node, _, size, isRoot) in sorted do
    if isRoot then continue
    let a ← get
    let dependent := getLowestDependentNode a node direction
    let parent := TreeUtil.getLowestParent a node direction
    let mut newPos := 0.0
    let mut newPosSize := 0.0
    if let some dep := dependent then
      if let some par := parent then
        let d := a.node dep
        let p := a.node par
        let (np, _) := behind direction nodeNodeSpacing size d.position d.size
        let (alt, _) := behind direction nodeNodeSpacing size p.position p.size
        let lessIsFurther := direction == .left || direction == .up
        let np := if (lessIsFurther && alt < np) || (!lessIsFurther && alt > np) then alt else np
        newPos := np
        newPosSize := np + (if direction.isHorizontal then size.x else size.y)
    else if let some par := parent then
      let p := a.node par
      let (np, nps) := behind direction nodeNodeSpacing size p.position p.size
      newPos := np
      newPosSize := nps
    if routingMode == .avoidOverlap then
      let mut chosen : Option (Nat × Float × Float) :=
        (levels.findIdx? fun (first, second) => first <= newPos && second >= newPosSize).map
          fun i => (i, levels[i]!)
      if chosen.isNone then
        let lessIsFurther := direction == .left || direction == .up
        for i in [1:levels.size] do
          let (first, second) := levels[i]!
          if (lessIsFurther && first <= newPos) || (!lessIsFurther && first >= newPos) then
            chosen := some (i, first, second)
            break
      if let some (index, first, _) := chosen then
        let currentLevel := ((a.node node).props.get MrTreeOptions.TREE_LEVEL).getD 0
        MrTreeM.modifyNode node fun n =>
          let n := if direction.isHorizontal then { n with position.x := first }
            else { n with position.y := first }
          if index > 0 && currentLevel != (index : Int) then
            { n with internal.compactLevelAscension := true,
                     props := n.props.set MrTreeOptions.TREE_LEVEL (index : Int) }
          else n
    else
      MrTreeM.modifyNode node fun n =>
        if direction.isHorizontal then { n with position.x := newPos } else { n with position.y := newPos }
  monitor.done

/-- The `CompactionProcessor` (`IntermediateProcessorStrategy.COMPACTION_PROC`). -/
def processor : TreeProcessor := { name := "CompactionProcessor", process }

end CompactionProcessor

end Elk.Alg.MrTree.Intermediate
