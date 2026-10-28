import Std.Data.HashMap
import Elk.Core.Util.Java
import Elk.Core.Util.Sort
import Elk.Alg.MrTree.Graph.TArena
import Elk.Alg.MrTree.Options.MrTreeOptions
import Elk.Alg.MrTree.TreeUtil

/-!
# `org.eclipse.elk.alg.mrtree.intermediate.CompactionProcessor`

ELK Java's `CompactionProcessor` (elk-rs `intermediate/compaction_processor.rs` was the code
reference; ELK Java decides where they differ). Only active if `COMPACTION` is set. It

1. computes the extent of every tree level along the layout axis (`setUpLevels`; strict `<`/`>`
   comparisons starting at `(Double.MAX_VALUE, -Double.MAX_VALUE)`),
2. computes the compaction constraints by a sweep perpendicular to the layout direction over the
   node boxes enlarged by a quarter of the node spacing (`computeNodeConstraints`),
3. sorts the graph's node list **in place** by the projection of the node positions on the layout
   direction (so the later processors and the edge router see the new order) and moves every non-root
   node right behind its lowest dependent node (`COMPACT_CONSTRAINTS`) and its lowest parent
   (`TreeUtil.getLowestParent`); with `EDGE_ROUTING_MODE = AVOID_OVERLAP` the node keeps the new
   position if it lies within a level and otherwise snaps to the start of the next level
   (`COMPACT_LEVEL_ASCENSION`, new `TREE_LEVEL`).

ELK Java details (elk-rs differs in all of them):

* the sweep points are all box starts (in node order) followed by all box ends, sorted stably;
* the active set is a `TreeSet` ordered by the projection of the node positions on the layout
  direction: a node whose projection equals that of an active node is not added, `headSet`/
  `tailSet` are the active nodes strictly before / not before the node's projection, and `remove`
  removes the active node with the same projection;
* behind a dependent node, the parent wins for `RIGHT`/`DOWN` if `parent + spacing > newPos` (the
  parent's size is not in the test, but in the new position), for `LEFT`/`UP` if
  `parent - spacing - size < newPos`;
* `Direction.UNDEFINED` matches no `switch` case: the new position stays 0 and the lowest dependent
  node of several constraints is `null`;
* the found level is identified by `levels.indexOf` (`Pair.equals`, the first level with the same
  bounds by `Double.equals`).

Like Java, the sort keys of the main loop are read before the loop, while the positions of dependent
nodes and parents are read when they are needed (they may have been moved earlier in the loop).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl1p0 : Float := 1.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.MrTree.Intermediate

open Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.MrTree Elk.Alg.MrTree.Graph Elk.Alg.MrTree.Options

namespace CompactionProcessor

/-- `setUpLevels(tGraph, dir)`: `(first, second)` of every tree level along the layout axis. -/
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

/-- The `TreeSet<TNode>` of the sweep: the active nodes with their keys (the projection of the
position on the layout direction) in ascending `Double.compare` order, at most one node per key. -/
abbrev ActiveSet := Array (UInt64 × TNodeId)

/-- The index of the first element whose key is not below `k` (`tailSet` start). -/
private def lowerBound (s : ActiveSet) (k : UInt64) : Nat := Id.run do
  let mut lo := 0
  let mut hi := s.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if s[mid]!.1 < k then lo := mid + 1 else hi := mid
  return lo

/-- `s.add(r)`: no-op if a node with the same key is active. -/
private def setAdd (s : ActiveSet) (k : UInt64) (n : TNodeId) : ActiveSet :=
  let i := lowerBound s k
  if i < s.size && s[i]!.1 == k then s else s.insertIdx! i (k, n)

/-- `s.remove(r)`: removes the node with the same key. -/
private def setRemove (s : ActiveSet) (k : UInt64) : ActiveSet :=
  let i := lowerBound s k
  if i < s.size && s[i]!.1 == k then s.eraseIdx! i else s

/-- `s.headSet(r).last()` (`none` for an empty head set). -/
@[inline] private def headLast (s : ActiveSet) (k : UInt64) : Option TNodeId :=
  let i := lowerBound s k
  if i == 0 then none else some s[i - 1]!.2

/-- `getRightElement(s, r)` when `s.tailSet(r).size() > 1`: the second element of the tail set. -/
@[inline] private def tailSecond (s : ActiveSet) (k : UInt64) : Option TNodeId :=
  let i := lowerBound s k
  if i + 1 < s.size then some s[i + 1]!.2 else none

/-- `push_constraint(node, constraint)`: appends to `COMPACT_CONSTRAINTS`. -/
private def pushConstraint (node constraint : TNodeId) : MrTreeM Unit :=
  MrTreeM.modifyNode node fun n =>
    { n with internal.compactConstraints := n.internal.compactConstraints.push constraint }

/-- Substring test (`String.contains`). -/
private def containsStr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- `computeNodeConstraints(tGraph, nodeNodeSpacing)`. -/
def computeNodeConstraints (graph : TGraphId) (nodeNodeSpacing : Float) : MrTreeM Unit := do
  let a ← get
  let g := a.graph graph
  let direction := (g.props.get MrTreeOptions.DIRECTION).getD .undefined
  let rightDir : Direction := if direction.isHorizontal then .down else .right
  let actualNodes := g.nodes.filter fun n =>
    !(((a.node n).label.map fun l => containsStr l "SUPER_ROOT").getD false)
  -- all box starts in node order, then all box ends
  let mut points : Array (TNodeId × KVector × Bool) := Array.mkEmpty (2 * actualNodes.size)
  for node in actualNodes do
    let n := a.node node
    points := points.push (node, n.position.subValues nodeNodeSpacing nodeNodeSpacing, true)
  for node in actualNodes do
    let n := a.node node
    points := points.push (node, n.position.addValues (n.size.x + nodeNodeSpacing) (n.size.y + nodeNodeSpacing), false)
  let rightVec := TreeUtil.getDirectionVector rightDir
  let sortedPoints := javaSortByDouble points fun p => rightVec.dotProduct p.2.1
  let dirVec := TreeUtil.getDirectionVector direction
  let keyOf (n : TNodeId) : UInt64 := (dirVec.dotProduct (a.node n).position).javaOrderKey
  let mut active : ActiveSet := #[]
  let mut candidates : Std.HashMap TNodeId TNodeId := {}
  for (node, _, isStart) in sortedPoints do
    let k := keyOf node
    if isStart then
      active := setAdd active k node
      if let some left := headLast active k then
        candidates := candidates.insert node left
      if let some r := tailSecond active k then
        candidates := candidates.insert r node
    else
      if let some left := headLast active k then
        if candidates[node]? == some left then pushConstraint node left
      if let some r := tailSecond active k then
        if candidates[r]? == some node then pushConstraint r node
      active := setRemove active k

/-- `getLowestDependentNode(n, d)`: the compaction constraint that reaches furthest in the layout
direction (`Stream.min`/`max` with `Double.compare`: the first one on ties); `none` for no
constraint, and for several constraints with `Direction.UNDEFINED` (no `switch` case). -/
def getLowestDependentNode (a : TArena) (node : TNodeId) (direction : Direction) : Option TNodeId :=
  Id.run do
    let constraints := (a.node node).internal.compactConstraints
    if constraints.isEmpty then return none
    if constraints.size == 1 then return constraints[0]?
    if direction == .undefined then return none
    let lessIsFurther := direction == .left || direction == .up
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
        | some _ => Float.compareJava value bestValue == (if lessIsFurther then .lt else .gt)
      if isBetter then
        bestValue := value
        best := some candidate
    return best

/-- `TreeUtil.getLowestParent(n, g)` in ELK Java: the sources of the incoming edges in the order of
the graph's node list (`g.getNodes().stream().filter(sources::contains)`), the first whose centre has
the largest projection on the direction vector (`max(Comparator.naturalOrder())`, then the first
with `==`); `none` without incoming edges; `java.util.NoSuchElementException` if no source is in the
node list. -/
def getLowestParent (a : TArena) (listPos : Std.HashMap TNodeId Nat) (node : TNodeId) (direction : Direction) :
    Except String (Option TNodeId) := Id.run do
  let incoming := (a.node node).incomingEdges
  if incoming.isEmpty then return .ok none
  let sources := incoming.filterMap fun e => (a.edge e).source
  let dirVec := TreeUtil.getDirectionVector direction
  let score (p : TNodeId) : Float :=
    let pn := a.node p
    (KVector.mk (pn.position.x + pn.size.x / fl2p0) (pn.position.y + pn.size.y / fl2p0)).dotProduct dirVec
  -- the sources in node list order (`listPos`: first position of every listed node; a node listed
  -- twice appears twice in Java's filter, which changes neither the maximum nor the first match)
  let mut keyed : Array (Nat × TNodeId) := #[]
  for src in sources do
    if let some i := listPos.get? src then
      if !keyed.any (·.2 == src) then keyed := keyed.push (i, src)
  let parents := (stableSort keyed fun x y => compare x.1 y.1).map (·.2)
  let some first := parents[0]? | return .error "java.util.NoSuchElementException"
  let mut best := score first
  for p in parents do
    let s := score p
    if Float.compareJava best s == .lt then best := s
  -- `filter(x -> score(x) == lowestParentPos).findFirst().get()` (a NaN maximum matches nothing)
  match parents.find? fun p => score p == best with
  | some p => return .ok (some p)
  | none => return .error "java.util.NoSuchElementException"

/-- `CompactionProcessor.process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Process compaction" fl1p0
  let g ← MrTreeM.getGraph graph
  let enabled := (g.props.get MrTreeOptions.COMPACTION).getD false
  let direction := (g.props.get MrTreeOptions.DIRECTION).getD .undefined
  let s := (g.props.get MrTreeOptions.SPACING_NODE_NODE).getD fl0p0
  let routingMode := (g.props.get MrTreeOptions.EDGE_ROUTING_MODE).getD .avoidOverlap
  if !enabled then
    monitor.done
    return
  let levels := setUpLevels (← get) graph direction
  computeNodeConstraints graph (s / fl2p0 / fl2p0)
  let a ← get
  let dirVec := TreeUtil.getDirectionVector direction
  -- `nodes.sort(...)` sorts the graph's own node list
  let nodes := javaSortByDouble (a.graph graph).nodes fun n => dirVec.dotProduct (a.node n).position
  MrTreeM.modifyGraph graph fun x => { x with nodes }
  let mut listPos : Std.HashMap TNodeId Nat := {}
  for h : i in [0:nodes.size] do
    if !listPos.contains nodes[i] then listPos := listPos.insert nodes[i] i
  for node in nodes do
    let a ← get
    let n := a.node node
    if n.internal.root then continue
    let size := n.size
    let dependent := getLowestDependentNode a node direction
    let parent ← match getLowestParent a listPos node direction with
      | .ok p => pure p
      | .error e => throw (IO.userError e)
    let mut newPos := fl0p0
    let mut newPosSize := fl0p0
    if let some dep := dependent then
      -- Java dereferences the parent without a check
      let some par := parent | throw (IO.userError "java.lang.NullPointerException")
      let pos := (a.node dep).position
      let dsize := (a.node dep).size
      let p := a.node par
      match direction with
      | .left =>
        newPos := pos.x - s - size.x
        if p.position.x - s - size.x < newPos then newPos := p.position.x - s - size.x
        newPosSize := newPos + size.x
      | .right =>
        newPos := pos.x + dsize.x + s
        if p.position.x + s > newPos then newPos := p.position.x + p.size.x + s
        newPosSize := newPos + size.x
      | .up =>
        newPos := pos.y - s - size.y
        if p.position.y - s - size.y < newPos then newPos := p.position.y - s - size.y
        newPosSize := newPos + size.y
      | .down =>
        newPos := pos.y + dsize.y + s
        if p.position.y + s > newPos then newPos := p.position.y + p.size.y + s
        newPosSize := newPos + size.y
      | _ => pure ()
    else if let some par := parent then
      let p := a.node par
      match direction with
      | .left => newPos := p.position.x - s - size.x; newPosSize := newPos + size.x
      | .right => newPos := p.position.x + p.size.x + s; newPosSize := newPos + size.x
      | .up => newPos := p.position.y - s - size.y; newPosSize := newPos + size.y
      | .down => newPos := p.position.y + p.size.y + s; newPosSize := newPos + size.y
      | _ => pure ()
    if routingMode == .avoidOverlap then
      let setPos (v : Float) : MrTreeM Unit := MrTreeM.modifyNode node fun n =>
        if direction.isHorizontal then { n with position.x := v } else { n with position.y := v }
      -- the node ended up within a level: it keeps the new position
      let mut chosen : Option (Float × Float) := levels.find? fun (first, second) =>
        first <= newPos && second >= newPosSize
      if chosen.isSome then
        setPos newPos
      else
        -- force the node into the next level (the first level only holds the `SUPER_ROOT`)
        let lessIsFurther := direction == .left || direction == .up
        chosen := (levels.extract 1 levels.size).find? fun (first, _) =>
          if lessIsFurther then first <= newPos else first >= newPos
        if let some (first, _) := chosen then setPos first
      if let some (first, second) := chosen then
        -- `levels.indexOf(level)`: `Pair.equals` compares the bounds with `Double.equals`
        let newIndex := (levels.findIdx? fun (f, sc) => f.equalsJava first && sc.equalsJava second).getD 0
        let currentLevel := ((a.node node).props.get MrTreeOptions.TREE_LEVEL).getD 0
        if newIndex > 0 && (newIndex : Int) != currentLevel then
          MrTreeM.modifyNode node fun n =>
            { n with internal.compactLevelAscension := true,
                     props := n.props.set MrTreeOptions.TREE_LEVEL (newIndex : Int) }
    else
      MrTreeM.modifyNode node fun n =>
        if direction.isHorizontal then { n with position.x := newPos } else { n with position.y := newPos }
  monitor.done

/-- The `CompactionProcessor` (`IntermediateProcessorStrategy.COMPACTION_PROC`). -/
def processor : TreeProcessor := { name := "CompactionProcessor", process }

end CompactionProcessor

end Elk.Alg.MrTree.Intermediate
