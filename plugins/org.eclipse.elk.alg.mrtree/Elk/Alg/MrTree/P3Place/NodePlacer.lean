import Std.Data.HashMap
import Elk.Core.Util.Java
import Elk.Alg.MrTree.TreeLayoutPhases
import Elk.Alg.MrTree.Options.MrTreeOptions
/-!
# `org.eclipse.elk.alg.mrtree.p3place.NodePlacer`

The phase `P3_NODE_PLACEMENT` of ELK Java: Walker's algorithm (`firstWalk`, `apportion`,
`secondWalk`) over the properties set by the `LevelHeightProcessor` and the `NeighborsProcessor`,
followed by the `DirectionProcessor` and the `NodePositionProcessor`. elk-rs replaced it by a
self-contained Reingold-Tilford pass over a breadth-first copy of the tree in which every node is
reached once (elk-lean followed it before agent RJ3); ELK Java walks the trees as they are:

* `getChildren()` are the targets of the outgoing edges, so a child linked by parallel edges (kept by
  the `BFS` treeification) or a node with several parents (`BFS`) is listed and visited once per
  edge; the levels of the `LevelHeightProcessor`/`NeighborsProcessor` are the concatenations of the
  children lists of the previous level, duplicates included, and the last assignment of a node's
  `LEVELHEIGHT`, neighbours and siblings wins (a node listed twice in a row becomes its own right and
  left sibling);
* `getParent()` is the source of the first incoming edge;
* positions are `(int) Math.round(x)` (half up), the direction transform works on these `int`s, the
  `NodePositionProcessor` copies them to the nodes reached from the root over the children lists and
  then moves *every* node of the graph by half its size.

The walker properties (`PRELIM`, `MODIFIER`, `LEVELHEIGHT`, `LEFTSIBLING`, `RIGHTSIBLING`,
`LEFTNEIGHBOR`, `XCOOR`, `YCOOR`) are not read by later phases, so they live in arrays indexed by a
dense node index (`Walker`) instead of the nodes. Java behaviour that cannot terminate is cut off: a
cycle of the first child and right sibling steps (e.g. a node that is its own right sibling) makes
`secondWalk` recurse forever (Java's `java.lang.StackOverflowError`; Lean finds the cycle before the
walk, `secondWalkLoops`, and throws the same error without writing any coordinate), a left sibling
chain that is a cycle makes `apportion` loop forever (Java hangs; Lean throws
`java.lang.StackOverflowError` too after as many steps as there are nodes), and a missing ancestor in
`apportion` is Java's `NullPointerException`. The recursions of `firstWalk`/`secondWalk` themselves
are not bounded: on trees deep enough to overflow Java's thread stack (a JVM setting) Lean still
lays the tree out.

`DIRECTION` `UNDEFINED` becomes `DOWN` and is written back to the graph (Java `NodePlacer.process`;
the `LevelHeightProcessor` runs before and still sees `UNDEFINED`, which is vertical).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl2p0 : Float := 2.0

namespace Elk.Alg.MrTree.P3Place

open Elk.Core.Alg Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Alg.MrTree Elk.Alg.MrTree.Graph
open Elk.Alg.MrTree.Options Elk.Alg.MrTree.Intermediate

namespace NodePlacer

/-- Java's `java.lang.StackOverflowError` (no message). -/
def stackOverflow : String := "java.lang.StackOverflowError"

/-- The walker state by dense node index. -/
structure Walker where
  nodes : Array TNodeId
  /-- `getChildren()`: the targets of the outgoing edges (duplicates included). -/
  children : Array (Array Nat)
  /-- `getParent()`: the source of the first incoming edge. -/
  parent : Array (Option Nat)
  /-- Half the node width (vertical direction) or height (`meanNodeWidth`). -/
  halfWidth : Array Float
  levelHeight : Array Float
  leftSibling : Array (Option Nat)
  rightSibling : Array (Option Nat)
  leftNeighbor : Array (Option Nat)
  prelim : Array Float
  modifier : Array Float
  xcoor : Array Int
  ycoor : Array Int
  deriving Inhabited

namespace Walker

/-- Indexes `n` (and the nodes reachable from it over children and parents) and fills the
structural arrays. -/
def build (a : TArena) (nodes : Array TNodeId) (isVertical : Bool) : Walker × Std.HashMap TNodeId Nat :=
  Id.run do
    let mut index : Std.HashMap TNodeId Nat := {}
    let mut order : Array TNodeId := #[]
    let mut queue := nodes
    let mut qi := 0
    -- index every node of the graph, then every node met as a child or parent
    while qi < queue.size do
      let n := queue[qi]!
      qi := qi + 1
      if index.contains n then continue
      index := index.insert n order.size
      order := order.push n
      let x := a.node n
      for e in x.outgoingEdges do
        if let some t := (a.edge e).target then
          if !index.contains t then queue := queue.push t
      if let some e := x.incomingEdges[0]? then
        if let some s := (a.edge e).source then
          if !index.contains s then queue := queue.push s
    let mut children : Array (Array Nat) := Array.mkEmpty order.size
    let mut parent : Array (Option Nat) := Array.mkEmpty order.size
    let mut halfWidth : Array Float := Array.mkEmpty order.size
    for n in order do
      let x := a.node n
      children := children.push (x.outgoingEdges.filterMap fun e => (a.edge e).target.bind index.get?)
      parent := parent.push (x.incomingEdges[0]?.bind fun e => (a.edge e).source.bind index.get?)
      halfWidth := halfWidth.push (if isVertical then x.size.x / fl2p0 else x.size.y / fl2p0)
    let k := order.size
    return ({ nodes := order, children, parent, halfWidth, levelHeight := Array.replicate k fl0p0,
              leftSibling := Array.replicate k none, rightSibling := Array.replicate k none,
              leftNeighbor := Array.replicate k none, prelim := Array.replicate k fl0p0,
              modifier := Array.replicate k fl0p0, xcoor := Array.replicate k 0,
              ycoor := Array.replicate k 0 }, index)

/-- The next level: the concatenation of the children lists of the level's entries. -/
@[inline] def nextLevel (w : Walker) (level : Array Nat) : Array Nat :=
  level.foldl (fun acc i => acc ++ w.children[i]!) #[]

/-- Bound of the level sizes (Java builds them lazily and would run out of time or memory). -/
def LEVEL_LIMIT : Nat := 50000000

/-- `LevelHeightProcessor.setNeighbors`: every entry of a level gets the largest node height
(vertical) or width of the level (`height < size`, starting at 0). -/
def setLevelHeights (a : TArena) (w : Walker) (root : Nat) (horizontal : Bool) : Except String Walker := do
  let mut w := w
  let mut level := #[root]
  let mut entries := 0
  while !level.isEmpty do
    entries := entries + level.size
    if entries > LEVEL_LIMIT then throw "java.lang.OutOfMemoryError: Java heap space"
    let mut height := fl0p0
    for i in level do
      let size := (a.node w.nodes[i]!).size
      let s := if horizontal then size.x else size.y
      if height < s then height := s
    for i in level do
      w := { w with levelHeight := w.levelHeight.set! i height }
    level := w.nextLevel level
  return w

/-- `NeighborsProcessor.setNeighbors` from the children of the root. -/
def setNeighbors (w : Walker) (root : Nat) : Walker := Id.run do
  let mut w := w
  let mut level := w.children[root]!
  while !level.isEmpty do
    let mut lN : Option Nat := none
    for cN in level do
      if let some l := lN then
        w := { w with leftNeighbor := w.leftNeighbor.set! cN (some l) }
        if w.parent[cN]! == w.parent[l]! then
          w := { w with rightSibling := w.rightSibling.set! l (some cN), leftSibling := w.leftSibling.set! cN (some l) }
      lN := some cN
    level := w.nextLevel level
  return w

/-- `meanNodeWidth(leftNode, rightNode)`. -/
@[inline] def meanNodeWidth (w : Walker) (left right : Nat) : Float :=
  w.halfWidth[left]! + w.halfWidth[right]!

/-- `TreeUtil.getLeftMost(currentLevel, depth)` over the children lists. -/
partial def getLeftMost (w : Walker) (currentLevel : Array Nat) (depth : Int) : Option Nat :=
  if currentLevel.isEmpty then none
  else if depth > 1 then getLeftMost w (w.nextLevel currentLevel) (depth - 1)
  else if depth < 0 then
    let next := w.nextLevel currentLevel
    if !next.isEmpty then getLeftMost w next depth else currentLevel[0]?
  else currentLevel[0]?

end Walker

/-- Java's `NullPointerException` of `apportion` (an ancestor of the leftmost node or of its neighbour
missing). -/
private def apportionNpe (var : String) : String :=
  s!"java.lang.NullPointerException: Cannot invoke \"org.eclipse.elk.alg.mrtree.graph.TNode.getProperty(org.eclipse.elk.graph.properties.IProperty)\" because \"{var}\" is null"

/-- `apportion(cN, level)`. -/
def apportion (spacing : Float) (w : Walker) (cN : Nat) : Except String Walker := do
  let mut w := w
  let children := w.children[cN]!
  let mut leftmost : Option Nat := children[0]?
  let mut neighbor : Option Nat := leftmost.bind fun lm => w.leftNeighbor[lm]!
  let mut compareDepth : Nat := 1
  while true do
    let (some lm, some nb) := (leftmost, neighbor) | break
    let mut leftModSum := fl0p0
    let mut rightModSum := fl0p0
    let mut ancestorLeftmost : Option Nat := some lm
    let mut ancestorNeighbor : Option Nat := some nb
    for _ in [0:compareDepth] do
      ancestorLeftmost := ancestorLeftmost.bind fun x => w.parent[x]!
      ancestorNeighbor := ancestorNeighbor.bind fun x => w.parent[x]!
      let some al := ancestorLeftmost | throw (apportionNpe "ancestorLeftmost")
      rightModSum := rightModSum + w.modifier[al]!
      let some an := ancestorNeighbor | throw (apportionNpe "ancestorNeighbor")
      leftModSum := leftModSum + w.modifier[an]!
    let ancestorNb := ancestorNeighbor.getD 0
    let mean := w.meanNodeWidth lm nb
    let mut moveDistance := w.prelim[nb]! + leftModSum + spacing + mean - w.prelim[lm]! - rightModSum
    if 0.0 < moveDistance then
      let mut leftSibling : Option Nat := some cN
      let mut leftSiblings : Nat := 0
      let mut steps := 0
      while true do
        let some ls := leftSibling | break
        if ls == ancestorNb then break
        steps := steps + 1
        -- a cyclic left sibling chain: Java loops forever
        if steps > w.nodes.size then throw stackOverflow
        leftSiblings := leftSiblings + 1
        leftSibling := w.leftSibling[ls]!
      if leftSibling.isSome then
        let portion := moveDistance / Float.ofNat leftSiblings
        let mut cur := cN
        while cur != ancestorNb do
          w := { w with prelim := w.prelim.modify cur (· + moveDistance),
                        modifier := w.modifier.modify cur (· + moveDistance) }
          moveDistance := moveDistance - portion
          -- the chain reaches `ancestorNeighbor` (checked above)
          cur := (w.leftSibling[cur]!).getD ancestorNb
      else
        return w
    compareDepth := compareDepth + 1
    if w.children[lm]!.isEmpty then
      leftmost := w.getLeftMost children compareDepth
    else
      leftmost := w.children[lm]![0]?
    neighbor := leftmost.bind fun x => w.leftNeighbor[x]!
  return w

/-- `firstWalk(cN, level)`. -/
partial def firstWalk (spacing : Float) (w : Walker) (cN : Nat) : Except String Walker := do
  let mut w := { w with modifier := w.modifier.set! cN fl0p0 }
  let lS := w.leftSibling[cN]!
  let children := w.children[cN]!
  if children.isEmpty then
    let p := match lS with
      | some l => w.prelim[l]! + spacing + w.meanNodeWidth l cN
      | none => fl0p0
    return { w with prelim := w.prelim.set! cN p }
  for child in children do
    w ← firstWalk spacing w child
  let lM := children[0]!
  let rM := children[children.size - 1]!
  let midPoint := (w.prelim[rM]! + w.prelim[lM]!) / fl2p0
  match lS with
  | some l =>
    let p := w.prelim[l]! + spacing + w.meanNodeWidth l cN
    w := { w with prelim := w.prelim.set! cN p, modifier := w.modifier.set! cN (p - midPoint) }
    apportion spacing w cN
  | none => return { w with prelim := w.prelim.set! cN midPoint }

/-- Java `(int) Math.round(x)`: round half up (`floor(x + 0.5)`; elk-rs rounds half away from zero,
which differs for negative halves such as `-2.5`), saturated to `long`, then narrowed to `int`
(two's complement wrap; NaN to 0). -/
@[inline] def roundToI32 (x : Float) : Int :=
  Int.wrap32 (Float.javaRound x)

/-- Whether `secondWalk` from `root` recurses forever: a cycle of the "first child" and "right
sibling" steps it follows (Java's `java.lang.StackOverflowError`). Iterative three-colour search. -/
def secondWalkLoops (w : Walker) (root : Nat) : Bool := Id.run do
  -- 0 unvisited, 1 on the stack, 2 done
  let mut color : Array UInt8 := Array.replicate w.nodes.size 0
  let mut stack : Array (Nat × Nat) := #[(root, 0)]
  color := color.set! root 1
  while !stack.isEmpty do
    let (t, k) := stack.back!
    let next : Option Nat :=
      if k == 0 then w.children[t]![0]? else if k == 1 then w.rightSibling[t]! else none
    if k ≥ 2 then
      stack := stack.pop
      color := color.set! t 2
      continue
    stack := stack.set! (stack.size - 1) (t, k + 1)
    if let some n := next then
      if color[n]! == 1 then return true
      if color[n]! == 0 then
        color := color.set! n 1
        stack := stack.push (n, 0)
  return false

/-- `secondWalk(tNode, yCoor, modsum)` (terminates: `secondWalkLoops` is false). -/
partial def secondWalk (spacing : Float) (w : Walker) (tNode : Nat) (yCoor modsum : Float) : Walker := Id.run do
  let xTemp := w.prelim[tNode]! + modsum
  let yTemp := yCoor + w.levelHeight[tNode]! / fl2p0
  let mut w := { w with xcoor := w.xcoor.set! tNode (roundToI32 xTemp),
                        ycoor := w.ycoor.set! tNode (roundToI32 yTemp) }
  if let some first := w.children[tNode]![0]? then
    w := secondWalk spacing w first (yCoor + w.levelHeight[tNode]! + spacing) (modsum + w.modifier[tNode]!)
  if let some rs := w.rightSibling[tNode]! then
    w := secondWalk spacing w rs yCoor modsum
  return w

/-- `NodePlacer.process` with the `LevelHeightProcessor` and `NeighborsProcessor` before it and the
`DirectionProcessor` and `NodePositionProcessor` after it (see the module doc). -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Processor order nodes" 2.0
  let g ← MrTreeM.getGraph graph
  let spacing := (g.props.get MrTreeOptions.SPACING_NODE_NODE).getD 0.0
  let levelDirection := (g.props.get MrTreeOptions.DIRECTION).getD .undefined
  let mut direction := levelDirection
  if direction == .undefined then
    direction := .down
    MrTreeM.setGraphProp graph MrTreeOptions.DIRECTION direction
  let a ← get
  let nodes := g.nodes
  -- Java `roots.getFirst()` (every processor takes the first `ROOT` of the node list)
  let some rootNode := nodes.find? fun n => (a.node n).internal.root
    | throw (IO.userError "java.util.NoSuchElementException")
  let (w, index) := Walker.build a nodes direction.isVertical
  let root := index[rootNode]!
  let w ← match Walker.setLevelHeights a w root levelDirection.isHorizontal with
    | .ok w => pure w
    | .error e => throw (IO.userError e)
  let w := Walker.setNeighbors w root
  let w ← match firstWalk spacing w root with
    | .ok w => pure w
    | .error e => throw (IO.userError e)
  monitor.worked 1.0
  if secondWalkLoops w root then throw (IO.userError stackOverflow)
  let w := secondWalk spacing w root (fl0p0 - w.levelHeight[root]! / fl2p0) fl0p0
  monitor.worked 1.0
  -- `DirectionProcessor` (on the `int` coordinates of every listed node) and `NodePositionProcessor`
  let mut w := w
  if direction != .down then
    for n in nodes do
      let i := index[n]!
      let x := w.xcoor[i]!
      let y := w.ycoor[i]!
      let (x, y) := match direction with
        | .up => (x, Int.wrap32 (-y))
        | .right => (y, x)
        | .left => (Int.wrap32 (-y), x)
        | _ => (x, y)
      w := { w with xcoor := w.xcoor.set! i x, ycoor := w.ycoor.set! i y }
  let setPos (i : Nat) : MrTreeM Unit :=
    MrTreeM.modifyNode w.nodes[i]! fun n => { n with position := ⟨Float.ofInt w.xcoor[i]!, Float.ofInt w.ycoor[i]!⟩ }
  setPos root
  let mut level := w.children[root]!
  while !level.isEmpty do
    for i in level do setPos i
    level := w.nextLevel level
  for n in nodes do
    MrTreeM.modifyNode n fun x => { x with position := ⟨x.position.x - x.size.x / fl2p0, x.position.y - x.size.y / fl2p0⟩ }
  monitor.done

/-- `getLayoutProcessorConfiguration`: `ROOT_PROC` before `P2_NODE_ORDERING` (the
`LEVEL_HEIGHT`/`NEIGHBORS_PROC` and `DIRECTION_PROC`/`NODE_POSITION_PROC` of Java are part of
`process`; no other processor runs between them and this phase). -/
def configuration : TreeProcessorConfiguration :=
  LayoutProcessorConfiguration.create.addBefore TreeLayoutPhases.p2NodeOrdering
    IntermediateProcessorStrategy.rootProc

/-- The `NodePlacer` phase. -/
def phase : TreePhase :=
  { name := "NodePlacer", process, getLayoutProcessorConfiguration := fun _ => pure (some configuration) }

end NodePlacer

end Elk.Alg.MrTree.P3Place
