import Std.Data.HashMap
import Elk.Core.Util.Java
import Elk.Alg.MrTree.TreeLayoutPhases
import Elk.Alg.MrTree.Options.MrTreeOptions
/-!
# `org.eclipse.elk.alg.mrtree.p3place.NodePlacer`

Port of `p3place/node_placer.rs` (elk-rs), the phase `P3_NODE_PLACEMENT`. elk-rs replaces the Java
implementation (Walker's algorithm over the `LEVELHEIGHT`/neighbour properties, followed by the
`DirectionProcessor` and `NodePositionProcessor`) by a self-contained Reingold-Tilford pass over a
struct-of-arrays copy of the tree (`TreeSoA`); this port follows Rust:

1. `TreeSoA::build`: breadth first from the first `ROOT` node over the `direct_children` caches; a
   child already reached is skipped (it gets no second parent), but a node whose cache is non-empty
   is no leaf even if all its children were skipped. Per node: half the width (vertical direction)
   or height (horizontal), half the size, and the full height (vertical) or width (horizontal); per
   BFS level the level height is the maximum full extent (`f64::max` from 0); consecutive nodes of a
   level are left neighbours, and siblings if their BFS parents coincide.
2. `first_walk`: post-order prelim/modifier computation; a leaf is placed `spacing + mean width`
   right of its left sibling, an inner node centred over its first and last child or, with a left
   sibling, right of it with `modifier = prelim - midpoint` followed by `apportion`.
3. `apportion`: Rust's bounded variant (at most 256 rounds; gives up when an ancestor, a left sibling
   chain or the ancestor neighbour is missing; distributes the move over the left siblings between
   the node and the ancestor neighbour).
4. `second_walk`: `x = prelim + modifier sum`, `y = level top + level height / 2`, both rounded
   (`f64::round`, then `as i32`, saturating) and transformed by the layout direction (Rust inlines
   the `DirectionProcessor`); the node position becomes the integer centre minus half the node
   size (Rust inlines the `NodePositionProcessor`). `XCOOR`/`YCOOR`/`PRELIM`/`MODIFIER` are not
   written. Nodes not reached from the root keep their positions.

`DIRECTION` is read with `unwrap_or(UNDEFINED)`; `UNDEFINED` becomes `DOWN` and is written back to
the graph. `SPACING_NODE_NODE` is read with `unwrap_or(0.0)`. The processor configuration only slots
`ROOT_PROC` before `P2_NODE_ORDERING`.

Rust indexes `children[0]` of a non-leaf node without children (only possible if a node has two
parents in the treeified graph, e.g. after a `BFS` treeification); that panics in Rust and throws
`IndexOutOfBoundsException` here.
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

/-- `TreeSoA`: the tree in BFS order (index 0 = root). -/
structure TreeSoA where
  nodes : Array TNodeId
  children : Array (Array Nat)
  parent : Array (Option Nat)
  leftSibling : Array (Option Nat)
  leftNeighbor : Array (Option Nat)
  rightSibling : Array (Option Nat)
  isLeaf : Array Bool
  halfWidth : Array Float
  halfSizeX : Array Float
  halfSizeY : Array Float
  levelheight : Array Float
  prelim : Array Float
  modifier : Array Float
  deriving Inhabited

namespace TreeSoA

/-- `TreeSoA::build(root, is_vertical)`. -/
def build (a : TArena) (root : TNodeId) (isVertical : Bool) : TreeSoA := Id.run do
  let mut nodes : Array TNodeId := #[root]
  let mut indexMap : Std.HashMap TNodeId Nat := ({} : Std.HashMap TNodeId Nat).insert root 0
  let mut childrenVec : Array (Array Nat) := #[#[]]
  let mut parentVec : Array (Option Nat) := #[none]
  let mut isLeafVec : Array Bool := #[true]
  let mut halfWidthVec : Array Float := #[fl0p0]
  let mut halfSizeXVec : Array Float := #[fl0p0]
  let mut halfSizeYVec : Array Float := #[fl0p0]
  let mut fullDimVec : Array Float := #[fl0p0]
  let mut levelRanges : Array (Nat × Nat) := #[]
  let mut levelStart := 0
  let mut levelEnd := 1
  while levelStart < levelEnd do
    levelRanges := levelRanges.push (levelStart, levelEnd)
    for idx in [levelStart:levelEnd] do
      let node := a.node nodes[idx]!
      let size := node.size
      halfWidthVec := halfWidthVec.set! idx (if isVertical then size.x / fl2p0 else size.y / fl2p0)
      halfSizeXVec := halfSizeXVec.set! idx (size.x / fl2p0)
      halfSizeYVec := halfSizeYVec.set! idx (size.y / fl2p0)
      fullDimVec := fullDimVec.set! idx (if isVertical then size.y else size.x)
      let childRefs := node.directChildren
      isLeafVec := isLeafVec.set! idx childRefs.isEmpty
      let mut childIndices : Array Nat := #[]
      for child in childRefs do
        if !indexMap.contains child then
          let ci := nodes.size
          indexMap := indexMap.insert child ci
          nodes := nodes.push child
          childrenVec := childrenVec.push #[]
          parentVec := parentVec.push (some idx)
          isLeafVec := isLeafVec.push true
          halfWidthVec := halfWidthVec.push fl0p0
          halfSizeXVec := halfSizeXVec.push fl0p0
          halfSizeYVec := halfSizeYVec.push fl0p0
          fullDimVec := fullDimVec.push fl0p0
          childIndices := childIndices.push ci
      childrenVec := childrenVec.set! idx childIndices
      -- a node whose children were all reached before (a BFS treeification of a cyclic graph can
      -- leave a node with several parents; Java walks such a child once per parent) is a leaf of the
      -- tree arrays: elk-rs keeps `is_leaf = false` and panics on its empty child list (agent OPT;
      -- the multi-parent placement of Java is not reproduced)
      if childIndices.isEmpty then isLeafVec := isLeafVec.set! idx true
    levelStart := levelEnd
    levelEnd := nodes.size
  let n := nodes.size
  let mut levelheight : Array Float := Array.replicate n fl0p0
  let mut leftSibling : Array (Option Nat) := Array.replicate n none
  let mut leftNeighbor : Array (Option Nat) := Array.replicate n none
  let mut rightSibling : Array (Option Nat) := Array.replicate n none
  for (start, stop) in levelRanges do
    let mut height : Float := fl0p0
    for i in [start:stop] do
      height := fmax height fullDimVec[i]!
    let mut prev : Option Nat := none
    for idx in [start:stop] do
      levelheight := levelheight.set! idx height
      if let some p := prev then
        leftNeighbor := leftNeighbor.set! idx (some p)
        if parentVec[p]! == parentVec[idx]! then
          leftSibling := leftSibling.set! idx (some p)
          rightSibling := rightSibling.set! p (some idx)
      prev := some idx
  return { nodes, children := childrenVec, parent := parentVec, leftSibling, leftNeighbor,
           rightSibling, isLeaf := isLeafVec, halfWidth := halfWidthVec, halfSizeX := halfSizeXVec,
           halfSizeY := halfSizeYVec, levelheight, prelim := Array.replicate n fl0p0,
           modifier := Array.replicate n fl0p0 }

/-- `mean_node_width(left, right)`. -/
@[inline] def meanNodeWidth (soa : TreeSoA) (left right : Nat) : Float :=
  soa.halfWidth[left]! + soa.halfWidth[right]!

/-- `get_left_most(start_children, depth)`. -/
partial def getLeftMost (soa : TreeSoA) (startChildren : Array Nat) (depth : Int) : Option Nat :=
  if startChildren.isEmpty then none
  else if depth > 1 then
    getLeftMost soa (startChildren.foldl (fun acc i => acc ++ soa.children[i]!) #[]) (depth - 1)
  else if depth < 0 then
    let nextLevel := startChildren.foldl (fun acc i => acc ++ soa.children[i]!) #[]
    if !nextLevel.isEmpty then getLeftMost soa nextLevel depth else startChildren[0]?
  else startChildren[0]?

end TreeSoA

/-- `apportion_soa(soa, node_idx)`. -/
def apportion (spacing : Float) (soa : TreeSoA) (nodeIdx : Nat) : TreeSoA := Id.run do
  let mut soa := soa
  let children := soa.children[nodeIdx]!
  let mut leftmost : Option Nat := children[0]?
  let mut neighbor : Option Nat := leftmost.bind fun lm => soa.leftNeighbor[lm]!
  let mut compareDepth : Nat := 1
  let mut apportionIterations := 0
  while true do
    let (some lmIdx, some nbIdx) := (leftmost, neighbor) | break
    apportionIterations := apportionIterations + 1
    if apportionIterations > 256 then return soa
    let mut leftModSum := 0.0
    let mut rightModSum := 0.0
    let mut ancestorLeftmost := lmIdx
    let mut ancestorNeighbor := nbIdx
    for _ in [0:compareDepth] do
      let some alp := soa.parent[ancestorLeftmost]! | return soa
      let some anp := soa.parent[ancestorNeighbor]! | return soa
      ancestorLeftmost := alp
      ancestorNeighbor := anp
      rightModSum := rightModSum + soa.modifier[ancestorLeftmost]!
      leftModSum := leftModSum + soa.modifier[ancestorNeighbor]!
    let mean := soa.meanNodeWidth lmIdx nbIdx
    let mut moveDistance := soa.prelim[nbIdx]! + leftModSum + spacing + mean - soa.prelim[lmIdx]!
      - rightModSum
    if moveDistance > 0.0 then
      let mut current := nodeIdx
      let mut leftSiblings := 0
      let mut found := false
      let mut seenCount := 0
      while true do
        seenCount := seenCount + 1
        if seenCount > soa.nodes.size then return soa
        if current == ancestorNeighbor then
          found := true
          break
        leftSiblings := leftSiblings + 1
        match soa.leftSibling[current]! with
        | some ls => current := ls
        | none => break
      if !found || leftSiblings == 0 then return soa
      let portion := moveDistance / Float.ofNat leftSiblings
      current := nodeIdx
      seenCount := 0
      while current != ancestorNeighbor do
        seenCount := seenCount + 1
        if seenCount > soa.nodes.size then return soa
        soa := { soa with
          prelim := soa.prelim.modify current (· + moveDistance)
          modifier := soa.modifier.modify current (· + moveDistance) }
        moveDistance := moveDistance - portion
        match soa.leftSibling[current]! with
        | some ls => current := ls
        | none => return soa
    compareDepth := compareDepth + 1
    if soa.isLeaf[lmIdx]! then
      leftmost := soa.getLeftMost children compareDepth
    else
      leftmost := soa.children[lmIdx]![0]?
    neighbor := leftmost.bind fun lm => soa.leftNeighbor[lm]!
  return soa

/-- `first_walk_soa(soa, idx)`. -/
partial def firstWalk (spacing : Float) (soa : TreeSoA) (idx : Nat) : Except String TreeSoA := do
  let mut soa := { soa with modifier := soa.modifier.set! idx 0.0 }
  if soa.isLeaf[idx]! then
    let prelim := match soa.leftSibling[idx]! with
      | some ls => soa.prelim[ls]! + spacing + soa.meanNodeWidth ls idx
      | none => 0.0
    return { soa with prelim := soa.prelim.set! idx prelim }
  let children := soa.children[idx]!
  for child in children do
    soa ← firstWalk spacing soa child
  let some firstChild := children[0]?
    | throw "java.lang.IndexOutOfBoundsException: index out of bounds: the len is 0 but the index is 0"
  let lastChild := children[children.size - 1]!
  let midPoint := (soa.prelim[lastChild]! + soa.prelim[firstChild]!) / 2.0
  match soa.leftSibling[idx]! with
  | some ls =>
    let p := soa.prelim[ls]! + spacing + soa.meanNodeWidth ls idx
    soa := { soa with prelim := soa.prelim.set! idx p, modifier := soa.modifier.set! idx (p - midPoint) }
    return apportion spacing soa idx
  | none => return { soa with prelim := soa.prelim.set! idx midPoint }

/-- Rust `x.round() as i32` (round half away from zero, saturating, NaN to 0). -/
@[inline] def roundToI32 (x : Float) : Int :=
  max (-2147483648) (min 2147483647 (Float.roundToInt x))

/-- `second_walk_soa(soa, idx, y_coor, mod_sum)`: appends the final positions (by SoA index). -/
partial def secondWalk (spacing : Float) (direction : Direction) (soa : TreeSoA) (idx : Nat)
    (yCoor modSum : Float) (acc : Array (Nat × KVector)) : Array (Nat × KVector) := Id.run do
  let xTemp := soa.prelim[idx]! + modSum
  let yTemp := yCoor + soa.levelheight[idx]! / 2.0
  let xr := roundToI32 xTemp
  let yr := roundToI32 yTemp
  let (xcoor, ycoor) : Int × Int := match direction with
    | .up => (xr, -yr)
    | .right => (yr, xr)
    | .left => (-yr, xr)
    | _ => (xr, yr)
  let posX := Float.ofInt xcoor - soa.halfSizeX[idx]!
  let posY := Float.ofInt ycoor - soa.halfSizeY[idx]!
  let mut acc := acc.push (idx, ⟨posX, posY⟩)
  if !soa.isLeaf[idx]! then
    if let some firstChild := soa.children[idx]![0]? then
      acc := secondWalk spacing direction soa firstChild (yCoor + soa.levelheight[idx]! + spacing)
        (modSum + soa.modifier[idx]!) acc
  if let some rs := soa.rightSibling[idx]! then
    acc := secondWalk spacing direction soa rs yCoor modSum acc
  return acc

/-- `NodePlacer::process`. -/
def process (graph : TGraphId) (monitor : ProgressMonitor) : MrTreeM Unit := do
  discard <| monitor.begin "Processor order nodes" 2.0
  let g ← MrTreeM.getGraph graph
  let spacing := (g.props.get MrTreeOptions.SPACING_NODE_NODE).getD 0.0
  let mut direction := (g.props.get MrTreeOptions.DIRECTION).getD .undefined
  if direction == .undefined then
    direction := .down
    MrTreeM.setGraphProp graph MrTreeOptions.DIRECTION direction
  let a ← get
  let root := g.nodes.find? fun n => (a.node n).internal.root
  if let some root := root then
    let soa := TreeSoA.build a root direction.isVertical
    let soa ← match firstWalk spacing soa 0 with
      | .ok s => pure s
      | .error e => throw (IO.userError e)
    monitor.worked 1.0
    let levelHeight := soa.levelheight[0]!
    let positions := secondWalk spacing direction soa 0 (0.0 - levelHeight / 2.0) 0.0 #[]
    for (idx, pos) in positions do
      MrTreeM.modifyNode soa.nodes[idx]! fun n => { n with position := pos }
    monitor.worked 1.0
  monitor.done

/-- `get_layout_processor_configuration`: `ROOT_PROC` before `P2_NODE_ORDERING`. -/
def configuration : TreeProcessorConfiguration :=
  LayoutProcessorConfiguration.create.addBefore TreeLayoutPhases.p2NodeOrdering
    IntermediateProcessorStrategy.rootProc

/-- The `NodePlacer` phase. -/
def phase : TreePhase :=
  { name := "NodePlacer", process, getLayoutProcessorConfiguration := fun _ => pure (some configuration) }

end NodePlacer

end Elk.Alg.MrTree.P3Place
