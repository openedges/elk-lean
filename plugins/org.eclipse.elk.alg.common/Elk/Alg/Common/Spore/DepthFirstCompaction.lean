import Elk.Alg.Common.Geometry.Tree
import Elk.Alg.Common.Spore.Node
/-!
# `org.eclipse.elk.alg.common.spore.DepthFirstCompaction`

A compaction method that expects a spanning tree of a graph. While traversing
the spanning tree in a depth-first manner the nodes of each subtree are shifted
as one unit towards the parent node of that subtree (elk-rs
`spore/depth_first_compaction.rs`).

## Representation
Rust mutates the tree in place and reads the (partially compacted) whole tree
through a raw root pointer; subtrees are identified by pointer
(`std::ptr::eq`). The Lean port threads the whole tree value through the
traversal and addresses subtrees by paths of child indices (`Tree.getAt?`,
`Tree.modifyAt`); pointer identity becomes path equality. The traversal order
is the Rust one: post-order (all children of a node are compacted first), then
the children of the node are shifted towards it one by one in child order,
each shift seeing the shifts done before. SVG debug output is not ported
(TODO(debug)).
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.Common.Spore

open Elk.Core.Util Elk.Core.Math Elk.Alg.Common

namespace DepthFirstCompaction

/-- Rust `translate_subtree`: translates every node of the subtree by `v`. -/
def translateSubtree (tree : Tree Node) (v : KVector) : Tree Node :=
  { node := tree.node.translate v, children := tree.children.map (translateSubtree · v) }
termination_by tree
decreasing_by exact Tree.sizeOf_lt_of_mem ‹_›

/-- Rust `min_underlap_with_subtree(root, tree, currentMinUnderlap, compactionVector)`:
the minimum distance along the compaction vector between `root` and the descendants of
`tree` (not `tree.node` itself); `0` as soon as a touching descendant blocks the movement. -/
def minUnderlapWithSubtree (root : Node) (tree : Tree Node) (currentMinUnderlap : Float)
    (compactionVector : KVector) : Float := Id.run do
  let f := InternalProperties.FUZZINESS
  let fc := InternalProperties.fuzzyCompare
  let mut minUnderlap := currentMinUnderlap
  for _h : child in tree.children do
    let c := child.node
    if root.touches c then
      if (fc c.rect.x (root.rect.x + root.rect.width) f == 0 && compactionVector.x < fl0p0)
          || (fc (c.rect.x + c.rect.width) root.rect.x f == 0 && compactionVector.x > fl0p0)
          || (fc c.rect.y (root.rect.y + root.rect.height) f == 0 && compactionVector.y < fl0p0)
          || (fc (c.rect.y + c.rect.height) root.rect.y f == 0 && compactionVector.y > fl0p0) then
        minUnderlap := fl0p0
        break
    else
      minUnderlap := fmin minUnderlap (root.distance c compactionVector)
    minUnderlap := fmin minUnderlap
      (minUnderlapWithSubtree root child minUnderlap compactionVector)
  return minUnderlap
termination_by tree
decreasing_by exact Tree.sizeOf_lt_of_mem ‹_›

/-- Rust `get_min_underlap(tree, child, currentMinUnderlap, compactionVector)`: minimum over
every node of `tree` except the subtree at `childPath` (`treePath` is the path of `tree`). -/
def getMinUnderlap (tree : Tree Node) (treePath : List Nat) (child : Tree Node)
    (childPath : List Nat) (currentMinUnderlap : Float) (compactionVector : KVector) :
    Float := Id.run do
  let mut minUnderlap := fmin currentMinUnderlap
    (minUnderlapWithSubtree tree.node child currentMinUnderlap compactionVector)
  let mut i := 0
  for _h : c in tree.children do
    let cPath := treePath ++ [i]
    if cPath != childPath then
      minUnderlap := fmin minUnderlap
        (getMinUnderlap c cPath child childPath minUnderlap compactionVector)
    i := i + 1
  return minUnderlap
termination_by tree
decreasing_by exact Tree.sizeOf_lt_of_mem ‹_›

/-- The Rust compaction vector of `child` towards `parent` (before `get_min_underlap`). -/
def initialCompactionVector (parent child : Node) (orthogonal : Bool) : KVector := Id.run do
  let mut cv := parent.vertex - child.vertex
  if orthogonal then
    let rt := parent.rect
    let rc := child.rect
    if cv.x.abs >= cv.y.abs then
      cv := { cv with y := fl0p0 }
      if rc.y + rc.height > rt.y && rc.y < rt.y + rt.height then
        let dist := fmax (rt.x - (rc.x + rc.width)) (rc.x - (rt.x + rt.width))
        cv := cv.scaleToLength dist
    else
      cv := { cv with x := fl0p0 }
      if rc.x + rc.width > rt.x && rc.x < rt.x + rt.width then
        let dist := fmax (rt.y - (rc.y + rc.height)) (rc.y - (rt.y + rt.height))
        cv := cv.scaleToLength dist
  else
    cv := cv.scaleToLength (parent.underlap child)
  return cv

/-- Rust `compact_tree(tree, root, orthogonal)` for the subtree at `path` of `root`; returns
the updated whole tree. `partial`: the recursion goes through a path lookup in the
updated tree, which is not structural. -/
partial def compactTree (root : Tree Node) (path : List Nat) (orthogonal : Bool) : Tree Node := Id.run do
  let some sub := root.getAt? path | return root
  let n := sub.children.size
  let mut root := root
  for i in [0:n] do
    root := compactTree root (path ++ [i]) orthogonal
  for idx in [0:n] do
    let some tree := root.getAt? path | return root
    let some child := tree.children[idx]? | continue
    let childPath := path ++ [idx]
    let cv := initialCompactionVector tree.node child.node orthogonal
    let minUnderlap := getMinUnderlap root [] child childPath cv.length cv
    let cv := cv.scaleToLength minUnderlap
    root := root.modifyAt childPath (translateSubtree · cv)
  return root

/-- `DepthFirstCompaction.compact(tree, orthogonal, debugOutputFile)`: returns the compacted
tree. The debug output file is ignored (TODO(debug)). -/
def compact (tree : Tree Node) (orthogonal : Bool) (_debugOutputFile : Option String := none) :
    Tree Node :=
  compactTree tree [] orthogonal

/-- `compact(tree, orthogonal)` without debug output. -/
@[inline] def compactWithoutDebug (tree : Tree Node) (orthogonal : Bool) : Tree Node :=
  compact tree orthogonal none

end DepthFirstCompaction

end Elk.Alg.Common.Spore
