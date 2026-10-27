import Tests.Framework
import Elk.Alg.Common.Geometry
import Elk.Alg.Common.Spore
/-! Tests of `org.eclipse.elk.alg.common.spore`: `Node`, `InternalProperties`,
`DepthFirstCompaction` and `ScanlineOverlapCheck` (including the overlap check part of
the elk-rs spore test `scanline_overlap_removal_test`). -/
namespace Tests.AlgCommon.Spore

open Tests Elk Elk.Graph Elk.Core.Util Elk.Core.Math Elk.Alg.Common Elk.Alg.Common.Spore

private def kv (x y : Float) : KVector := ⟨x, y⟩
private def rect (x y w h : Float) : ElkRectangle := ElkRectangle.ofValues x y w h
/-- A node centered in its rectangle (like the spore `ElkGraphImporter`). -/
private def node (x y w h : Float) : Node := Node.new (kv (x + w / 2) (y + h / 2)) (rect x y w h)

def internalProperties : Suite := suite "alg.common.spore.InternalProperties" do
  checkFloat "FUZZINESS" InternalProperties.FUZZINESS 0.0001
  checkEq "DEBUG_SVG id" InternalProperties.DEBUG_SVG.id "debugSVG"
  checkEq "DEBUG_SVG default" InternalProperties.DEBUG_SVG.default (some false)
  checkEq "OVERLAPS_EXISTED id" InternalProperties.OVERLAPS_EXISTED.id "overlapsExisted"
  checkEq "OVERLAPS_EXISTED default" InternalProperties.OVERLAPS_EXISTED.default (some true)

def nodeSuite : Suite := suite "alg.common.spore.Node" do
  let n := node 0 0 10 10
  check "new keeps original vertex" (n.originalVertex == kv 5 5 && n.vertex == kv 5 5)
  let t := n.translate (kv 3 (-2))
  check "translate" (t.vertex == kv 8 3 && t.rect == rect 3 (-2) 10 10 && t.originalVertex == kv 5 5)
  let c := n.setCenterPosition (kv 20 30)
  check "setCenterPosition" (c.vertex == kv 20 30 && c.rect == rect 15 25 10 10)
  -- horizontal gap of 10 between centers 20 apart: h_scale = 0.5
  checkFloat "underlap horizontal" (n.underlap (node 20 0 10 10)) 10
  checkFloat "underlap overlapping" (n.underlap (node 5 5 10 10)) 0
  -- diagonal: centers (5,5)/(25,25), h and v underlap 10 → scale 0.5 of the center distance
  checkFloat "underlap diagonal" (n.underlap (node 20 20 10 10)) (0.5 * Float.sqrt 800) 1e-9
  -- the rays are limited to the length of `v` (`ElkMath.intersects2`): values match elk-rs
  checkFloat "distance along +x" ((node 20 0 10 10).distance n (kv 100 0)) 10
  checkFloat "distance along -x" (n.distance (node 20 0 10 10) (kv (-100) 0)) 10
  check "distance with too short v" (((node 20 0 10 10).distance n (kv 1 0)).isInf)
  check "distance without hit" ((n.distance (node 20 0 10 10) (kv 0 100)).isInf)
  check "touches adjacent" (n.touches (node 10 0 10 10))
  check "touches within fuzziness" (n.touches (node 10.00005 0 10 10))
  check "does not touch" (!n.touches (node 10.1 0 10 10))
  check "touches corner" (n.touches (node 10 10 5 5))

private def rectXs (t : Tree Node) : Array Float := t.preorder.map (·.rect.x)

private def approxEq (a b : Array Float) : Bool :=
  a.size == b.size && (a.zip b).all fun (x, y) => (x - y).abs < 1e-9

def depthFirstCompaction : Suite := suite "alg.common.spore.DepthFirstCompaction" do
  -- chain root - child - grandchild along x, 20 apart each
  let gc := Tree.new (node 60 0 10 10)
  let child : Tree Node := { node := node 30 0 10 10, children := #[gc] }
  let root : Tree Node := { node := node 0 0 10 10, children := #[child] }
  let out := DepthFirstCompaction.compactWithoutDebug root false
  checkEq "chain compacted" (rectXs out) #[0, 10, 20]
  checkEq "chain vertices" (out.preorder.map (·.vertex.x)) #[5, 15, 25]
  checkEq "chain original vertices kept" (out.preorder.map (·.originalVertex.x)) #[5, 35, 65]
  checkEq "chain structure kept" out.size 3
  -- orthogonal: diagonal offset, only the x component is compacted
  let root2 : Tree Node := { node := node 0 0 10 10, children := #[Tree.new (node 30 3 10 10)] }
  let out2 := DepthFirstCompaction.compact root2 true
  check "orthogonal x compaction" (match out2.getAt? [0] with
    | some t => t.node.rect == rect 10 3 10 10
    | none => false)
  -- non-orthogonal diagonal: moved along the center line until the rectangles touch
  let root3 : Tree Node := { node := node 0 0 10 10, children := #[Tree.new (node 20 20 10 10)] }
  let out3 := DepthFirstCompaction.compact root3 false
  check "diagonal compaction" (match out3.getAt? [0] with
    | some t => (t.node.rect.x - 10).abs < 1e-9 && (t.node.rect.y - 10).abs < 1e-9
    | none => false)
  -- two leaf children: `min_underlap_with_subtree` only looks at the *descendants* of the
  -- moved subtree, so a leaf sibling does not block (Java/Rust quirk, kept): both end at 10
  let blockA := Tree.new (node 30 0 10 10)
  let blockB := Tree.new (node 60 0 10 10)
  let root4 : Tree Node := { node := node 0 0 10 10, children := #[blockA, blockB] }
  let out4 := DepthFirstCompaction.compact root4 false
  checkEq "leaf siblings are not obstacles" (rectXs out4) #[0, 10, 10]
  -- a descendant of the moved subtree is an obstacle: `mover` alone could move 30 to the
  -- left, but its child `moverChild` hits the (compacted) `blocker` after 20
  let blocker := Tree.new (node 15 12 10 10)
  let mover : Tree Node := { node := node 40 0 10 10, children := #[Tree.new (node 40 8 10 10)] }
  let root5 : Tree Node := { node := node 0 0 10 10, children := #[blocker, mover] }
  let out5 := DepthFirstCompaction.compact root5 false
  check "descendant obstacle" (approxEq (rectXs out5) #[0, 10, 20, 20])
  check "blocker moved diagonally" (approxEq (out5.preorder.map (·.rect.y)) #[0, 8, 0, 8])
  -- a leaf stays unchanged
  checkEq "single node" (rectXs (DepthFirstCompaction.compact (Tree.new (node 3 4 5 6)) false)) #[3]

private def collect : IOverlapHandler (Array TEdge) :=
  ⟨fun n1 n2 acc => TEdge.insertUnique acc (TEdge.new n1.originalVertex n2.originalVertex)⟩

private def pairs : IOverlapHandler (Array (Float × Float)) :=
  ⟨fun n1 n2 acc => acc.push (n1.rect.x, n2.rect.x)⟩

def scanlineOverlapCheck : Suite := suite "alg.common.spore.ScanlineOverlapCheck" do
  let nodes := #[node 0 0 10 10, node 5 5 10 10, node 100 0 10 10, node 8 30 10 10]
  let found := (ScanlineOverlapCheck.new pairs).sweep nodes #[]
  checkEq "overlapping pair (inserted, active)" found #[(5.0, 0.0)]
  -- touching rectangles do not overlap (strict fuzzy comparison)
  let touching := (ScanlineOverlapCheck.new pairs).sweep #[node 0 0 10 10, node 10 0 10 10] #[]
  checkEq "touching not reported" touching.size 0
  -- three mutually overlapping nodes
  let three := (ScanlineOverlapCheck.new pairs).sweep
    #[node 0 0 10 10, node 2 2 10 10, node 4 4 10 10] #[]
  checkEq "three overlapping" three #[(2.0, 0.0), (4.0, 0.0), (4.0, 2.0)]
  -- scanline_overlap_removal_test: graph of build_graph(true), overlap check part
  let graph := #[node 0 30 160 20, node 150 40 160 20, node 150 0 20 20, node 150 70 20 20]
  let edges := (ScanlineOverlapCheck.new collect).sweep graph #[]
  check "scanline_overlap_removal_test overlaps found" (!edges.isEmpty)
  checkEq "scanline_overlap_removal_test overlap count" edges.size 1
  check "scanline_overlap_removal_test pair"
    (edges.all (· == TEdge.new (kv 80 40) (kv 230 50)))
  checkEq "timestamp order: upper end before lower end at equal y"
    (ScanlineOverlapCheck.timestampCmp #[node 0 0 10 10, node 0 10 10 10] ⟨0, false⟩ ⟨1, true⟩ == .lt)
    true

def suites : Array Tests.Suite :=
  #[internalProperties, nodeSuite, depthFirstCompaction, scanlineOverlapCheck]

end Tests.AlgCommon.Spore
