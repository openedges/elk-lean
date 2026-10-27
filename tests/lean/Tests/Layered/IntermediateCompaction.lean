import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Intermediate.CompactionProcessors
/-!
Tests of `HorizontalGraphCompactor` and its `intermediate.compaction` companions on hand-built,
already routed graphs. Expected values are derived by hand (comments "hand: …"). elk-rs has only
pipeline-driven tests (`tests/compaction/compaction_test.rs`, assertions: finite positions and
positive sizes per strategy); their assertions are applied to the hand-built graphs under the
Rust test names.

Spacings of all graphs: node-node 20, edge-edge 10, edge-node 10, node-node between layers 20,
edge-node between layers 10. The edge-aware scanline enlarges segments by `10/2 - 0.5 = 4.5`
(+ `0.01`), nodes by `4.5` (edge-edge) and, in the final round, by the minimum half spacing.
-/
namespace Tests.Layered.IntermediateCompaction

open Tests Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Alg.Common.Compaction.OneD
open Elk.Alg.Layered Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate
open Elk.Alg.Layered.Intermediate.Compaction LayeredM

/-- Graph properties of the tests. -/
def graphProps (strategy : GraphCompactionStrategy) (routing : EdgeRouting := .orthogonal)
    (constraints : ConstraintCalculationStrategy := .scanline) : PropertyMap :=
  ({} : PropertyMap)
    |>.set LayeredOptions.COMPACTION_POST_COMPACTION_STRATEGY strategy
    |>.set LayeredOptions.COMPACTION_POST_COMPACTION_CONSTRAINTS constraints
    |>.set LayeredOptions.EDGE_ROUTING routing
    |>.set LayeredOptions.SPACING_NODE_NODE 20.0
    |>.set LayeredOptions.SPACING_EDGE_EDGE 10.0
    |>.set LayeredOptions.SPACING_EDGE_NODE 10.0
    |>.set LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS 20.0
    |>.set LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS 10.0

/-- A graph with the test properties and its `Spacings`. -/
def mkGraph (props : PropertyMap) : LayeredM LGraphId :=
  createGraph { props, internal := { spacings := some (Spacings.new props) } }

/-- A node with position and size. -/
def box (x y w h : Float) : LNode := { position := ⟨x, y⟩, size := ⟨w, h⟩ }

/-- Appends a layer with the given nodes. -/
def addLayer (g : LGraphId) (nodes : Array LNode) : LayeredM (Array LNodeId) := do
  let l ← createLayer g
  modifyGraph g fun x => { x with layers := x.layers.push l }
  let mut ids : Array LNodeId := #[]
  for n in nodes do
    let id ← createNode g n
    setNodeLayer id (some l)
    ids := ids.push id
  return ids

/-- Adds a port to a node. -/
def addPort (n : LNodeId) (side : PortSide) (pos : KVector := {}) : LayeredM LPortId := do
  let p ← createPort { side, position := pos }
  setPortNode p (some n)
  return p

/-- Adds an edge with bend points. -/
def addEdge (source target : LPortId) (bends : Array KVector := #[]) : LayeredM LEdgeId := do
  let e ← createEdge { bendPoints := bends }
  setEdgeSource e (some source)
  setEdgeTarget e (some target)
  return e

/-- Runs the registered-style processor on the graph. -/
def runProcessor (g : LGraphId) (p : LayeredProcessor := HorizontalGraphCompactor.processor) : LayeredM Unit := do
  p.process g (← ProgressMonitor.basic)

/-- Rust `compaction_test.rs` assertions: finite positions, positive sizes. -/
def checkFiniteLayout (name : String) (a : LGraphArena) (nodes : Array LNodeId) : TestM Unit := do
  check s!"{name}: finite positions" (nodes.all fun n => (a.node n).position.x.isFinite && (a.node n).position.y.isFinite)
  check s!"{name}: positive sizes" (nodes.all fun n => (a.node n).size.x > 0.0 && (a.node n).size.y > 0.0)

/-! ### Graphs -/

/-- G1: two nodes without edges, `n0 (0,0)` and `n1 (100,0)`, 20×20. -/
def buildG1 (props : PropertyMap) : LayeredM (LGraphId × Array LNodeId) := do
  let g ← mkGraph props
  let l0 ← addLayer g #[box 0 0 20 20]
  let l1 ← addLayer g #[box 100 0 20 20]
  return (g, l0 ++ l1)

/-- G2: `n0 (0,0)` → `n1 (200,50)` with the vertical segment `(100,10)-(100,60)`. -/
def buildG2 (props : PropertyMap) : LayeredM (LGraphId × Array LNodeId × LEdgeId) := do
  let g ← mkGraph props
  let l0 ← addLayer g #[box 0 0 20 20]
  let l1 ← addLayer g #[box 200 50 20 20]
  let p0 ← addPort l0[0]! .east ⟨20, 10⟩
  let p1 ← addPort l1[0]! .west ⟨0, 10⟩
  let e ← addEdge p0 p1 #[⟨100, 10⟩, ⟨100, 60⟩]
  return (g, l0 ++ l1, e)

/-- G3: `n0 (0,0)` leaves through a south port, bend `(10,60)`, into the west port of `n1 (100,50)`. -/
def buildG3 (props : PropertyMap) : LayeredM (LGraphId × Array LNodeId × LEdgeId × LPortId) := do
  let g ← mkGraph props
  let l0 ← addLayer g #[box 0 0 20 20]
  let l1 ← addLayer g #[box 100 50 20 20]
  let p0 ← addPort l0[0]! .south ⟨10, 20⟩
  let p1 ← addPort l1[0]! .west ⟨0, 10⟩
  let e ← addEdge p0 p1 #[⟨10, 60⟩]
  return (g, l0 ++ l1, e, p0)

/-- G4: `n0 (0,0)` → `n1 (100,0)` (straight edge) and the unconnected `n2 (100,100)`. -/
def buildG4 (props : PropertyMap) : LayeredM (LGraphId × Array LNodeId) := do
  let g ← mkGraph props
  let l0 ← addLayer g #[box 0 0 20 20]
  let l1 ← addLayer g #[box 100 0 20 20, box 100 100 20 20]
  let p0 ← addPort l0[0]! .east ⟨20, 10⟩
  let p1 ← addPort l1[0]! .west ⟨0, 10⟩
  let _ ← addEdge p0 p1
  return (g, l0 ++ l1)

/-! ### Unit tests of the companions -/

def segmentTests : Suite := suite "layered.intermediate.compaction.VerticalSegment" do
  let e : LEdgeId := ⟨3⟩
  let s := VerticalSegment.new 7 ⟨100, 60⟩ ⟨100, 10⟩ e #[0, 1] none
  checkEqR "hitbox spans both bends (hand: min x/y, abs extents)" s.hitbox ⟨100, 10, 0, 50⟩
  checkEqR "joined ids = own id" s.joinedSegmentIds #[7]
  checkEqR "affected bends" s.affectedBends #[(e, 0), (e, 1)]
  let t := VerticalSegment.new 8 ⟨100.00005, 55⟩ ⟨100.00005, 80⟩ ⟨4⟩ #[2] (some ⟨1⟩)
  check "intersects: same fuzzy x, overlapping y" (s.intersects t)
  let u := VerticalSegment.new 9 ⟨100, 70⟩ ⟨100, 90⟩ ⟨5⟩ #[0] none
  check "no intersection: y gap 60..70" (!s.intersects u)
  let j := s.joinWith t
  checkEqR "join: union hitbox origin (hand: min x 100, min y 10)" (j.hitbox.x, j.hitbox.y) (100.0, 10.0)
  checkFloat "join: union hitbox height (hand: 80 - 10)" j.hitbox.height 70.0
  checkFloat "join: union hitbox width (hand: 100.00005 - 100)" j.hitbox.width 0.00005
  checkEqR "join: represented edges appended" j.representedEdges #[e, ⟨4⟩]
  checkEqR "join: joined ids" j.joinedSegmentIds #[7, 8]
  checkEqR "join: group parents of the right segment" j.potentialGroupParents #[⟨1⟩]
  checkEqR "compareTo: fuzzy equal x, then y" (VerticalSegment.compareTo t s) Ordering.gt
  checkEqR "compareTo: smaller x first" (VerticalSegment.compareTo s { u with hitbox := { u.hitbox with x := 120 } }) Ordering.lt

def spacingsTests : Suite := suite "layered.intermediate.compaction.SpecialSpacingsHandler" do
  let props := graphProps .left
  let h : SpecialSpacingsHandler :=
    { nodeTypes := #[some .normal, some .normal, some .externalPort, none, none]
      segmentEdgeKeys := #[none, none, none, some #[⟨1⟩, ⟨2⟩], some #[⟨2⟩]]
      spacings := some (Spacings.new props) }
  checkFloat "horizontal normal-normal = node-node between layers" (h.horizontalSpacing ⟨0⟩ ⟨1⟩) 20.0
  checkFloat "horizontal normal-segment = edge-node between layers" (h.horizontalSpacing ⟨0⟩ ⟨3⟩) 10.0
  checkFloat "horizontal external port = 0" (h.horizontalSpacing ⟨0⟩ ⟨2⟩) 0.0
  checkFloat "horizontal segments of the same edge = 0" (h.horizontalSpacing ⟨3⟩ ⟨4⟩) 0.0
  checkFloat "vertical segments of the same edge = 1" (h.verticalSpacing ⟨3⟩ ⟨4⟩) 1.0
  checkFloat "vertical normal-normal = node-node" (h.verticalSpacing ⟨0⟩ ⟨1⟩) 20.0
  checkFloat "vertical external port = 0 (Rust)" (h.verticalSpacing ⟨2⟩ ⟨1⟩) 0.0
  checkFloat "no Spacings → 0" ({ h with spacings := none }.horizontalSpacing ⟨0⟩ ⟨1⟩) 0.0

/-! ### LGraphToCGraphTransformer -/

def transformerTests : Suite := suite "layered.intermediate.compaction.LGraphToCGraphTransformer" do
  -- G2: one regular segment
  let ((ctx, nodes, e), _) ← LayeredM.run (do
      let (g, nodes, e) ← buildG2 (graphProps .left)
      let ctx ← CompactionContext.transform g .orthogonal
      return (ctx, nodes, e))
  let cg := ctx.cGraph
  checkEq "G2: 3 CNodes (2 nodes + 1 segment)" cg.cNodes.size 3
  checkEqR "G2: node hitbox" (cg.cNode ⟨0⟩).hitbox ⟨0, 0, 20, 20⟩
  checkEqR "G2: node hitbox n1" (cg.cNode ⟨1⟩).hitbox ⟨200, 50, 20, 20⟩
  checkEqR "G2: segment hitbox (hand: x 100, y 10..60)" (cg.cNode ⟨2⟩).hitbox ⟨100, 10, 0, 50⟩
  checkEqR "G2: origins" ctx.cnodeOrigin #[.node nodes[0]!, .node nodes[1]!, .segment 0]
  checkEq "G2: only node groups (segment has no parent)" cg.cGroups.size 2
  check "G2: segment not grouped yet" (cg.cNode ⟨2⟩).cGroup.isNone
  let seg := ctx.segments[0]!
  check "G2: first regular segment below the source: ignore up (hand: 60 > 20)" seg.ignoreSpacingUp
  check "G2: last segment ends inside the target: ignore both (hand: 60 in 50..70)" seg.ignoreSpacingDown
  checkEqR "G2: affected bends" seg.affectedBends #[(e, 0), (e, 1)]
  checkEqR "G2: connection locks (hand: n0 out>in → left, n1 in>out → right)" ctx.connectionLocks
    #[{ left := true }, { right := true }, {}]
  checkEqR "G2: graph with edges supports LEFT/RIGHT only" cg.supportedDirections #[.left, .right]
  -- G1: no edges → all directions
  let ((ctx1, _), _) ← LayeredM.run (do
      let (g, nodes) ← buildG1 (graphProps .left)
      let ctx ← CompactionContext.transform g .orthogonal
      return (ctx, nodes))
  checkEqR "G1: no edges → LEFT, RIGHT, UP, DOWN" ctx1.cGraph.supportedDirections #[.left, .right, .up, .down]
  checkEq "G1: no segments" ctx1.segments.size 0
  -- G3: north/south segment grouped with its node
  let ((ctx3, p0), _) ← LayeredM.run (do
      let (g, _, _, p0) ← buildG3 (graphProps .left)
      let ctx ← CompactionContext.transform g .orthogonal
      return (ctx, p0))
  checkEqR "G3: south segment hitbox (hand: bend (10,60) to node bottom 20)" (ctx3.cGraph.cNode ⟨2⟩).hitbox ⟨10, 20, 0, 40⟩
  checkEqR "G3: segment joins the node's group" (ctx3.cGraph.cGroup ⟨0⟩).cNodes #[⟨0⟩, ⟨2⟩]
  checkEq "G3: still two groups" ctx3.cGraph.cGroups.size 2
  check "G3: south segment ignores spacing up" (ctx3.segments[0]!.ignoreSpacingUp && !ctx3.segments[0]!.ignoreSpacingDown)
  checkEqR "G3: segment port" ctx3.segments[0]!.port (some p0)
  -- merging: two overlapping segments at x = 100 of two edges from the same port
  let ((ctxM, eM), _) ← LayeredM.run (do
      let g ← mkGraph (graphProps .left)
      let l0 ← addLayer g #[box 0 0 20 20]
      let l1 ← addLayer g #[box 200 0 20 60]
      let p0 ← addPort l0[0]! .east
      let p1 ← addPort l1[0]! .west
      let p2 ← addPort l1[0]! .west
      let e0 ← addEdge p0 p1 #[⟨100, 10⟩, ⟨100, 30⟩]
      let e1 ← addEdge p0 p2 #[⟨100, 20⟩, ⟨100, 50⟩]
      let ctx ← CompactionContext.transform g .orthogonal
      return (ctx, #[e0, e1]))
  checkEq "merge: one merged segment" ctxM.segments.size 1
  checkEqR "merge: union hitbox (hand: y 10..50)" ctxM.segments[0]!.hitbox ⟨100, 10, 0, 40⟩
  checkEqR "merge: represented edges" ctxM.segments[0]!.representedEdges eM
  checkEqR "merge: joined segment ids" ctxM.segments[0]!.joinedSegmentIds #[0, 1]
  checkEqR "merge: affected bends of both edges" ctxM.segments[0]!.affectedBends
    #[(eM[0]!, 0), (eM[0]!, 1), (eM[1]!, 0), (eM[1]!, 1)]
  checkEqR "merge: segment lock (hand: 1 source port < 2 target ports → left)" ctxM.connectionLocks[2]! { left := true }
  -- comment boxes are no CNodes
  let ((ctxC, cm, n0), _) ← LayeredM.run (do
      let g ← mkGraph (graphProps .left)
      let l0 ← addLayer g #[box 0 0 20 20, { box 5 (-30) 10 10 with props := ({} : PropertyMap).set LayeredOptions.COMMENT_BOX true }]
      let pc ← addPort l0[1]! .south
      let pn ← addPort l0[0]! .north
      let _ ← addEdge pc pn
      let ctx ← CompactionContext.transform g .orthogonal
      return (ctx, l0[1]!, l0[0]!))
  checkEq "comment: only the node is a CNode" ctxC.cGraph.cNodes.size 1
  checkEq "comment: one comment offset" ctxC.commentOffsets.size 1
  check "comment: anchored at the connected node" (ctxC.commentOffsets[0]!.comment == cm && ctxC.commentOffsets[0]!.anchor == n0)
  checkFloat "comment: offset x (hand: 5 - 0)" ctxC.commentOffsets[0]!.offset.x 5.0
  checkFloat "comment: offset y (hand: -30 - 0)" ctxC.commentOffsets[0]!.offset.y (-30.0)

/-! ### Compaction strategies (orthogonal routing) -/

def strategyTests : Suite := suite "layered.intermediate.compaction.HorizontalGraphCompactor" do
  -- G1 LEFT: hand: n1 = 0 + 20 + 20 (node-node between layers)
  let ((g, nodes), a) ← LayeredM.run (do
      let (g, nodes) ← buildG1 (graphProps .left)
      runProcessor g
      return (g, nodes))
  checkFloat "G1 LEFT: n0 stays at 0" (a.node nodes[0]!).position.x 0.0
  checkFloat "G1 LEFT: n1 at 40 (hand: 0 + 20 + 20)" (a.node nodes[1]!).position.x 40.0
  checkFloat "G1 LEFT: graph width 60" (a.graph g).size.x 60.0
  checkFloat "G1 LEFT: graph height 20" (a.graph g).size.y 20.0
  checkFloat "G1 LEFT: offset 0" (a.graph g).offset.x 0.0
  -- G1 RIGHT: hand: mirrored -120 / -20 → n0 at -(-80) - 20 = 60
  let ((g, nodes), a) ← LayeredM.run (do
      let (g, nodes) ← buildG1 (graphProps .right)
      runProcessor g
      return (g, nodes))
  checkFloat "G1 RIGHT: n0 moves to 60" (a.node nodes[0]!).position.x 60.0
  checkFloat "G1 RIGHT: n1 stays at 100" (a.node nodes[1]!).position.x 100.0
  checkFloat "G1 RIGHT: offset -60 (hand: -top left x)" (a.graph g).offset.x (-60.0)
  checkFloat "G1 RIGHT: graph width 60" (a.graph g).size.x 60.0
  -- G2 LEFT: hand: segment at 0 + 20 + 10 = 30, n1 at 30 + 0 + 10 = 40
  let ((g, nodes, e), a) ← LayeredM.run (do
      let (g, nodes, e) ← buildG2 (graphProps .left)
      runProcessor g
      return (g, nodes, e))
  checkFloat "G2 LEFT: n1 at 40" (a.node nodes[1]!).position.x 40.0
  checkFloat "G2 LEFT: bend 0 moved with the segment (hand: 30)" (a.edge e).bendPoints[0]!.x 30.0
  checkFloat "G2 LEFT: bend 1 moved with the segment" (a.edge e).bendPoints[1]!.x 30.0
  checkFloat "G2 LEFT: bend y unchanged" (a.edge e).bendPoints[1]!.y 60.0
  checkFloat "G2 LEFT: graph width (hand: 60)" (a.graph g).size.x 60.0
  checkFloat "G2 LEFT: graph height (hand: 70)" (a.graph g).size.y 70.0
  checkFiniteLayout "compaction_left_orthogonal_scanline" a nodes
  -- G2 RIGHT: hand: mirrored n1 -220, segment -190, n0 -180 → n0 160, segment 190
  let ((g, nodes, e), a) ← LayeredM.run (do
      let (g, nodes, e) ← buildG2 (graphProps .right)
      runProcessor g
      return (g, nodes, e))
  checkFloat "G2 RIGHT: n0 at 160" (a.node nodes[0]!).position.x 160.0
  checkFloat "G2 RIGHT: n1 stays at 200" (a.node nodes[1]!).position.x 200.0
  checkFloat "G2 RIGHT: bends at 190 (hand: delta +90)" (a.edge e).bendPoints[0]!.x 190.0
  checkFloat "G2 RIGHT: offset -160" (a.graph g).offset.x (-160.0)
  checkFiniteLayout "compaction_right_orthogonal_scanline" a nodes
  -- G3 LEFT: the south segment is grouped with n0; hand: n1 = 10 (segment offset) + 0 + 10 = 20
  let ((g, nodes, e, _), a) ← LayeredM.run (do
      let r ← buildG3 (graphProps .left)
      runProcessor r.1
      return r)
  checkFloat "G3 LEFT: n1 at 20 (constraint from the grouped segment)" (a.node nodes[1]!).position.x 20.0
  checkFloat "G3 LEFT: bend unchanged (segment did not move)" (a.edge e).bendPoints[0]!.x 10.0
  checkFloat "G3 LEFT: graph width (hand: 40)" (a.graph g).size.x 40.0
  checkFloat "G3 LEFT: graph height (hand: 70)" (a.graph g).size.y 70.0
  -- G4: locking variants (hand: LEFT pass puts the unconnected n2 at 0)
  let ((g, nodes), a) ← LayeredM.run (do
      let (g, nodes) ← buildG4 (graphProps .leftRightConstraintLocking (constraints := .quadratic))
      runProcessor g
      return (g, nodes))
  checkFloat "G4 constraint locking: n0 at 0" (a.node nodes[0]!).position.x 0.0
  checkFloat "G4 constraint locking: n1 at 40" (a.node nodes[1]!).position.x 40.0
  checkFloat "G4 constraint locking: unconstrained n2 is locked at 0" (a.node nodes[2]!).position.x 0.0
  checkFloat "G4 constraint locking: graph height (hand: 120)" (a.graph g).size.y 120.0
  checkFiniteLayout "compaction_left_right_constraint_locking_orthogonal_quadratic" a nodes
  let ((_, nodes), a) ← LayeredM.run (do
      let (g, nodes) ← buildG4 (graphProps .leftRightConstraintLocking)
      runProcessor g
      return (g, nodes))
  checkFloat "G4 constraint locking (scanline): n2 at 0" (a.node nodes[2]!).position.x 0.0
  let ((g, nodes), a) ← LayeredM.run (do
      let (g, nodes) ← buildG4 (graphProps .leftRightConnectionLocking)
      runProcessor g
      return (g, nodes))
  checkFloat "G4 connection locking: n0 at 0" (a.node nodes[0]!).position.x 0.0
  checkFloat "G4 connection locking: n1 locked right at 40" (a.node nodes[1]!).position.x 40.0
  checkFloat "G4 connection locking: n2 (no lock) moves right to 40 (hand: -(-60) - 20)" (a.node nodes[2]!).position.x 40.0
  checkFloat "G4 connection locking: graph width 60" (a.graph g).size.x 60.0
  checkFiniteLayout "compaction_left_right_connection_locking_orthogonal_scanline" a nodes
  -- quadratic vs. scanline: n2 (100,39.5) below n1; hand: quadratic overlap test 39.5 < 0 + 20 + 20,
  -- edge-aware final round 39.5 - 9.5 = 30 > 20 + 9.5
  let ((_, nodes), a) ← LayeredM.run (do
      let g ← mkGraph (graphProps .left)
      let l0 ← addLayer g #[box 0 0 20 20]
      let l1 ← addLayer g #[box 100 0 20 20, box 100 39.5 20 20]
      runProcessor g
      return (g, l0 ++ l1))
  checkFloat "scanline LEFT: n2 unconstrained, at 0" (a.node nodes[2]!).position.x 0.0
  let ((_, nodes), a) ← LayeredM.run (do
      let g ← mkGraph (graphProps .left (constraints := .quadratic))
      let l0 ← addLayer g #[box 0 0 20 20]
      let l1 ← addLayer g #[box 100 0 20 20, box 100 39.5 20 20]
      runProcessor g
      return (g, l0 ++ l1))
  checkFloat "quadratic LEFT: n2 constrained by n0, at 40" (a.node nodes[2]!).position.x 40.0
  checkFloat "quadratic LEFT: n1 at 40" (a.node nodes[1]!).position.x 40.0
  -- NONE and POLYLINE leave the graph unchanged
  let ((_, nodes), a) ← LayeredM.run (do
      let (g, nodes) ← buildG1 (graphProps .none)
      runProcessor g
      return (g, nodes))
  checkFloat "compaction_none_orthogonal_scanline: n1 unchanged" (a.node nodes[1]!).position.x 100.0
  checkFiniteLayout "compaction_none_orthogonal_scanline" a nodes
  let ((g, nodes), a) ← LayeredM.run (do
      let (g, nodes) ← buildG1 (graphProps .left (routing := .polyline))
      runProcessor g
      return (g, nodes))
  checkFloat "compaction_polyline_left_does_not_fail: n1 unchanged" (a.node nodes[1]!).position.x 100.0
  checkFloat "compaction_polyline_left_does_not_fail: graph size untouched" (a.graph g).size.x 0.0
  -- comment box and self loop label follow the moved node (RIGHT)
  let ((cm, n0, lb), a) ← LayeredM.run (do
      let g ← mkGraph (graphProps .right)
      let l0 ← addLayer g #[box 0 0 20 20, { box 5 (-30) 10 10 with props := ({} : PropertyMap).set LayeredOptions.COMMENT_BOX true }]
      let _ ← addLayer g #[box 100 0 20 20]
      let pc ← addPort l0[1]! .south
      let pn ← addPort l0[0]! .north
      let _ ← addEdge pc pn
      let ps ← addPort l0[0]! .east
      let pt ← addPort l0[0]! .east
      let sl ← addEdge ps pt
      let lb ← createLabel "loop" { position := ⟨30, 2⟩ }
      modifyEdge sl fun ed => { ed with labels := #[lb] }
      runProcessor g
      return (l0[1]!, l0[0]!, lb))
  checkFloat "RIGHT: n0 moves to 60" (a.node n0).position.x 60.0
  checkFloat "comment follows its anchor (hand: 60 + 5)" (a.node cm).position.x 65.0
  checkFloat "comment y = anchor y + offset" (a.node cm).position.y (-30.0)
  checkFloat "self loop label moved by the node delta (hand: 30 + 60)" (a.label lb).position.x 90.0
  -- external port dummy (WEST) is put back to the left border
  let ((g, nodes), a) ← LayeredM.run (do
      let g ← mkGraph (graphProps .left)
      let l0 ← addLayer g #[box 0 0 20 20]
      let l1 ← addLayer g #[box 100 0 20 20]
      let l2 ← addLayer g #[{ box 150 8 4 4 with type := .externalPort, internal := { extPortSide := .west } }]
      runProcessor g
      return (g, l0 ++ l1 ++ l2))
  checkFloat "external port: n1 at 40" (a.node nodes[1]!).position.x 40.0
  checkFloat "external port WEST: x = top left x (hand: 0)" (a.node nodes[2]!).position.x 0.0
  checkFloat "external port: graph width includes the compacted dummy (hand: 60 + 4)" (a.graph g).size.x 64.0

/-! ### EDGE_LENGTH (network simplex compaction) -/

def networkSimplexTests : Suite := suite "layered.intermediate.compaction.NetworkSimplexCompaction" do
  -- G2: hand: layers n0 0, segment 30, n1 40 (all tight)
  let ((_, nodes, e), a) ← LayeredM.run (do
      let (g, nodes, e) ← buildG2 (graphProps .edgeLength)
      runProcessor g
      return (g, nodes, e))
  checkFloat "G2 EDGE_LENGTH: n0 at 0" (a.node nodes[0]!).position.x 0.0
  checkFloat "G2 EDGE_LENGTH: n1 at 40" (a.node nodes[1]!).position.x 40.0
  checkFloat "G2 EDGE_LENGTH: bends at 30" (a.edge e).bendPoints[0]!.x 30.0
  checkFiniteLayout "compaction_edge_length_orthogonal_scanline" a nodes
  -- two components: the artificial source (delta 1) shifts both by one
  let (nodes, a) ← LayeredM.run (do
      let g ← mkGraph (graphProps .edgeLength)
      let l0 ← addLayer g #[box 0 0 20 20, box 0 100 20 20]
      let l1 ← addLayer g #[box 100 0 20 20, box 100 100 20 20]
      let p0 ← addPort l0[0]! .east
      let p1 ← addPort l1[0]! .west
      let p2 ← addPort l0[1]! .east
      let p3 ← addPort l1[1]! .west
      let _ ← addEdge p0 p1
      let _ ← addEdge p2 p3
      runProcessor g
      return l0 ++ l1)
  checkFloat "two components: n0 at layer 1 (hand: artificial source at 0)" (a.node nodes[0]!).position.x 1.0
  checkFloat "two components: n2 at layer 1" (a.node nodes[1]!).position.x 1.0
  checkFloat "two components: n1 at 41 (hand: 1 + 20 + 20)" (a.node nodes[2]!).position.x 41.0
  checkFloat "two components: n3 at 41" (a.node nodes[3]!).position.x 41.0
  -- south-south edge: both north/south segments represent the same edge (helper nodes), the
  -- fractional target offset 10.5 rounds to 1 and moves the source port by 0.5
  let ((g, nodes, e, p0), a) ← LayeredM.run (do
      let g ← mkGraph (graphProps .edgeLength)
      let l0 ← addLayer g #[box 0 0 20 20]
      let l1 ← addLayer g #[box 100 0 20 20]
      let p0 ← addPort l0[0]! .south ⟨10, 20⟩
      let p1 ← addPort l1[0]! .south ⟨10.5, 20⟩
      let e ← addEdge p0 p1 #[⟨10, 40⟩, ⟨110.5, 40⟩]
      runProcessor g
      return (g, l0 ++ l1, e, p0))
  checkFloat "south-south: n0 at layer 2 (hand: source 0, helpers 1)" (a.node nodes[0]!).position.x 2.0
  checkFloat "south-south: n1 at 42 (hand: 2 + 40)" (a.node nodes[1]!).position.x 42.0
  checkFloat "south-south: source segment bend (hand: 2 + 9.5)" (a.edge e).bendPoints[0]!.x 11.5
  checkFloat "south-south: target segment bend (hand: 42 + 10.5)" (a.edge e).bendPoints[1]!.x 52.5
  checkFloat "south-south: source port moved by the rounding (hand: 10 - 0.5)" (a.port p0).position.x 9.5
  checkFloat "south-south: graph width (hand: 62 - 2)" (a.graph g).size.x 60.0
  checkFloat "south-south: graph height includes the 0.02 epsilon drift (hand: 20.02 + 20)" (a.graph g).size.y 40.02

/-! ### Spline routes (through a fake `SplineRouteAccess`) -/

/-- A fake spline segment store. -/
def fakeSplines (store : IO.Ref (Array SplineSegmentView)) (routes : Array (LEdgeId × Array Nat)) : SplineRouteAccess :=
  { routeStart := fun e => return (routes.find? (·.1 == e)).map (·.2)
    segment := fun s => return ((← store.get)[s]?).getD {}
    modifyBoundingBox := fun s f => store.modify fun arr =>
      arr.modify s fun v => { v with boundingBox := f v.boundingBox } }

def splineTests : Suite := suite "layered.intermediate.compaction.splines" do
  -- chain: straight initial s0, curved s1, straight s2, curved s3, straight last s4
  let store ← IO.mkRef (#[] : Array SplineSegmentView)
  let (ctx, _) ← LayeredM.run (do
      let g ← mkGraph (graphProps .left (routing := .splines))
      let l0 ← addLayer g #[box 0 0 20 20]
      let l1 ← addLayer g #[box 300 0 20 20]
      let p0 ← addPort l0[0]! .east
      let p1 ← addPort l1[0]! .west
      let e ← addEdge p0 p1
      store.set #[
        { edges := #[e], isStraight := true, initialSegment := true, boundingBox := ⟨20, 5, 40, 10⟩, sourceNode := some l0[0]! },
        { edges := #[e], boundingBox := ⟨80, 0, 20, 20⟩ },
        { edges := #[e], isStraight := true, boundingBox := ⟨100, 5, 50, 10⟩ },
        { edges := #[e], boundingBox := ⟨150, 0, 20, 20⟩ },
        { edges := #[e], isStraight := true, lastSegment := true, boundingBox := ⟨170, 5, 130, 10⟩, targetNode := some l1[0]! }]
      CompactionContext.transform g .splines (fakeSplines store #[(e, #[0, 1, 2, 3, 4])]))
  checkEq "spline chain: two curved segments" ctx.segments.size 2
  checkEqR "spline chain: segment hitbox = bounding box" ctx.segments[0]!.hitbox ⟨80, 0, 20, 20⟩
  checkEqR "spline chain: affected spline segments" (ctx.segments.map (·.affectedSplineSegments)) #[#[1], #[3]]
  checkEqR "spline chain: constraint to the next curved segment" ctx.segments[0]!.constraintTargetIds #[1]
  checkEqR "spline chain: predefined constraint (hand: CNode 2 → 3)" ctx.cGraph.predefinedHorizontalConstraints
    #[((⟨2⟩ : CNodeId), (⟨3⟩ : CNodeId))]
  -- compaction of the chain s0 (straight) - s1 (curved) - s2 (straight)
  let store ← IO.mkRef (#[] : Array SplineSegmentView)
  let ((g, nodes), a) ← LayeredM.run (do
      let g ← mkGraph (graphProps .left (routing := .splines))
      let l0 ← addLayer g #[box 0 0 20 20]
      let l1 ← addLayer g #[box 200 0 20 20]
      let p0 ← addPort l0[0]! .east
      let p1 ← addPort l1[0]! .west
      let e ← addEdge p0 p1
      store.set #[
        { edges := #[e], isStraight := true, initialSegment := true, boundingBox := ⟨20, 5, 40, 10⟩, sourceNode := some l0[0]! },
        { edges := #[e], boundingBox := ⟨80, 0, 20, 20⟩ },
        { edges := #[e], isStraight := true, lastSegment := true, boundingBox := ⟨120, 5, 80, 10⟩, targetNode := some l1[0]! }]
      runProcessor g (HorizontalGraphCompactor.processorWith (fakeSplines store #[(e, #[0, 1, 2])]))
      return (g, l0 ++ l1))
  let segs ← store.get
  checkFloat "splines LEFT: n1 at 60 (hand: segment 30 + 20 + 10)" (a.node nodes[1]!).position.x 60.0
  checkFloat "splines LEFT: curved segment moved (hand: 80 - 50)" segs[1]!.boundingBox.x 30.0
  checkFloat "splines LEFT: initial straight segment centred (hand: 25 - 40/2)" segs[0]!.boundingBox.x 5.0
  checkFloat "splines LEFT: last straight segment centred (hand: 55 - 80/2)" segs[2]!.boundingBox.x 15.0
  checkFloat "splines LEFT: graph width (hand: 80)" (a.graph g).size.x 80.0
  checkFiniteLayout "compaction_left_splines_quadratic (scanline variant)" a nodes
  -- the same chain stored like the spline router does (graph segment table + SPLINE_ROUTE_START),
  -- compacted by the registered processor (real `splineRouteAccess`): same results
  let ((g, nodes, e), a) ← LayeredM.run (do
      let g ← mkGraph (graphProps .left (routing := .splines))
      let l0 ← addLayer g #[box 0 0 20 20]
      let l1 ← addLayer g #[box 200 0 20 20]
      let p0 ← addPort l0[0]! .east
      let p1 ← addPort l1[0]! .west
      let e ← addEdge p0 p1
      let segs : Array P5Edges.Splines.SplineSegment := #[
        { edges := #[e], isStraight := true, initialSegment := true, boundingBox := ⟨20, 5, 40, 10⟩, sourceNode := some l0[0]! },
        { edges := #[e], boundingBox := ⟨80, 0, 20, 20⟩ },
        { edges := #[e], isStraight := true, lastSegment := true, boundingBox := ⟨120, 5, 80, 10⟩, targetNode := some l1[0]! }]
      modifyGraph g fun x => { x with internal := { x.internal with splineSegments := segs } }
      modifyEdge e fun x => { x with internal := { x.internal with splineRouteStart := some #[⟨0⟩, ⟨1⟩, ⟨2⟩] } }
      runProcessor g
      return (g, l0 ++ l1, e))
  let segs := (a.graph g).internal.splineSegments
  checkFloat "splines LEFT (stored segments): n1 at 60" (a.node nodes[1]!).position.x 60.0
  checkFloat "splines LEFT (stored segments): curved segment moved" segs[1]!.boundingBox.x 30.0
  checkFloat "splines LEFT (stored segments): initial straight segment centred" segs[0]!.boundingBox.x 5.0
  checkFloat "splines LEFT (stored segments): last straight segment centred" segs[2]!.boundingBox.x 15.0
  checkEq "splines LEFT (stored segments): route start kept" ((a.edge e).internal.splineRouteStart.map (·.size)) (some 3)
  let (view, _) ← LayeredM.run (do
      let g ← mkGraph (graphProps .left (routing := .splines))
      modifyGraph g fun x => { x with internal := { x.internal with splineSegments := #[{ lastSegment := true, rank := 3 }] } }
      (HorizontalGraphCompactor.splineRouteAccess g).segment 0)
  check "splineRouteAccess.segment reads the graph table" (view.lastSegment && !view.initialSegment)
  -- unavailable spline access: the nodes are still compacted
  let ((_, nodes), a) ← LayeredM.run (do
      let (g, nodes) ← buildG1 (graphProps .right (routing := .splines))
      runProcessor g
      return (g, nodes))
  checkFloat "compaction_right_splines_scanline: n0 at 60" (a.node nodes[0]!).position.x 60.0
  checkFiniteLayout "compaction_right_splines_scanline" a nodes

/-! ### Oracle cases

Generated from elk-rs traces (`scripts/oracle_layout.sh <input.json> <out.json> <trace_dir>` on
small ELK graphs with `postCompaction.strategy`/`constraints` set): the graph is the routed state of
the trace step before `HorizontalGraphCompactor` (node boxes, margins, port sides and positions,
bend points, edge labels; layered default spacings), the expectations are the trace step
`HorizontalGraphCompactor` (node positions, bend points, edge label positions, port x, graph size
and offset). Graphs: `B` six nodes / seven edges (regular vertical segments); `C` fixed-side ports
with a south → north edge (north/south segments grouped with their nodes, port margins); `D` a
self loop (routed above the node, label margin); `E` an edge label (label dummy node); `F` an
inverted west port (reversed edge); `G` twelve nodes / eighteen edges; `H` west/east/north
ports of the graph (external port dummies); `I` a connected comment box; `J` inverted west output
and east input ports (`EDGE_LENGTH` keeps their segments close); `K` graph `C` with widths 41/38
(the joined north/south segments differ by 1.5, so `NetworkSimplexCompaction` moves the south
port by 0.5). -/

/-- A node of an oracle case. -/
structure OracleNode where
  /-- Position and size. -/
  box : ElkRectangle
  type : NodeType := .normal
  margin : LMargin := {}
  /-- Ports: side and position. -/
  ports : Array (PortSide × KVector) := #[]
  /-- `InternalProperties.EXT_PORT_SIDE` of external port dummies (the trace does not record it;
  the generator derives it from the side of the dummy's port). -/
  extPortSide : PortSide := .undefined
  /-- `COMMENT_BOX`. -/
  comment : Bool := false

/-- A trace pair of elk-rs (before / after `HorizontalGraphCompactor`). Ports are numbered in
node order, then port order; edges are given in trace order. -/
structure OracleCase where
  name : String
  strategy : GraphCompactionStrategy
  constraints : ConstraintCalculationStrategy
  /-- Nodes per layer. -/
  layers : Array (Array OracleNode)
  /-- `(source port, target port, bend points, label boxes)`. -/
  edges : Array (Nat × Nat × Array KVector × Array ElkRectangle)
  /-- Expected node positions (node order). -/
  nodePositions : Array KVector
  /-- Expected bend points per edge. -/
  bendPoints : Array (Array KVector)
  /-- Expected label positions per edge. -/
  labelPositions : Array (Array KVector)
  /-- Expected port x coordinates (port order). -/
  portX : Array Float
  /-- Expected graph size and offset. -/
  size : KVector
  offset : KVector

namespace OracleCase

/-- Builds the routed graph of the case and runs the processor. -/
def build (c : OracleCase) : LayeredM (LGraphId × Array LNodeId × Array LPortId × Array LEdgeId) := do
  let g ← mkGraph (graphProps c.strategy (constraints := c.constraints))
  let mut nodes : Array LNodeId := #[]
  let mut ports : Array LPortId := #[]
  for layer in c.layers do
    let ids ← addLayer g (layer.map fun n =>
      { position := ⟨n.box.x, n.box.y⟩, size := ⟨n.box.width, n.box.height⟩, type := n.type, margin := n.margin
        props := if n.comment then ({} : PropertyMap).set LayeredOptions.COMMENT_BOX true else {}
        internal := { extPortSide := n.extPortSide } })
    for (id, n) in ids.zip layer do
      nodes := nodes.push id
      for (side, pos) in n.ports do
        ports := ports.push (← addPort id side pos)
  let mut edges : Array LEdgeId := #[]
  for (s, t, bends, labels) in c.edges do
    let e ← addEdge ports[s]! ports[t]! bends
    let mut lbs : Array LLabelId := #[]
    for r in labels do
      lbs := lbs.push (← createLabel "" { position := ⟨r.x, r.y⟩, size := ⟨r.width, r.height⟩ })
    let edgeLabels := lbs
    modifyEdge e fun ed => { ed with labels := edgeLabels }
    edges := edges.push e
  runProcessor g
  return (g, nodes, ports, edges)

/-- Compares the processed graph with the elk-rs trace. -/
def check (c : OracleCase) : TestM Unit := do
  let ((g, nodes, ports, edges), a) ← LayeredM.run c.build
  for (n, i) in nodes.zipIdx do
    let expected := c.nodePositions[i]!
    checkFloat s!"{c.name}: node {i} x" (a.node n).position.x expected.x
    checkFloat s!"{c.name}: node {i} y" (a.node n).position.y expected.y
  for (e, i) in edges.zipIdx do
    let bends := (a.edge e).bendPoints
    let expected := c.bendPoints[i]!
    checkEq s!"{c.name}: edge {i} bend count" bends.size expected.size
    for (b, j) in expected.zipIdx do
      checkFloat s!"{c.name}: edge {i} bend {j} x" bends[j]!.x b.x
      checkFloat s!"{c.name}: edge {i} bend {j} y" bends[j]!.y b.y
    for (l, j) in (a.edge e).labels.zipIdx do
      let expectedLabel := c.labelPositions[i]![j]!
      checkFloat s!"{c.name}: edge {i} label {j} x" (a.label l).position.x expectedLabel.x
      checkFloat s!"{c.name}: edge {i} label {j} y" (a.label l).position.y expectedLabel.y
  for (p, i) in ports.zipIdx do
    checkFloat s!"{c.name}: port {i} x" (a.port p).position.x c.portX[i]!
  checkFloat s!"{c.name}: graph width" (a.graph g).size.x c.size.x
  checkFloat s!"{c.name}: graph height" (a.graph g).size.y c.size.y
  checkFloat s!"{c.name}: offset x" (a.graph g).offset.x c.offset.x
  checkFloat s!"{c.name}: offset y" (a.graph g).offset.y c.offset.y

end OracleCase
/-- Oracle case `oracleB_edgeLength_quadratic`. -/
def oracleB_edgeLength_quadratic : OracleCase where
  name := "oracleB_edgeLength_quadratic"
  strategy := .edgeLength
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 5, 30, 60⟩, ports := #[(.east, ⟨30, 20⟩), (.east, ⟨30, 40⟩)] },
        { box := ⟨0, 85, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨60, 0, 20, 50⟩, ports := #[(.east, ⟨20, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨53.333333333333336, 75, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨50, 125, 40, 20⟩, ports := #[(.east, ⟨40, 10⟩), (.west, ⟨-0.0, 10⟩)] }],
      #[{ box := ⟨110, 75, 30, 30⟩, ports := #[(.west, ⟨-0.0, 22.5⟩), (.west, ⟨-0.0, 15⟩), (.west, ⟨-0.0, 7.5⟩)] }]]
  edges := #[(0, 5, #[], #[]),
    (1, 8, #[⟨40, 45⟩, ⟨40, 85⟩], #[]),
    (2, 7, #[], #[]),
    (3, 10, #[⟨40, 105⟩, ⟨40, 135⟩], #[]),
    (4, 13, #[⟨100, 25⟩, ⟨100, 82.5⟩], #[]),
    (6, 12, #[], #[]),
    (9, 11, #[⟨100, 135⟩, ⟨100, 97.5⟩], #[])]
  nodePositions := #[⟨11, 5⟩, ⟨1, 85⟩, ⟨61, 0⟩, ⟨61, 75⟩, ⟨51, 125⟩, ⟨111, 75⟩]
  bendPoints := #[#[], #[⟨51, 45⟩, ⟨51, 85⟩], #[], #[⟨41, 105⟩, ⟨41, 135⟩], #[⟨101, 25⟩, ⟨101, 82.5⟩], #[], #[⟨101, 135⟩, ⟨101, 97.5⟩]]
  labelPositions := #[#[], #[], #[], #[], #[], #[], #[]]
  portX := #[30, 30, 30, 30, 20, -0.0, 30, -0.0, -0.0, 40, -0.0, -0.0, -0.0, -0.0]
  size := ⟨140, 145⟩
  offset := ⟨-1, 0⟩

/-- Oracle case `oracleB_edgeLength_scanline`. -/
def oracleB_edgeLength_scanline : OracleCase where
  name := "oracleB_edgeLength_scanline"
  strategy := .edgeLength
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 5, 30, 60⟩, ports := #[(.east, ⟨30, 20⟩), (.east, ⟨30, 40⟩)] },
        { box := ⟨0, 85, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨60, 0, 20, 50⟩, ports := #[(.east, ⟨20, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨53.333333333333336, 75, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨50, 125, 40, 20⟩, ports := #[(.east, ⟨40, 10⟩), (.west, ⟨-0.0, 10⟩)] }],
      #[{ box := ⟨110, 75, 30, 30⟩, ports := #[(.west, ⟨-0.0, 22.5⟩), (.west, ⟨-0.0, 15⟩), (.west, ⟨-0.0, 7.5⟩)] }]]
  edges := #[(0, 5, #[], #[]),
    (1, 8, #[⟨40, 45⟩, ⟨40, 85⟩], #[]),
    (2, 7, #[], #[]),
    (3, 10, #[⟨40, 105⟩, ⟨40, 135⟩], #[]),
    (4, 13, #[⟨100, 25⟩, ⟨100, 82.5⟩], #[]),
    (6, 12, #[], #[]),
    (9, 11, #[⟨100, 135⟩, ⟨100, 97.5⟩], #[])]
  nodePositions := #[⟨11, 5⟩, ⟨1, 85⟩, ⟨61, 0⟩, ⟨61, 75⟩, ⟨51, 125⟩, ⟨111, 75⟩]
  bendPoints := #[#[], #[⟨51, 45⟩, ⟨51, 85⟩], #[], #[⟨41, 105⟩, ⟨41, 135⟩], #[⟨101, 25⟩, ⟨101, 82.5⟩], #[], #[⟨101, 135⟩, ⟨101, 97.5⟩]]
  labelPositions := #[#[], #[], #[], #[], #[], #[], #[]]
  portX := #[30, 30, 30, 30, 20, -0.0, 30, -0.0, -0.0, 40, -0.0, -0.0, -0.0, -0.0]
  size := ⟨140, 145⟩
  offset := ⟨-1, 0⟩

/-- Oracle case `oracleB_left_quadratic`. -/
def oracleB_left_quadratic : OracleCase where
  name := "oracleB_left_quadratic"
  strategy := .left
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 5, 30, 60⟩, ports := #[(.east, ⟨30, 20⟩), (.east, ⟨30, 40⟩)] },
        { box := ⟨0, 85, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨60, 0, 20, 50⟩, ports := #[(.east, ⟨20, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨53.333333333333336, 75, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨50, 125, 40, 20⟩, ports := #[(.east, ⟨40, 10⟩), (.west, ⟨-0.0, 10⟩)] }],
      #[{ box := ⟨110, 75, 30, 30⟩, ports := #[(.west, ⟨-0.0, 22.5⟩), (.west, ⟨-0.0, 15⟩), (.west, ⟨-0.0, 7.5⟩)] }]]
  edges := #[(0, 5, #[], #[]),
    (1, 8, #[⟨40, 45⟩, ⟨40, 85⟩], #[]),
    (2, 7, #[], #[]),
    (3, 10, #[⟨40, 105⟩, ⟨40, 135⟩], #[]),
    (4, 13, #[⟨100, 25⟩, ⟨100, 82.5⟩], #[]),
    (6, 12, #[], #[]),
    (9, 11, #[⟨100, 135⟩, ⟨100, 97.5⟩], #[])]
  nodePositions := #[⟨0, 5⟩, ⟨0, 85⟩, ⟨50, 0⟩, ⟨50, 75⟩, ⟨50, 125⟩, ⟨110, 75⟩]
  bendPoints := #[#[], #[⟨40, 45⟩, ⟨40, 85⟩], #[], #[⟨40, 105⟩, ⟨40, 135⟩], #[⟨90, 25⟩, ⟨90, 82.5⟩], #[], #[⟨100, 135⟩, ⟨100, 97.5⟩]]
  labelPositions := #[#[], #[], #[], #[], #[], #[], #[]]
  portX := #[30, 30, 30, 30, 20, -0.0, 30, -0.0, -0.0, 40, -0.0, -0.0, -0.0, -0.0]
  size := ⟨140, 145⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleB_leftRightConnectionLocking_scanline`. -/
def oracleB_leftRightConnectionLocking_scanline : OracleCase where
  name := "oracleB_leftRightConnectionLocking_scanline"
  strategy := .leftRightConnectionLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 5, 30, 60⟩, ports := #[(.east, ⟨30, 20⟩), (.east, ⟨30, 40⟩)] },
        { box := ⟨0, 85, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨60, 0, 20, 50⟩, ports := #[(.east, ⟨20, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨53.333333333333336, 75, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨50, 125, 40, 20⟩, ports := #[(.east, ⟨40, 10⟩), (.west, ⟨-0.0, 10⟩)] }],
      #[{ box := ⟨110, 75, 30, 30⟩, ports := #[(.west, ⟨-0.0, 22.5⟩), (.west, ⟨-0.0, 15⟩), (.west, ⟨-0.0, 7.5⟩)] }]]
  edges := #[(0, 5, #[], #[]),
    (1, 8, #[⟨40, 45⟩, ⟨40, 85⟩], #[]),
    (2, 7, #[], #[]),
    (3, 10, #[⟨40, 105⟩, ⟨40, 135⟩], #[]),
    (4, 13, #[⟨100, 25⟩, ⟨100, 82.5⟩], #[]),
    (6, 12, #[], #[]),
    (9, 11, #[⟨100, 135⟩, ⟨100, 97.5⟩], #[])]
  nodePositions := #[⟨0, 5⟩, ⟨0, 85⟩, ⟨70, 0⟩, ⟨50, 75⟩, ⟨50, 125⟩, ⟨110, 75⟩]
  bendPoints := #[#[], #[⟨40, 45⟩, ⟨40, 85⟩], #[], #[⟨40, 105⟩, ⟨40, 135⟩], #[⟨100, 25⟩, ⟨100, 82.5⟩], #[], #[⟨100, 135⟩, ⟨100, 97.5⟩]]
  labelPositions := #[#[], #[], #[], #[], #[], #[], #[]]
  portX := #[30, 30, 30, 30, 20, -0.0, 30, -0.0, -0.0, 40, -0.0, -0.0, -0.0, -0.0]
  size := ⟨140, 145⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleB_leftRightConstraintLocking_quadratic`. -/
def oracleB_leftRightConstraintLocking_quadratic : OracleCase where
  name := "oracleB_leftRightConstraintLocking_quadratic"
  strategy := .leftRightConstraintLocking
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 5, 30, 60⟩, ports := #[(.east, ⟨30, 20⟩), (.east, ⟨30, 40⟩)] },
        { box := ⟨0, 85, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨60, 0, 20, 50⟩, ports := #[(.east, ⟨20, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨53.333333333333336, 75, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨50, 125, 40, 20⟩, ports := #[(.east, ⟨40, 10⟩), (.west, ⟨-0.0, 10⟩)] }],
      #[{ box := ⟨110, 75, 30, 30⟩, ports := #[(.west, ⟨-0.0, 22.5⟩), (.west, ⟨-0.0, 15⟩), (.west, ⟨-0.0, 7.5⟩)] }]]
  edges := #[(0, 5, #[], #[]),
    (1, 8, #[⟨40, 45⟩, ⟨40, 85⟩], #[]),
    (2, 7, #[], #[]),
    (3, 10, #[⟨40, 105⟩, ⟨40, 135⟩], #[]),
    (4, 13, #[⟨100, 25⟩, ⟨100, 82.5⟩], #[]),
    (6, 12, #[], #[]),
    (9, 11, #[⟨100, 135⟩, ⟨100, 97.5⟩], #[])]
  nodePositions := #[⟨10, 5⟩, ⟨0, 85⟩, ⟨70, 0⟩, ⟨60, 75⟩, ⟨50, 125⟩, ⟨110, 75⟩]
  bendPoints := #[#[], #[⟨50, 45⟩, ⟨50, 85⟩], #[], #[⟨40, 105⟩, ⟨40, 135⟩], #[⟨100, 25⟩, ⟨100, 82.5⟩], #[], #[⟨100, 135⟩, ⟨100, 97.5⟩]]
  labelPositions := #[#[], #[], #[], #[], #[], #[], #[]]
  portX := #[30, 30, 30, 30, 20, -0.0, 30, -0.0, -0.0, 40, -0.0, -0.0, -0.0, -0.0]
  size := ⟨140, 145⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleB_leftRightConstraintLocking_scanline`. -/
def oracleB_leftRightConstraintLocking_scanline : OracleCase where
  name := "oracleB_leftRightConstraintLocking_scanline"
  strategy := .leftRightConstraintLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 5, 30, 60⟩, ports := #[(.east, ⟨30, 20⟩), (.east, ⟨30, 40⟩)] },
        { box := ⟨0, 85, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨60, 0, 20, 50⟩, ports := #[(.east, ⟨20, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨53.333333333333336, 75, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨50, 125, 40, 20⟩, ports := #[(.east, ⟨40, 10⟩), (.west, ⟨-0.0, 10⟩)] }],
      #[{ box := ⟨110, 75, 30, 30⟩, ports := #[(.west, ⟨-0.0, 22.5⟩), (.west, ⟨-0.0, 15⟩), (.west, ⟨-0.0, 7.5⟩)] }]]
  edges := #[(0, 5, #[], #[]),
    (1, 8, #[⟨40, 45⟩, ⟨40, 85⟩], #[]),
    (2, 7, #[], #[]),
    (3, 10, #[⟨40, 105⟩, ⟨40, 135⟩], #[]),
    (4, 13, #[⟨100, 25⟩, ⟨100, 82.5⟩], #[]),
    (6, 12, #[], #[]),
    (9, 11, #[⟨100, 135⟩, ⟨100, 97.5⟩], #[])]
  nodePositions := #[⟨10, 5⟩, ⟨0, 85⟩, ⟨70, 0⟩, ⟨60, 75⟩, ⟨50, 125⟩, ⟨110, 75⟩]
  bendPoints := #[#[], #[⟨50, 45⟩, ⟨50, 85⟩], #[], #[⟨40, 105⟩, ⟨40, 135⟩], #[⟨100, 25⟩, ⟨100, 82.5⟩], #[], #[⟨100, 135⟩, ⟨100, 97.5⟩]]
  labelPositions := #[#[], #[], #[], #[], #[], #[], #[]]
  portX := #[30, 30, 30, 30, 20, -0.0, 30, -0.0, -0.0, 40, -0.0, -0.0, -0.0, -0.0]
  size := ⟨140, 145⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleB_left_scanline`. -/
def oracleB_left_scanline : OracleCase where
  name := "oracleB_left_scanline"
  strategy := .left
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 5, 30, 60⟩, ports := #[(.east, ⟨30, 20⟩), (.east, ⟨30, 40⟩)] },
        { box := ⟨0, 85, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨60, 0, 20, 50⟩, ports := #[(.east, ⟨20, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨53.333333333333336, 75, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨50, 125, 40, 20⟩, ports := #[(.east, ⟨40, 10⟩), (.west, ⟨-0.0, 10⟩)] }],
      #[{ box := ⟨110, 75, 30, 30⟩, ports := #[(.west, ⟨-0.0, 22.5⟩), (.west, ⟨-0.0, 15⟩), (.west, ⟨-0.0, 7.5⟩)] }]]
  edges := #[(0, 5, #[], #[]),
    (1, 8, #[⟨40, 45⟩, ⟨40, 85⟩], #[]),
    (2, 7, #[], #[]),
    (3, 10, #[⟨40, 105⟩, ⟨40, 135⟩], #[]),
    (4, 13, #[⟨100, 25⟩, ⟨100, 82.5⟩], #[]),
    (6, 12, #[], #[]),
    (9, 11, #[⟨100, 135⟩, ⟨100, 97.5⟩], #[])]
  nodePositions := #[⟨0, 5⟩, ⟨0, 85⟩, ⟨50, 0⟩, ⟨50, 75⟩, ⟨50, 125⟩, ⟨110, 75⟩]
  bendPoints := #[#[], #[⟨40, 45⟩, ⟨40, 85⟩], #[], #[⟨40, 105⟩, ⟨40, 135⟩], #[⟨90, 25⟩, ⟨90, 82.5⟩], #[], #[⟨100, 135⟩, ⟨100, 97.5⟩]]
  labelPositions := #[#[], #[], #[], #[], #[], #[], #[]]
  portX := #[30, 30, 30, 30, 20, -0.0, 30, -0.0, -0.0, 40, -0.0, -0.0, -0.0, -0.0]
  size := ⟨140, 145⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleB_right_scanline`. -/
def oracleB_right_scanline : OracleCase where
  name := "oracleB_right_scanline"
  strategy := .right
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 5, 30, 60⟩, ports := #[(.east, ⟨30, 20⟩), (.east, ⟨30, 40⟩)] },
        { box := ⟨0, 85, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨60, 0, 20, 50⟩, ports := #[(.east, ⟨20, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨53.333333333333336, 75, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨50, 125, 40, 20⟩, ports := #[(.east, ⟨40, 10⟩), (.west, ⟨-0.0, 10⟩)] }],
      #[{ box := ⟨110, 75, 30, 30⟩, ports := #[(.west, ⟨-0.0, 22.5⟩), (.west, ⟨-0.0, 15⟩), (.west, ⟨-0.0, 7.5⟩)] }]]
  edges := #[(0, 5, #[], #[]),
    (1, 8, #[⟨40, 45⟩, ⟨40, 85⟩], #[]),
    (2, 7, #[], #[]),
    (3, 10, #[⟨40, 105⟩, ⟨40, 135⟩], #[]),
    (4, 13, #[⟨100, 25⟩, ⟨100, 82.5⟩], #[]),
    (6, 12, #[], #[]),
    (9, 11, #[⟨100, 135⟩, ⟨100, 97.5⟩], #[])]
  nodePositions := #[⟨10, 5⟩, ⟨0, 85⟩, ⟨70, 0⟩, ⟨60, 75⟩, ⟨50, 125⟩, ⟨110, 75⟩]
  bendPoints := #[#[], #[⟨50, 45⟩, ⟨50, 85⟩], #[], #[⟨40, 105⟩, ⟨40, 135⟩], #[⟨100, 25⟩, ⟨100, 82.5⟩], #[], #[⟨100, 135⟩, ⟨100, 97.5⟩]]
  labelPositions := #[#[], #[], #[], #[], #[], #[], #[]]
  portX := #[30, 30, 30, 30, 20, -0.0, 30, -0.0, -0.0, 40, -0.0, -0.0, -0.0, -0.0]
  size := ⟨140, 145⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleC_edgeLength_quadratic`. -/
def oracleC_edgeLength_quadratic : OracleCase where
  name := "oracleC_edgeLength_quadratic"
  strategy := .edgeLength
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 10, 40, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨40, 13⟩), (.south, ⟨18, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨64, 74, 40, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨18, -4⟩), (.east, ⟨40, 15⟩)] }],
      #[{ box := ⟨124, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨114, 89⟩, ⟨114, 35⟩], #[])]
  nodePositions := #[⟨0, 10⟩, ⟨64, 0⟩, ⟨54, 74⟩, ⟨114, 15⟩]
  bendPoints := #[#[], #[⟨20, 60⟩, ⟨74, 60⟩], #[], #[⟨104, 89⟩, ⟨104, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[40, 18, 30, -0.0, 18, 40, -0.0, -0.0]
  size := ⟨144, 104⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleC_edgeLength_scanline`. -/
def oracleC_edgeLength_scanline : OracleCase where
  name := "oracleC_edgeLength_scanline"
  strategy := .edgeLength
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 10, 40, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨40, 13⟩), (.south, ⟨18, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨64, 74, 40, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨18, -4⟩), (.east, ⟨40, 15⟩)] }],
      #[{ box := ⟨124, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨114, 89⟩, ⟨114, 35⟩], #[])]
  nodePositions := #[⟨1, 10⟩, ⟨65, 0⟩, ⟨55, 74⟩, ⟨115, 15⟩]
  bendPoints := #[#[], #[⟨21, 60⟩, ⟨75, 60⟩], #[], #[⟨105, 89⟩, ⟨105, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[40, 18, 30, -0.0, 18, 40, -0.0, -0.0]
  size := ⟨144, 104⟩
  offset := ⟨-1, 0⟩

/-- Oracle case `oracleC_left_quadratic`. -/
def oracleC_left_quadratic : OracleCase where
  name := "oracleC_left_quadratic"
  strategy := .left
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 10, 40, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨40, 13⟩), (.south, ⟨18, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨64, 74, 40, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨18, -4⟩), (.east, ⟨40, 15⟩)] }],
      #[{ box := ⟨124, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨114, 89⟩, ⟨114, 35⟩], #[])]
  nodePositions := #[⟨0, 10⟩, ⟨64, 0⟩, ⟨0, 74⟩, ⟨114, 15⟩]
  bendPoints := #[#[], #[⟨20, 60⟩, ⟨20, 60⟩], #[], #[⟨104, 89⟩, ⟨104, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[40, 18, 30, -0.0, 18, 40, -0.0, -0.0]
  size := ⟨144, 104⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleC_leftRightConnectionLocking_scanline`. -/
def oracleC_leftRightConnectionLocking_scanline : OracleCase where
  name := "oracleC_leftRightConnectionLocking_scanline"
  strategy := .leftRightConnectionLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 10, 40, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨40, 13⟩), (.south, ⟨18, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨64, 74, 40, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨18, -4⟩), (.east, ⟨40, 15⟩)] }],
      #[{ box := ⟨124, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨114, 89⟩, ⟨114, 35⟩], #[])]
  nodePositions := #[⟨0, 10⟩, ⟨64, 0⟩, ⟨54, 74⟩, ⟨114, 15⟩]
  bendPoints := #[#[], #[⟨20, 60⟩, ⟨74, 60⟩], #[], #[⟨104, 89⟩, ⟨104, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[40, 18, 30, -0.0, 18, 40, -0.0, -0.0]
  size := ⟨144, 104⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleC_leftRightConstraintLocking_quadratic`. -/
def oracleC_leftRightConstraintLocking_quadratic : OracleCase where
  name := "oracleC_leftRightConstraintLocking_quadratic"
  strategy := .leftRightConstraintLocking
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 10, 40, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨40, 13⟩), (.south, ⟨18, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨64, 74, 40, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨18, -4⟩), (.east, ⟨40, 15⟩)] }],
      #[{ box := ⟨124, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨114, 89⟩, ⟨114, 35⟩], #[])]
  nodePositions := #[⟨0, 10⟩, ⟨64, 0⟩, ⟨54, 74⟩, ⟨114, 15⟩]
  bendPoints := #[#[], #[⟨20, 60⟩, ⟨74, 60⟩], #[], #[⟨104, 89⟩, ⟨104, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[40, 18, 30, -0.0, 18, 40, -0.0, -0.0]
  size := ⟨144, 104⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleC_leftRightConstraintLocking_scanline`. -/
def oracleC_leftRightConstraintLocking_scanline : OracleCase where
  name := "oracleC_leftRightConstraintLocking_scanline"
  strategy := .leftRightConstraintLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 10, 40, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨40, 13⟩), (.south, ⟨18, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨64, 74, 40, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨18, -4⟩), (.east, ⟨40, 15⟩)] }],
      #[{ box := ⟨124, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨114, 89⟩, ⟨114, 35⟩], #[])]
  nodePositions := #[⟨0, 10⟩, ⟨64, 0⟩, ⟨54, 74⟩, ⟨114, 15⟩]
  bendPoints := #[#[], #[⟨20, 60⟩, ⟨74, 60⟩], #[], #[⟨104, 89⟩, ⟨104, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[40, 18, 30, -0.0, 18, 40, -0.0, -0.0]
  size := ⟨144, 104⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleC_left_scanline`. -/
def oracleC_left_scanline : OracleCase where
  name := "oracleC_left_scanline"
  strategy := .left
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 10, 40, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨40, 13⟩), (.south, ⟨18, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨64, 74, 40, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨18, -4⟩), (.east, ⟨40, 15⟩)] }],
      #[{ box := ⟨124, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨114, 89⟩, ⟨114, 35⟩], #[])]
  nodePositions := #[⟨0, 10⟩, ⟨64, 0⟩, ⟨0, 74⟩, ⟨114, 15⟩]
  bendPoints := #[#[], #[⟨20, 60⟩, ⟨20, 60⟩], #[], #[⟨104, 89⟩, ⟨104, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[40, 18, 30, -0.0, 18, 40, -0.0, -0.0]
  size := ⟨144, 104⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleC_right_scanline`. -/
def oracleC_right_scanline : OracleCase where
  name := "oracleC_right_scanline"
  strategy := .right
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 10, 40, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨40, 13⟩), (.south, ⟨18, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨64, 74, 40, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨18, -4⟩), (.east, ⟨40, 15⟩)] }],
      #[{ box := ⟨124, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨114, 89⟩, ⟨114, 35⟩], #[])]
  nodePositions := #[⟨10, 10⟩, ⟨74, 0⟩, ⟨64, 74⟩, ⟨124, 15⟩]
  bendPoints := #[#[], #[⟨30, 60⟩, ⟨84, 60⟩], #[], #[⟨114, 89⟩, ⟨114, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[40, 18, 30, -0.0, 18, 40, -0.0, -0.0]
  size := ⟨144, 104⟩
  offset := ⟨-10, 0⟩

/-- Oracle case `oracleD_edgeLength_scanline`. -/
def oracleD_edgeLength_scanline : OracleCase where
  name := "oracleD_edgeLength_scanline"
  strategy := .edgeLength
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 22, 40, 40⟩, margin := ⟨22, 0, 0, 0⟩, ports := #[(.north, ⟨13.333333333333334, -0.0⟩), (.north, ⟨26.666666666666668, -0.0⟩), (.east, ⟨40, 13.333333333333334⟩), (.east, ⟨40, 26.666666666666668⟩)] }],
      #[{ box := ⟨60, 33.66666666666667, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨110, 28.666666666666668, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 1, #[⟨13.333333333333334, 12⟩, ⟨26.666666666666668, 12⟩], #[⟨10, 0, 20, 10⟩]),
    (2, 7, #[⟨50, 35.333333333333336⟩, ⟨50, 22.66666666666667⟩, ⟨100, 22.66666666666667⟩, ⟨100, 38.66666666666667⟩], #[]),
    (3, 5, #[], #[]),
    (4, 6, #[], #[])]
  nodePositions := #[⟨1, 22⟩, ⟨61, 33.66666666666667⟩, ⟨111, 28.666666666666668⟩]
  bendPoints := #[#[⟨14.333333333333334, 12⟩, ⟨27.666666666666668, 12⟩], #[⟨51, 35.333333333333336⟩, ⟨51, 22.66666666666667⟩, ⟨101, 22.66666666666667⟩, ⟨101, 38.66666666666667⟩], #[], #[]]
  labelPositions := #[#[⟨11, 0⟩], #[], #[], #[]]
  portX := #[13.333333333333334, 26.666666666666668, 40, 40, 30, -0.0, -0.0, -0.0]
  size := ⟨140, 63.68666666666667⟩
  offset := ⟨-1, 0.019999999999999574⟩

/-- Oracle case `oracleD_leftRightConnectionLocking_scanline`. -/
def oracleD_leftRightConnectionLocking_scanline : OracleCase where
  name := "oracleD_leftRightConnectionLocking_scanline"
  strategy := .leftRightConnectionLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 22, 40, 40⟩, margin := ⟨22, 0, 0, 0⟩, ports := #[(.north, ⟨13.333333333333334, -0.0⟩), (.north, ⟨26.666666666666668, -0.0⟩), (.east, ⟨40, 13.333333333333334⟩), (.east, ⟨40, 26.666666666666668⟩)] }],
      #[{ box := ⟨60, 33.66666666666667, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨110, 28.666666666666668, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 1, #[⟨13.333333333333334, 12⟩, ⟨26.666666666666668, 12⟩], #[⟨10, 0, 20, 10⟩]),
    (2, 7, #[⟨50, 35.333333333333336⟩, ⟨50, 22.66666666666667⟩, ⟨100, 22.66666666666667⟩, ⟨100, 38.66666666666667⟩], #[]),
    (3, 5, #[], #[]),
    (4, 6, #[], #[])]
  nodePositions := #[⟨0, 22⟩, ⟨60, 33.66666666666667⟩, ⟨110, 28.666666666666668⟩]
  bendPoints := #[#[⟨13.333333333333334, 12⟩, ⟨26.666666666666668, 12⟩], #[⟨50, 35.333333333333336⟩, ⟨50, 22.66666666666667⟩, ⟨100, 22.66666666666667⟩, ⟨100, 38.66666666666667⟩], #[], #[]]
  labelPositions := #[#[⟨10, 0⟩], #[], #[], #[]]
  portX := #[13.333333333333334, 26.666666666666668, 40, 40, 30, -0.0, -0.0, -0.0]
  size := ⟨140, 63.68666666666667⟩
  offset := ⟨0, 0.019999999999999574⟩

/-- Oracle case `oracleD_leftRightConstraintLocking_quadratic`. -/
def oracleD_leftRightConstraintLocking_quadratic : OracleCase where
  name := "oracleD_leftRightConstraintLocking_quadratic"
  strategy := .leftRightConstraintLocking
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 22, 40, 40⟩, margin := ⟨22, 0, 0, 0⟩, ports := #[(.north, ⟨13.333333333333334, -0.0⟩), (.north, ⟨26.666666666666668, -0.0⟩), (.east, ⟨40, 13.333333333333334⟩), (.east, ⟨40, 26.666666666666668⟩)] }],
      #[{ box := ⟨60, 33.66666666666667, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨110, 28.666666666666668, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 1, #[⟨13.333333333333334, 12⟩, ⟨26.666666666666668, 12⟩], #[⟨10, 0, 20, 10⟩]),
    (2, 7, #[⟨50, 35.333333333333336⟩, ⟨50, 22.66666666666667⟩, ⟨100, 22.66666666666667⟩, ⟨100, 38.66666666666667⟩], #[]),
    (3, 5, #[], #[]),
    (4, 6, #[], #[])]
  nodePositions := #[⟨0, 22⟩, ⟨60, 33.66666666666667⟩, ⟨110, 28.666666666666668⟩]
  bendPoints := #[#[⟨13.333333333333334, 12⟩, ⟨26.666666666666668, 12⟩], #[⟨50, 35.333333333333336⟩, ⟨50, 22.66666666666667⟩, ⟨100, 22.66666666666667⟩, ⟨100, 38.66666666666667⟩], #[], #[]]
  labelPositions := #[#[⟨10, 0⟩], #[], #[], #[]]
  portX := #[13.333333333333334, 26.666666666666668, 40, 40, 30, -0.0, -0.0, -0.0]
  size := ⟨140, 63.66666666666667⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleD_left_scanline`. -/
def oracleD_left_scanline : OracleCase where
  name := "oracleD_left_scanline"
  strategy := .left
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 22, 40, 40⟩, margin := ⟨22, 0, 0, 0⟩, ports := #[(.north, ⟨13.333333333333334, -0.0⟩), (.north, ⟨26.666666666666668, -0.0⟩), (.east, ⟨40, 13.333333333333334⟩), (.east, ⟨40, 26.666666666666668⟩)] }],
      #[{ box := ⟨60, 33.66666666666667, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨110, 28.666666666666668, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 1, #[⟨13.333333333333334, 12⟩, ⟨26.666666666666668, 12⟩], #[⟨10, 0, 20, 10⟩]),
    (2, 7, #[⟨50, 35.333333333333336⟩, ⟨50, 22.66666666666667⟩, ⟨100, 22.66666666666667⟩, ⟨100, 38.66666666666667⟩], #[]),
    (3, 5, #[], #[]),
    (4, 6, #[], #[])]
  nodePositions := #[⟨0, 22⟩, ⟨60, 33.66666666666667⟩, ⟨110, 28.666666666666668⟩]
  bendPoints := #[#[⟨13.333333333333334, 12⟩, ⟨26.666666666666668, 12⟩], #[⟨50, 35.333333333333336⟩, ⟨50, 22.66666666666667⟩, ⟨100, 22.66666666666667⟩, ⟨100, 38.66666666666667⟩], #[], #[]]
  labelPositions := #[#[⟨10, 0⟩], #[], #[], #[]]
  portX := #[13.333333333333334, 26.666666666666668, 40, 40, 30, -0.0, -0.0, -0.0]
  size := ⟨140, 63.68666666666667⟩
  offset := ⟨0, 0.019999999999999574⟩

/-- Oracle case `oracleD_right_scanline`. -/
def oracleD_right_scanline : OracleCase where
  name := "oracleD_right_scanline"
  strategy := .right
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 22, 40, 40⟩, margin := ⟨22, 0, 0, 0⟩, ports := #[(.north, ⟨13.333333333333334, -0.0⟩), (.north, ⟨26.666666666666668, -0.0⟩), (.east, ⟨40, 13.333333333333334⟩), (.east, ⟨40, 26.666666666666668⟩)] }],
      #[{ box := ⟨60, 33.66666666666667, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨110, 28.666666666666668, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 1, #[⟨13.333333333333334, 12⟩, ⟨26.666666666666668, 12⟩], #[⟨10, 0, 20, 10⟩]),
    (2, 7, #[⟨50, 35.333333333333336⟩, ⟨50, 22.66666666666667⟩, ⟨100, 22.66666666666667⟩, ⟨100, 38.66666666666667⟩], #[]),
    (3, 5, #[], #[]),
    (4, 6, #[], #[])]
  nodePositions := #[⟨0, 22⟩, ⟨60, 33.66666666666667⟩, ⟨110, 28.666666666666668⟩]
  bendPoints := #[#[⟨13.333333333333334, 12⟩, ⟨26.666666666666668, 12⟩], #[⟨50, 35.333333333333336⟩, ⟨50, 22.66666666666667⟩, ⟨100, 22.66666666666667⟩, ⟨100, 38.66666666666667⟩], #[], #[]]
  labelPositions := #[#[⟨10, 0⟩], #[], #[], #[]]
  portX := #[13.333333333333334, 26.666666666666668, 40, 40, 30, -0.0, -0.0, -0.0]
  size := ⟨140, 63.68666666666667⟩
  offset := ⟨0, 0.019999999999999574⟩

/-- Oracle case `oracleE_edgeLength_scanline`. -/
def oracleE_edgeLength_scanline : OracleCase where
  name := "oracleE_edgeLength_scanline"
  strategy := .edgeLength
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 20, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨50, 0, 30, 60⟩, ports := #[(.east, ⟨30, 30⟩), (.west, ⟨-0.0, 30⟩)] },
        { box := ⟨50, 80, 30, 16⟩, type := .label, ports := #[(.east, ⟨0, 0⟩), (.west, ⟨0, 0⟩)] }],
      #[{ box := ⟨100, 20, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 5, #[⟨40, 40⟩, ⟨40, 80⟩], #[]),
    (2, 7, #[], #[]),
    (4, 6, #[⟨90, 80⟩, ⟨90, 40⟩], #[])]
  nodePositions := #[⟨0, 20⟩, ⟨50, 0⟩, ⟨50, 80⟩, ⟨100, 20⟩]
  bendPoints := #[#[], #[⟨40, 40⟩, ⟨40, 80⟩], #[], #[⟨90, 80⟩, ⟨90, 40⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[30, 30, 30, -0.0, 0, 0, -0.0, -0.0]
  size := ⟨130, 96⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleE_leftRightConnectionLocking_scanline`. -/
def oracleE_leftRightConnectionLocking_scanline : OracleCase where
  name := "oracleE_leftRightConnectionLocking_scanline"
  strategy := .leftRightConnectionLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 20, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨50, 0, 30, 60⟩, ports := #[(.east, ⟨30, 30⟩), (.west, ⟨-0.0, 30⟩)] },
        { box := ⟨50, 80, 30, 16⟩, type := .label, ports := #[(.east, ⟨0, 0⟩), (.west, ⟨0, 0⟩)] }],
      #[{ box := ⟨100, 20, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 5, #[⟨40, 40⟩, ⟨40, 80⟩], #[]),
    (2, 7, #[], #[]),
    (4, 6, #[⟨90, 80⟩, ⟨90, 40⟩], #[])]
  nodePositions := #[⟨0, 20⟩, ⟨50, 0⟩, ⟨50, 80⟩, ⟨100, 20⟩]
  bendPoints := #[#[], #[⟨40, 40⟩, ⟨40, 80⟩], #[], #[⟨90, 80⟩, ⟨90, 40⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[30, 30, 30, -0.0, 0, 0, -0.0, -0.0]
  size := ⟨130, 96⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleE_leftRightConstraintLocking_quadratic`. -/
def oracleE_leftRightConstraintLocking_quadratic : OracleCase where
  name := "oracleE_leftRightConstraintLocking_quadratic"
  strategy := .leftRightConstraintLocking
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 20, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨50, 0, 30, 60⟩, ports := #[(.east, ⟨30, 30⟩), (.west, ⟨-0.0, 30⟩)] },
        { box := ⟨50, 80, 30, 16⟩, type := .label, ports := #[(.east, ⟨0, 0⟩), (.west, ⟨0, 0⟩)] }],
      #[{ box := ⟨100, 20, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 5, #[⟨40, 40⟩, ⟨40, 80⟩], #[]),
    (2, 7, #[], #[]),
    (4, 6, #[⟨90, 80⟩, ⟨90, 40⟩], #[])]
  nodePositions := #[⟨0, 20⟩, ⟨50, 0⟩, ⟨50, 80⟩, ⟨100, 20⟩]
  bendPoints := #[#[], #[⟨40, 40⟩, ⟨40, 80⟩], #[], #[⟨90, 80⟩, ⟨90, 40⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[30, 30, 30, -0.0, 0, 0, -0.0, -0.0]
  size := ⟨130, 96⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleE_left_scanline`. -/
def oracleE_left_scanline : OracleCase where
  name := "oracleE_left_scanline"
  strategy := .left
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 20, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨50, 0, 30, 60⟩, ports := #[(.east, ⟨30, 30⟩), (.west, ⟨-0.0, 30⟩)] },
        { box := ⟨50, 80, 30, 16⟩, type := .label, ports := #[(.east, ⟨0, 0⟩), (.west, ⟨0, 0⟩)] }],
      #[{ box := ⟨100, 20, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 5, #[⟨40, 40⟩, ⟨40, 80⟩], #[]),
    (2, 7, #[], #[]),
    (4, 6, #[⟨90, 80⟩, ⟨90, 40⟩], #[])]
  nodePositions := #[⟨0, 20⟩, ⟨50, 0⟩, ⟨50, 80⟩, ⟨100, 20⟩]
  bendPoints := #[#[], #[⟨40, 40⟩, ⟨40, 80⟩], #[], #[⟨90, 80⟩, ⟨90, 40⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[30, 30, 30, -0.0, 0, 0, -0.0, -0.0]
  size := ⟨130, 96⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleE_right_scanline`. -/
def oracleE_right_scanline : OracleCase where
  name := "oracleE_right_scanline"
  strategy := .right
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 20, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨50, 0, 30, 60⟩, ports := #[(.east, ⟨30, 30⟩), (.west, ⟨-0.0, 30⟩)] },
        { box := ⟨50, 80, 30, 16⟩, type := .label, ports := #[(.east, ⟨0, 0⟩), (.west, ⟨0, 0⟩)] }],
      #[{ box := ⟨100, 20, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 5, #[⟨40, 40⟩, ⟨40, 80⟩], #[]),
    (2, 7, #[], #[]),
    (4, 6, #[⟨90, 80⟩, ⟨90, 40⟩], #[])]
  nodePositions := #[⟨0, 20⟩, ⟨50, 0⟩, ⟨50, 80⟩, ⟨100, 20⟩]
  bendPoints := #[#[], #[⟨40, 40⟩, ⟨40, 80⟩], #[], #[⟨90, 80⟩, ⟨90, 40⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[30, 30, 30, -0.0, 0, 0, -0.0, -0.0]
  size := ⟨130, 96⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleF_edgeLength_scanline`. -/
def oracleF_edgeLength_scanline : OracleCase where
  name := "oracleF_edgeLength_scanline"
  strategy := .edgeLength
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 5.666666666666666, 30, 30⟩, margin := ⟨0, 4, 0, 0⟩, ports := #[(.east, ⟨30, 7.333333333333334⟩), (.east, ⟨30, 18.666666666666668⟩)] }],
      #[{ box := ⟨58, 0, 30, 30⟩, margin := ⟨0, 0, 0, 4⟩, ports := #[(.west, ⟨-4, 13⟩)] },
        { box := ⟨58, 50, 30, 30⟩, ports := #[(.west, ⟨-0.0, 15⟩)] }]]
  edges := #[(0, 2, #[], #[]),
    (1, 3, #[⟨44, 26.333333333333336⟩, ⟨44, 65⟩], #[])]
  nodePositions := #[⟨0, 5.666666666666666⟩, ⟨58, 0⟩, ⟨54, 50⟩]
  bendPoints := #[#[], #[⟨44, 26.333333333333336⟩, ⟨44, 65⟩]]
  labelPositions := #[#[], #[]]
  portX := #[30, 30, -4, -0.0]
  size := ⟨88, 80⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleF_leftRightConnectionLocking_scanline`. -/
def oracleF_leftRightConnectionLocking_scanline : OracleCase where
  name := "oracleF_leftRightConnectionLocking_scanline"
  strategy := .leftRightConnectionLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 5.666666666666666, 30, 30⟩, margin := ⟨0, 4, 0, 0⟩, ports := #[(.east, ⟨30, 7.333333333333334⟩), (.east, ⟨30, 18.666666666666668⟩)] }],
      #[{ box := ⟨58, 0, 30, 30⟩, margin := ⟨0, 0, 0, 4⟩, ports := #[(.west, ⟨-4, 13⟩)] },
        { box := ⟨58, 50, 30, 30⟩, ports := #[(.west, ⟨-0.0, 15⟩)] }]]
  edges := #[(0, 2, #[], #[]),
    (1, 3, #[⟨44, 26.333333333333336⟩, ⟨44, 65⟩], #[])]
  nodePositions := #[⟨0, 5.666666666666666⟩, ⟨58, 0⟩, ⟨54, 50⟩]
  bendPoints := #[#[], #[⟨44, 26.333333333333336⟩, ⟨44, 65⟩]]
  labelPositions := #[#[], #[]]
  portX := #[30, 30, -4, -0.0]
  size := ⟨88, 80⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleF_leftRightConstraintLocking_quadratic`. -/
def oracleF_leftRightConstraintLocking_quadratic : OracleCase where
  name := "oracleF_leftRightConstraintLocking_quadratic"
  strategy := .leftRightConstraintLocking
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 5.666666666666666, 30, 30⟩, margin := ⟨0, 4, 0, 0⟩, ports := #[(.east, ⟨30, 7.333333333333334⟩), (.east, ⟨30, 18.666666666666668⟩)] }],
      #[{ box := ⟨58, 0, 30, 30⟩, margin := ⟨0, 0, 0, 4⟩, ports := #[(.west, ⟨-4, 13⟩)] },
        { box := ⟨58, 50, 30, 30⟩, ports := #[(.west, ⟨-0.0, 15⟩)] }]]
  edges := #[(0, 2, #[], #[]),
    (1, 3, #[⟨44, 26.333333333333336⟩, ⟨44, 65⟩], #[])]
  nodePositions := #[⟨0, 5.666666666666666⟩, ⟨58, 0⟩, ⟨54, 50⟩]
  bendPoints := #[#[], #[⟨44, 26.333333333333336⟩, ⟨44, 65⟩]]
  labelPositions := #[#[], #[]]
  portX := #[30, 30, -4, -0.0]
  size := ⟨88, 80⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleF_left_scanline`. -/
def oracleF_left_scanline : OracleCase where
  name := "oracleF_left_scanline"
  strategy := .left
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 5.666666666666666, 30, 30⟩, margin := ⟨0, 4, 0, 0⟩, ports := #[(.east, ⟨30, 7.333333333333334⟩), (.east, ⟨30, 18.666666666666668⟩)] }],
      #[{ box := ⟨58, 0, 30, 30⟩, margin := ⟨0, 0, 0, 4⟩, ports := #[(.west, ⟨-4, 13⟩)] },
        { box := ⟨58, 50, 30, 30⟩, ports := #[(.west, ⟨-0.0, 15⟩)] }]]
  edges := #[(0, 2, #[], #[]),
    (1, 3, #[⟨44, 26.333333333333336⟩, ⟨44, 65⟩], #[])]
  nodePositions := #[⟨0, 5.666666666666666⟩, ⟨58, 0⟩, ⟨54, 50⟩]
  bendPoints := #[#[], #[⟨44, 26.333333333333336⟩, ⟨44, 65⟩]]
  labelPositions := #[#[], #[]]
  portX := #[30, 30, -4, -0.0]
  size := ⟨88, 80⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleF_right_scanline`. -/
def oracleF_right_scanline : OracleCase where
  name := "oracleF_right_scanline"
  strategy := .right
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 5.666666666666666, 30, 30⟩, margin := ⟨0, 4, 0, 0⟩, ports := #[(.east, ⟨30, 7.333333333333334⟩), (.east, ⟨30, 18.666666666666668⟩)] }],
      #[{ box := ⟨58, 0, 30, 30⟩, margin := ⟨0, 0, 0, 4⟩, ports := #[(.west, ⟨-4, 13⟩)] },
        { box := ⟨58, 50, 30, 30⟩, ports := #[(.west, ⟨-0.0, 15⟩)] }]]
  edges := #[(0, 2, #[], #[]),
    (1, 3, #[⟨44, 26.333333333333336⟩, ⟨44, 65⟩], #[])]
  nodePositions := #[⟨0, 5.666666666666666⟩, ⟨58, 0⟩, ⟨58, 50⟩]
  bendPoints := #[#[], #[⟨44, 26.333333333333336⟩, ⟨44, 65⟩]]
  labelPositions := #[#[], #[]]
  portX := #[30, 30, -4, -0.0]
  size := ⟨88, 80⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleG_edgeLength_scanline`. -/
def oracleG_edgeLength_scanline : OracleCase where
  name := "oracleG_edgeLength_scanline"
  strategy := .edgeLength
  constraints := .scanline
  layers := #[
      #[{ box := ⟨10, -89.33333333333333, 30, 30⟩, ports := #[(.east, ⟨30, 7.5⟩), (.east, ⟨30, 15⟩), (.east, ⟨30, 22.5⟩)] },
        { box := ⟨0, 11.666666666666668, 40, 20⟩, ports := #[(.east, ⟨40, 6.666666666666666⟩), (.east, ⟨40, 13.333333333333332⟩)] }],
      #[{ box := ⟨80, -144.33333333333331, 20, 60⟩, ports := #[(.east, ⟨20, 20⟩), (.east, ⟨20, 40⟩), (.west, ⟨-0.0, 30⟩)] },
        { box := ⟨70, -63.33333333333333, 30, 40⟩, ports := #[(.east, ⟨30, 13.333333333333334⟩), (.east, ⟨30, 26.666666666666668⟩), (.west, ⟨-0.0, 26.666666666666668⟩), (.west, ⟨-0.0, 13.333333333333334⟩)] },
        { box := ⟨60, 10, 50, 30⟩, ports := #[(.east, ⟨50, 10⟩), (.east, ⟨50, 20⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨143.33333333333334, -114.33333333333331, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨150, -43.33333333333333, 20, 20⟩, ports := #[(.east, ⟨20, 6.666666666666666⟩), (.east, ⟨20, 13.333333333333332⟩), (.west, ⟨-0.0, 13.333333333333332⟩), (.west, ⟨-0.0, 6.666666666666666⟩)] },
        { box := ⟨140, 3.333333333333332, 40, 40⟩, ports := #[(.east, ⟨40, 20⟩), (.west, ⟨-0.0, 26.666666666666668⟩), (.west, ⟨-0.0, 13.333333333333334⟩)] }],
      #[{ box := ⟨200, -70, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 33.333333333333336⟩), (.west, ⟨-0.0, 16.666666666666668⟩)] },
        { box := ⟨202.5, 0, 25, 35⟩, ports := #[(.east, ⟨25, 11.666666666666666⟩), (.east, ⟨25, 23.333333333333332⟩), (.west, ⟨-0.0, 23.333333333333332⟩), (.west, ⟨-0.0, 11.666666666666666⟩)] }],
      #[{ box := ⟨260, -133.66666666666666, 45, 25⟩, ports := #[(.west, ⟨-0.0, 16.666666666666668⟩), (.west, ⟨-0.0, 8.333333333333334⟩)] },
        { box := ⟨260, 3.333333333333332, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 7, #[⟨50, -81.83333333333333⟩, ⟨50, -114.33333333333331⟩], #[]),
    (1, 24, #[⟨130, -74.33333333333333⟩, ⟨130, 16.666666666666664⟩], #[]),
    (2, 11, #[⟨50, -66.83333333333333⟩, ⟨50, -49.99999999999999⟩], #[]),
    (3, 10, #[⟨50, 18.333333333333336⟩, ⟨50, -36.66666666666666⟩], #[]),
    (4, 14, #[], #[]),
    (5, 33, #[⟨120, -124.33333333333331⟩, ⟨120, -125.33333333333333⟩], #[]),
    (6, 17, #[], #[]),
    (8, 16, #[⟨120, -49.99999999999999⟩, ⟨120, -94.33333333333331⟩], #[]),
    (9, 21, #[], #[]),
    (12, 20, #[⟨120, 20⟩, ⟨120, -29.999999999999996⟩], #[]),
    (13, 23, #[], #[]),
    (15, 27, #[⟨190, -99.33333333333331⟩, ⟨190, -53.33333333333333⟩], #[]),
    (18, 26, #[], #[]),
    (19, 31, #[⟨190, -29.999999999999996⟩, ⟨190, 11.666666666666666⟩], #[]),
    (22, 30, #[], #[]),
    (25, 35, #[⟨250, -45⟩, ⟨250, 13.333333333333332⟩], #[]),
    (28, 32, #[⟨240, 11.666666666666666⟩, ⟨240, -116.99999999999999⟩], #[]),
    (29, 34, #[], #[])]
  nodePositions := #[⟨31, -89.33333333333333⟩, ⟨1, 11.666666666666668⟩, ⟨91, -144.33333333333331⟩, ⟨81, -63.33333333333333⟩, ⟨61, 10⟩, ⟨131, -114.33333333333331⟩, ⟨141, -43.33333333333333⟩, ⟨141, 3.333333333333332⟩, ⟨201, -70⟩, ⟨201, 0⟩, ⟨251, -133.66666666666666⟩, ⟨261, 3.333333333333332⟩]
  bendPoints := #[#[⟨81, -81.83333333333333⟩, ⟨81, -114.33333333333331⟩], #[⟨131, -74.33333333333333⟩, ⟨131, 16.666666666666664⟩], #[⟨71, -66.83333333333333⟩, ⟨71, -49.99999999999999⟩], #[⟨51, 18.333333333333336⟩, ⟨51, -36.66666666666666⟩], #[], #[⟨121, -124.33333333333331⟩, ⟨121, -125.33333333333333⟩], #[], #[⟨121, -49.99999999999999⟩, ⟨121, -94.33333333333331⟩], #[], #[⟨121, 20⟩, ⟨121, -29.999999999999996⟩], #[], #[⟨171, -99.33333333333331⟩, ⟨171, -53.33333333333333⟩], #[], #[⟨191, -29.999999999999996⟩, ⟨191, 11.666666666666666⟩], #[], #[⟨251, -45⟩, ⟨251, 13.333333333333332⟩], #[⟨241, 11.666666666666666⟩, ⟨241, -116.99999999999999⟩], #[]]
  labelPositions := #[#[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[]]
  portX := #[30, 30, 30, 40, 40, 20, 20, -0.0, 30, 30, -0.0, -0.0, 50, 50, -0.0, 30, -0.0, -0.0, 20, 20, -0.0, -0.0, 40, -0.0, -0.0, 30, -0.0, -0.0, 25, 25, -0.0, -0.0, -0.0, -0.0, -0.0, -0.0]
  size := ⟨295, 187.66666666666663⟩
  offset := ⟨-1, 144.33333333333331⟩

/-- Oracle case `oracleG_leftRightConnectionLocking_scanline`. -/
def oracleG_leftRightConnectionLocking_scanline : OracleCase where
  name := "oracleG_leftRightConnectionLocking_scanline"
  strategy := .leftRightConnectionLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨10, -89.33333333333333, 30, 30⟩, ports := #[(.east, ⟨30, 7.5⟩), (.east, ⟨30, 15⟩), (.east, ⟨30, 22.5⟩)] },
        { box := ⟨0, 11.666666666666668, 40, 20⟩, ports := #[(.east, ⟨40, 6.666666666666666⟩), (.east, ⟨40, 13.333333333333332⟩)] }],
      #[{ box := ⟨80, -144.33333333333331, 20, 60⟩, ports := #[(.east, ⟨20, 20⟩), (.east, ⟨20, 40⟩), (.west, ⟨-0.0, 30⟩)] },
        { box := ⟨70, -63.33333333333333, 30, 40⟩, ports := #[(.east, ⟨30, 13.333333333333334⟩), (.east, ⟨30, 26.666666666666668⟩), (.west, ⟨-0.0, 26.666666666666668⟩), (.west, ⟨-0.0, 13.333333333333334⟩)] },
        { box := ⟨60, 10, 50, 30⟩, ports := #[(.east, ⟨50, 10⟩), (.east, ⟨50, 20⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨143.33333333333334, -114.33333333333331, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨150, -43.33333333333333, 20, 20⟩, ports := #[(.east, ⟨20, 6.666666666666666⟩), (.east, ⟨20, 13.333333333333332⟩), (.west, ⟨-0.0, 13.333333333333332⟩), (.west, ⟨-0.0, 6.666666666666666⟩)] },
        { box := ⟨140, 3.333333333333332, 40, 40⟩, ports := #[(.east, ⟨40, 20⟩), (.west, ⟨-0.0, 26.666666666666668⟩), (.west, ⟨-0.0, 13.333333333333334⟩)] }],
      #[{ box := ⟨200, -70, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 33.333333333333336⟩), (.west, ⟨-0.0, 16.666666666666668⟩)] },
        { box := ⟨202.5, 0, 25, 35⟩, ports := #[(.east, ⟨25, 11.666666666666666⟩), (.east, ⟨25, 23.333333333333332⟩), (.west, ⟨-0.0, 23.333333333333332⟩), (.west, ⟨-0.0, 11.666666666666666⟩)] }],
      #[{ box := ⟨260, -133.66666666666666, 45, 25⟩, ports := #[(.west, ⟨-0.0, 16.666666666666668⟩), (.west, ⟨-0.0, 8.333333333333334⟩)] },
        { box := ⟨260, 3.333333333333332, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 7, #[⟨50, -81.83333333333333⟩, ⟨50, -114.33333333333331⟩], #[]),
    (1, 24, #[⟨130, -74.33333333333333⟩, ⟨130, 16.666666666666664⟩], #[]),
    (2, 11, #[⟨50, -66.83333333333333⟩, ⟨50, -49.99999999999999⟩], #[]),
    (3, 10, #[⟨50, 18.333333333333336⟩, ⟨50, -36.66666666666666⟩], #[]),
    (4, 14, #[], #[]),
    (5, 33, #[⟨120, -124.33333333333331⟩, ⟨120, -125.33333333333333⟩], #[]),
    (6, 17, #[], #[]),
    (8, 16, #[⟨120, -49.99999999999999⟩, ⟨120, -94.33333333333331⟩], #[]),
    (9, 21, #[], #[]),
    (12, 20, #[⟨120, 20⟩, ⟨120, -29.999999999999996⟩], #[]),
    (13, 23, #[], #[]),
    (15, 27, #[⟨190, -99.33333333333331⟩, ⟨190, -53.33333333333333⟩], #[]),
    (18, 26, #[], #[]),
    (19, 31, #[⟨190, -29.999999999999996⟩, ⟨190, 11.666666666666666⟩], #[]),
    (22, 30, #[], #[]),
    (25, 35, #[⟨250, -45⟩, ⟨250, 13.333333333333332⟩], #[]),
    (28, 32, #[⟨240, 11.666666666666666⟩, ⟨240, -116.99999999999999⟩], #[]),
    (29, 34, #[], #[])]
  nodePositions := #[⟨10, -89.33333333333333⟩, ⟨0, 11.666666666666668⟩, ⟨70, -144.33333333333331⟩, ⟨60, -63.33333333333333⟩, ⟨60, 10⟩, ⟨110, -114.33333333333331⟩, ⟨160, -43.33333333333333⟩, ⟨140, 3.333333333333332⟩, ⟨200, -70⟩, ⟨205, 0⟩, ⟨250, -133.66666666666666⟩, ⟨260, 3.333333333333332⟩]
  bendPoints := #[#[⟨60, -81.83333333333333⟩, ⟨60, -114.33333333333331⟩], #[⟨130, -74.33333333333333⟩, ⟨130, 16.666666666666664⟩], #[⟨50, -66.83333333333333⟩, ⟨50, -49.99999999999999⟩], #[⟨50, 18.333333333333336⟩, ⟨50, -36.66666666666666⟩], #[], #[⟨240, -124.33333333333331⟩, ⟨240, -125.33333333333333⟩], #[], #[⟨100, -49.99999999999999⟩, ⟨100, -94.33333333333331⟩], #[], #[⟨120, 20⟩, ⟨120, -29.999999999999996⟩], #[], #[⟨190, -99.33333333333331⟩, ⟨190, -53.33333333333333⟩], #[], #[⟨190, -29.999999999999996⟩, ⟨190, 11.666666666666666⟩], #[], #[⟨250, -45⟩, ⟨250, 13.333333333333332⟩], #[⟨240, 11.666666666666666⟩, ⟨240, -116.99999999999999⟩], #[]]
  labelPositions := #[#[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[]]
  portX := #[30, 30, 30, 40, 40, 20, 20, -0.0, 30, 30, -0.0, -0.0, 50, 50, -0.0, 30, -0.0, -0.0, 20, 20, -0.0, -0.0, 40, -0.0, -0.0, 30, -0.0, -0.0, 25, 25, -0.0, -0.0, -0.0, -0.0, -0.0, -0.0]
  size := ⟨295, 187.66666666666663⟩
  offset := ⟨0, 144.33333333333331⟩

/-- Oracle case `oracleG_leftRightConstraintLocking_quadratic`. -/
def oracleG_leftRightConstraintLocking_quadratic : OracleCase where
  name := "oracleG_leftRightConstraintLocking_quadratic"
  strategy := .leftRightConstraintLocking
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨10, -89.33333333333333, 30, 30⟩, ports := #[(.east, ⟨30, 7.5⟩), (.east, ⟨30, 15⟩), (.east, ⟨30, 22.5⟩)] },
        { box := ⟨0, 11.666666666666668, 40, 20⟩, ports := #[(.east, ⟨40, 6.666666666666666⟩), (.east, ⟨40, 13.333333333333332⟩)] }],
      #[{ box := ⟨80, -144.33333333333331, 20, 60⟩, ports := #[(.east, ⟨20, 20⟩), (.east, ⟨20, 40⟩), (.west, ⟨-0.0, 30⟩)] },
        { box := ⟨70, -63.33333333333333, 30, 40⟩, ports := #[(.east, ⟨30, 13.333333333333334⟩), (.east, ⟨30, 26.666666666666668⟩), (.west, ⟨-0.0, 26.666666666666668⟩), (.west, ⟨-0.0, 13.333333333333334⟩)] },
        { box := ⟨60, 10, 50, 30⟩, ports := #[(.east, ⟨50, 10⟩), (.east, ⟨50, 20⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨143.33333333333334, -114.33333333333331, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨150, -43.33333333333333, 20, 20⟩, ports := #[(.east, ⟨20, 6.666666666666666⟩), (.east, ⟨20, 13.333333333333332⟩), (.west, ⟨-0.0, 13.333333333333332⟩), (.west, ⟨-0.0, 6.666666666666666⟩)] },
        { box := ⟨140, 3.333333333333332, 40, 40⟩, ports := #[(.east, ⟨40, 20⟩), (.west, ⟨-0.0, 26.666666666666668⟩), (.west, ⟨-0.0, 13.333333333333334⟩)] }],
      #[{ box := ⟨200, -70, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 33.333333333333336⟩), (.west, ⟨-0.0, 16.666666666666668⟩)] },
        { box := ⟨202.5, 0, 25, 35⟩, ports := #[(.east, ⟨25, 11.666666666666666⟩), (.east, ⟨25, 23.333333333333332⟩), (.west, ⟨-0.0, 23.333333333333332⟩), (.west, ⟨-0.0, 11.666666666666666⟩)] }],
      #[{ box := ⟨260, -133.66666666666666, 45, 25⟩, ports := #[(.west, ⟨-0.0, 16.666666666666668⟩), (.west, ⟨-0.0, 8.333333333333334⟩)] },
        { box := ⟨260, 3.333333333333332, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 7, #[⟨50, -81.83333333333333⟩, ⟨50, -114.33333333333331⟩], #[]),
    (1, 24, #[⟨130, -74.33333333333333⟩, ⟨130, 16.666666666666664⟩], #[]),
    (2, 11, #[⟨50, -66.83333333333333⟩, ⟨50, -49.99999999999999⟩], #[]),
    (3, 10, #[⟨50, 18.333333333333336⟩, ⟨50, -36.66666666666666⟩], #[]),
    (4, 14, #[], #[]),
    (5, 33, #[⟨120, -124.33333333333331⟩, ⟨120, -125.33333333333333⟩], #[]),
    (6, 17, #[], #[]),
    (8, 16, #[⟨120, -49.99999999999999⟩, ⟨120, -94.33333333333331⟩], #[]),
    (9, 21, #[], #[]),
    (12, 20, #[⟨120, 20⟩, ⟨120, -29.999999999999996⟩], #[]),
    (13, 23, #[], #[]),
    (15, 27, #[⟨190, -99.33333333333331⟩, ⟨190, -53.33333333333333⟩], #[]),
    (18, 26, #[], #[]),
    (19, 31, #[⟨190, -29.999999999999996⟩, ⟨190, 11.666666666666666⟩], #[]),
    (22, 30, #[], #[]),
    (25, 35, #[⟨250, -45⟩, ⟨250, 13.333333333333332⟩], #[]),
    (28, 32, #[⟨240, 11.666666666666666⟩, ⟨240, -116.99999999999999⟩], #[]),
    (29, 34, #[], #[])]
  nodePositions := #[⟨30, -89.33333333333333⟩, ⟨0, 11.666666666666668⟩, ⟨90, -144.33333333333331⟩, ⟨80, -63.33333333333333⟩, ⟨60, 10⟩, ⟨150, -114.33333333333331⟩, ⟨160, -43.33333333333333⟩, ⟨140, 3.333333333333332⟩, ⟨200, -70⟩, ⟨205, 0⟩, ⟨250, -133.66666666666666⟩, ⟨260, 3.333333333333332⟩]
  bendPoints := #[#[⟨80, -81.83333333333333⟩, ⟨80, -114.33333333333331⟩], #[⟨130, -74.33333333333333⟩, ⟨130, 16.666666666666664⟩], #[⟨70, -66.83333333333333⟩, ⟨70, -49.99999999999999⟩], #[⟨50, 18.333333333333336⟩, ⟨50, -36.66666666666666⟩], #[], #[⟨230, -124.33333333333331⟩, ⟨230, -125.33333333333333⟩], #[], #[⟨120, -49.99999999999999⟩, ⟨120, -94.33333333333331⟩], #[], #[⟨120, 20⟩, ⟨120, -29.999999999999996⟩], #[], #[⟨190, -99.33333333333331⟩, ⟨190, -53.33333333333333⟩], #[], #[⟨190, -29.999999999999996⟩, ⟨190, 11.666666666666666⟩], #[], #[⟨250, -45⟩, ⟨250, 13.333333333333332⟩], #[⟨240, 11.666666666666666⟩, ⟨240, -116.99999999999999⟩], #[]]
  labelPositions := #[#[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[]]
  portX := #[30, 30, 30, 40, 40, 20, 20, -0.0, 30, 30, -0.0, -0.0, 50, 50, -0.0, 30, -0.0, -0.0, 20, 20, -0.0, -0.0, 40, -0.0, -0.0, 30, -0.0, -0.0, 25, 25, -0.0, -0.0, -0.0, -0.0, -0.0, -0.0]
  size := ⟨295, 187.66666666666663⟩
  offset := ⟨0, 144.33333333333331⟩

/-- Oracle case `oracleG_left_scanline`. -/
def oracleG_left_scanline : OracleCase where
  name := "oracleG_left_scanline"
  strategy := .left
  constraints := .scanline
  layers := #[
      #[{ box := ⟨10, -89.33333333333333, 30, 30⟩, ports := #[(.east, ⟨30, 7.5⟩), (.east, ⟨30, 15⟩), (.east, ⟨30, 22.5⟩)] },
        { box := ⟨0, 11.666666666666668, 40, 20⟩, ports := #[(.east, ⟨40, 6.666666666666666⟩), (.east, ⟨40, 13.333333333333332⟩)] }],
      #[{ box := ⟨80, -144.33333333333331, 20, 60⟩, ports := #[(.east, ⟨20, 20⟩), (.east, ⟨20, 40⟩), (.west, ⟨-0.0, 30⟩)] },
        { box := ⟨70, -63.33333333333333, 30, 40⟩, ports := #[(.east, ⟨30, 13.333333333333334⟩), (.east, ⟨30, 26.666666666666668⟩), (.west, ⟨-0.0, 26.666666666666668⟩), (.west, ⟨-0.0, 13.333333333333334⟩)] },
        { box := ⟨60, 10, 50, 30⟩, ports := #[(.east, ⟨50, 10⟩), (.east, ⟨50, 20⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨143.33333333333334, -114.33333333333331, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨150, -43.33333333333333, 20, 20⟩, ports := #[(.east, ⟨20, 6.666666666666666⟩), (.east, ⟨20, 13.333333333333332⟩), (.west, ⟨-0.0, 13.333333333333332⟩), (.west, ⟨-0.0, 6.666666666666666⟩)] },
        { box := ⟨140, 3.333333333333332, 40, 40⟩, ports := #[(.east, ⟨40, 20⟩), (.west, ⟨-0.0, 26.666666666666668⟩), (.west, ⟨-0.0, 13.333333333333334⟩)] }],
      #[{ box := ⟨200, -70, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 33.333333333333336⟩), (.west, ⟨-0.0, 16.666666666666668⟩)] },
        { box := ⟨202.5, 0, 25, 35⟩, ports := #[(.east, ⟨25, 11.666666666666666⟩), (.east, ⟨25, 23.333333333333332⟩), (.west, ⟨-0.0, 23.333333333333332⟩), (.west, ⟨-0.0, 11.666666666666666⟩)] }],
      #[{ box := ⟨260, -133.66666666666666, 45, 25⟩, ports := #[(.west, ⟨-0.0, 16.666666666666668⟩), (.west, ⟨-0.0, 8.333333333333334⟩)] },
        { box := ⟨260, 3.333333333333332, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 7, #[⟨50, -81.83333333333333⟩, ⟨50, -114.33333333333331⟩], #[]),
    (1, 24, #[⟨130, -74.33333333333333⟩, ⟨130, 16.666666666666664⟩], #[]),
    (2, 11, #[⟨50, -66.83333333333333⟩, ⟨50, -49.99999999999999⟩], #[]),
    (3, 10, #[⟨50, 18.333333333333336⟩, ⟨50, -36.66666666666666⟩], #[]),
    (4, 14, #[], #[]),
    (5, 33, #[⟨120, -124.33333333333331⟩, ⟨120, -125.33333333333333⟩], #[]),
    (6, 17, #[], #[]),
    (8, 16, #[⟨120, -49.99999999999999⟩, ⟨120, -94.33333333333331⟩], #[]),
    (9, 21, #[], #[]),
    (12, 20, #[⟨120, 20⟩, ⟨120, -29.999999999999996⟩], #[]),
    (13, 23, #[], #[]),
    (15, 27, #[⟨190, -99.33333333333331⟩, ⟨190, -53.33333333333333⟩], #[]),
    (18, 26, #[], #[]),
    (19, 31, #[⟨190, -29.999999999999996⟩, ⟨190, 11.666666666666666⟩], #[]),
    (22, 30, #[], #[]),
    (25, 35, #[⟨250, -45⟩, ⟨250, 13.333333333333332⟩], #[]),
    (28, 32, #[⟨240, 11.666666666666666⟩, ⟨240, -116.99999999999999⟩], #[]),
    (29, 34, #[], #[])]
  nodePositions := #[⟨0, -89.33333333333333⟩, ⟨0, 11.666666666666668⟩, ⟨50, -144.33333333333331⟩, ⟨60, -63.33333333333333⟩, ⟨60, 10⟩, ⟨110, -114.33333333333331⟩, ⟨140, -43.33333333333333⟩, ⟨140, 3.333333333333332⟩, ⟨200, -70⟩, ⟨200, 0⟩, ⟨250, -133.66666666666666⟩, ⟨260, 3.333333333333332⟩]
  bendPoints := #[#[⟨40, -81.83333333333333⟩, ⟨40, -114.33333333333331⟩], #[⟨130, -74.33333333333333⟩, ⟨130, 16.666666666666664⟩], #[⟨40, -66.83333333333333⟩, ⟨40, -49.99999999999999⟩], #[⟨50, 18.333333333333336⟩, ⟨50, -36.66666666666666⟩], #[], #[⟨80, -124.33333333333331⟩, ⟨80, -125.33333333333333⟩], #[], #[⟨100, -49.99999999999999⟩, ⟨100, -94.33333333333331⟩], #[], #[⟨120, 20⟩, ⟨120, -29.999999999999996⟩], #[], #[⟨150, -99.33333333333331⟩, ⟨150, -53.33333333333333⟩], #[], #[⟨190, -29.999999999999996⟩, ⟨190, 11.666666666666666⟩], #[], #[⟨250, -45⟩, ⟨250, 13.333333333333332⟩], #[⟨240, 11.666666666666666⟩, ⟨240, -116.99999999999999⟩], #[]]
  labelPositions := #[#[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[]]
  portX := #[30, 30, 30, 40, 40, 20, 20, -0.0, 30, 30, -0.0, -0.0, 50, 50, -0.0, 30, -0.0, -0.0, 20, 20, -0.0, -0.0, 40, -0.0, -0.0, 30, -0.0, -0.0, 25, 25, -0.0, -0.0, -0.0, -0.0, -0.0, -0.0]
  size := ⟨295, 187.66666666666663⟩
  offset := ⟨0, 144.33333333333331⟩

/-- Oracle case `oracleG_right_scanline`. -/
def oracleG_right_scanline : OracleCase where
  name := "oracleG_right_scanline"
  strategy := .right
  constraints := .scanline
  layers := #[
      #[{ box := ⟨10, -89.33333333333333, 30, 30⟩, ports := #[(.east, ⟨30, 7.5⟩), (.east, ⟨30, 15⟩), (.east, ⟨30, 22.5⟩)] },
        { box := ⟨0, 11.666666666666668, 40, 20⟩, ports := #[(.east, ⟨40, 6.666666666666666⟩), (.east, ⟨40, 13.333333333333332⟩)] }],
      #[{ box := ⟨80, -144.33333333333331, 20, 60⟩, ports := #[(.east, ⟨20, 20⟩), (.east, ⟨20, 40⟩), (.west, ⟨-0.0, 30⟩)] },
        { box := ⟨70, -63.33333333333333, 30, 40⟩, ports := #[(.east, ⟨30, 13.333333333333334⟩), (.east, ⟨30, 26.666666666666668⟩), (.west, ⟨-0.0, 26.666666666666668⟩), (.west, ⟨-0.0, 13.333333333333334⟩)] },
        { box := ⟨60, 10, 50, 30⟩, ports := #[(.east, ⟨50, 10⟩), (.east, ⟨50, 20⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨143.33333333333334, -114.33333333333331, 30, 30⟩, ports := #[(.east, ⟨30, 15⟩), (.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨150, -43.33333333333333, 20, 20⟩, ports := #[(.east, ⟨20, 6.666666666666666⟩), (.east, ⟨20, 13.333333333333332⟩), (.west, ⟨-0.0, 13.333333333333332⟩), (.west, ⟨-0.0, 6.666666666666666⟩)] },
        { box := ⟨140, 3.333333333333332, 40, 40⟩, ports := #[(.east, ⟨40, 20⟩), (.west, ⟨-0.0, 26.666666666666668⟩), (.west, ⟨-0.0, 13.333333333333334⟩)] }],
      #[{ box := ⟨200, -70, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 33.333333333333336⟩), (.west, ⟨-0.0, 16.666666666666668⟩)] },
        { box := ⟨202.5, 0, 25, 35⟩, ports := #[(.east, ⟨25, 11.666666666666666⟩), (.east, ⟨25, 23.333333333333332⟩), (.west, ⟨-0.0, 23.333333333333332⟩), (.west, ⟨-0.0, 11.666666666666666⟩)] }],
      #[{ box := ⟨260, -133.66666666666666, 45, 25⟩, ports := #[(.west, ⟨-0.0, 16.666666666666668⟩), (.west, ⟨-0.0, 8.333333333333334⟩)] },
        { box := ⟨260, 3.333333333333332, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 7, #[⟨50, -81.83333333333333⟩, ⟨50, -114.33333333333331⟩], #[]),
    (1, 24, #[⟨130, -74.33333333333333⟩, ⟨130, 16.666666666666664⟩], #[]),
    (2, 11, #[⟨50, -66.83333333333333⟩, ⟨50, -49.99999999999999⟩], #[]),
    (3, 10, #[⟨50, 18.333333333333336⟩, ⟨50, -36.66666666666666⟩], #[]),
    (4, 14, #[], #[]),
    (5, 33, #[⟨120, -124.33333333333331⟩, ⟨120, -125.33333333333333⟩], #[]),
    (6, 17, #[], #[]),
    (8, 16, #[⟨120, -49.99999999999999⟩, ⟨120, -94.33333333333331⟩], #[]),
    (9, 21, #[], #[]),
    (12, 20, #[⟨120, 20⟩, ⟨120, -29.999999999999996⟩], #[]),
    (13, 23, #[], #[]),
    (15, 27, #[⟨190, -99.33333333333331⟩, ⟨190, -53.33333333333333⟩], #[]),
    (18, 26, #[], #[]),
    (19, 31, #[⟨190, -29.999999999999996⟩, ⟨190, 11.666666666666666⟩], #[]),
    (22, 30, #[], #[]),
    (25, 35, #[⟨250, -45⟩, ⟨250, 13.333333333333332⟩], #[]),
    (28, 32, #[⟨240, 11.666666666666666⟩, ⟨240, -116.99999999999999⟩], #[]),
    (29, 34, #[], #[])]
  nodePositions := #[⟨40, -89.33333333333333⟩, ⟨10, 11.666666666666668⟩, ⟨100, -144.33333333333331⟩, ⟨90, -63.33333333333333⟩, ⟨70, 10⟩, ⟨160, -114.33333333333331⟩, ⟨170, -43.33333333333333⟩, ⟨150, 3.333333333333332⟩, ⟨210, -70⟩, ⟨215, 0⟩, ⟨260, -133.66666666666666⟩, ⟨275, 3.333333333333332⟩]
  bendPoints := #[#[⟨90, -81.83333333333333⟩, ⟨90, -114.33333333333331⟩], #[⟨140, -74.33333333333333⟩, ⟨140, 16.666666666666664⟩], #[⟨80, -66.83333333333333⟩, ⟨80, -49.99999999999999⟩], #[⟨60, 18.333333333333336⟩, ⟨60, -36.66666666666666⟩], #[], #[⟨250, -124.33333333333331⟩, ⟨250, -125.33333333333333⟩], #[], #[⟨130, -49.99999999999999⟩, ⟨130, -94.33333333333331⟩], #[], #[⟨130, 20⟩, ⟨130, -29.999999999999996⟩], #[], #[⟨200, -99.33333333333331⟩, ⟨200, -53.33333333333333⟩], #[], #[⟨200, -29.999999999999996⟩, ⟨200, 11.666666666666666⟩], #[], #[⟨265, -45⟩, ⟨265, 13.333333333333332⟩], #[⟨250, 11.666666666666666⟩, ⟨250, -116.99999999999999⟩], #[]]
  labelPositions := #[#[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[], #[]]
  portX := #[30, 30, 30, 40, 40, 20, 20, -0.0, 30, 30, -0.0, -0.0, 50, 50, -0.0, 30, -0.0, -0.0, 20, 20, -0.0, -0.0, 40, -0.0, -0.0, 30, -0.0, -0.0, 25, 25, -0.0, -0.0, -0.0, -0.0, -0.0, -0.0]
  size := ⟨295, 187.66666666666663⟩
  offset := ⟨-10, 144.33333333333331⟩

/-- Oracle case `oracleH_edgeLength_scanline`. -/
def oracleH_edgeLength_scanline : OracleCase where
  name := "oracleH_edgeLength_scanline"
  strategy := .edgeLength
  constraints := .scanline
  layers := #[
      #[{ box := ⟨-12, 68, 0, 4⟩, type := .externalPort, extPortSide := .west, ports := #[(.east, ⟨0, 2⟩)] }],
      #[{ box := ⟨0, 55, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨50, 0, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨50, 50, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] }],
      #[{ box := ⟨92, 73, 0, 4⟩, type := .externalPort, extPortSide := .east, ports := #[(.west, ⟨0, 2⟩)] },
        { box := ⟨13, -12, 4, 0⟩, type := .externalPort, extPortSide := .north, ports := #[(.south, ⟨2, 0⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨40, 65⟩, ⟨40, 20⟩], #[]),
    (2, 7, #[], #[]),
    (6, 8, #[], #[]),
    (9, 5, #[⟨15, 10⟩], #[])]
  nodePositions := #[⟨1, 68⟩, ⟨1, 55⟩, ⟨51, 0⟩, ⟨51, 50⟩, ⟨81, 73⟩, ⟨39, -12⟩]
  bendPoints := #[#[], #[⟨41, 65⟩, ⟨41, 20⟩], #[], #[], #[⟨41, 10⟩]]
  labelPositions := #[#[], #[], #[], #[], #[]]
  portX := #[0, 30, 30, -0.0, -0.0, -0.0, 30, -0.0, 0, 2]
  size := ⟨80, 112⟩
  offset := ⟨-1, 12⟩

/-- Oracle case `oracleH_leftRightConnectionLocking_scanline`. -/
def oracleH_leftRightConnectionLocking_scanline : OracleCase where
  name := "oracleH_leftRightConnectionLocking_scanline"
  strategy := .leftRightConnectionLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨-12, 68, 0, 4⟩, type := .externalPort, extPortSide := .west, ports := #[(.east, ⟨0, 2⟩)] }],
      #[{ box := ⟨0, 55, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨50, 0, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨50, 50, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] }],
      #[{ box := ⟨92, 73, 0, 4⟩, type := .externalPort, extPortSide := .east, ports := #[(.west, ⟨0, 2⟩)] },
        { box := ⟨13, -12, 4, 0⟩, type := .externalPort, extPortSide := .north, ports := #[(.south, ⟨2, 0⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨40, 65⟩, ⟨40, 20⟩], #[]),
    (2, 7, #[], #[]),
    (6, 8, #[], #[]),
    (9, 5, #[⟨15, 10⟩], #[])]
  nodePositions := #[⟨-12, 68⟩, ⟨-12, 55⟩, ⟨38, 0⟩, ⟨38, 50⟩, ⟨68, 73⟩, ⟨26, -12⟩]
  bendPoints := #[#[], #[⟨28, 65⟩, ⟨28, 20⟩], #[], #[], #[⟨28, 10⟩]]
  labelPositions := #[#[], #[], #[], #[], #[]]
  portX := #[0, 30, 30, -0.0, -0.0, -0.0, 30, -0.0, 0, 2]
  size := ⟨80, 112⟩
  offset := ⟨12, 12⟩

/-- Oracle case `oracleH_leftRightConstraintLocking_quadratic`. -/
def oracleH_leftRightConstraintLocking_quadratic : OracleCase where
  name := "oracleH_leftRightConstraintLocking_quadratic"
  strategy := .leftRightConstraintLocking
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨-12, 68, 0, 4⟩, type := .externalPort, extPortSide := .west, ports := #[(.east, ⟨0, 2⟩)] }],
      #[{ box := ⟨0, 55, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨50, 0, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨50, 50, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] }],
      #[{ box := ⟨92, 73, 0, 4⟩, type := .externalPort, extPortSide := .east, ports := #[(.west, ⟨0, 2⟩)] },
        { box := ⟨13, -12, 4, 0⟩, type := .externalPort, extPortSide := .north, ports := #[(.south, ⟨2, 0⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨40, 65⟩, ⟨40, 20⟩], #[]),
    (2, 7, #[], #[]),
    (6, 8, #[], #[]),
    (9, 5, #[⟨15, 10⟩], #[])]
  nodePositions := #[⟨-12, 68⟩, ⟨-12, 55⟩, ⟨38, 0⟩, ⟨38, 50⟩, ⟨68, 73⟩, ⟨26, -12⟩]
  bendPoints := #[#[], #[⟨28, 65⟩, ⟨28, 20⟩], #[], #[], #[⟨28, 10⟩]]
  labelPositions := #[#[], #[], #[], #[], #[]]
  portX := #[0, 30, 30, -0.0, -0.0, -0.0, 30, -0.0, 0, 2]
  size := ⟨80, 112⟩
  offset := ⟨12, 12⟩

/-- Oracle case `oracleH_left_scanline`. -/
def oracleH_left_scanline : OracleCase where
  name := "oracleH_left_scanline"
  strategy := .left
  constraints := .scanline
  layers := #[
      #[{ box := ⟨-12, 68, 0, 4⟩, type := .externalPort, extPortSide := .west, ports := #[(.east, ⟨0, 2⟩)] }],
      #[{ box := ⟨0, 55, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨50, 0, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨50, 50, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] }],
      #[{ box := ⟨92, 73, 0, 4⟩, type := .externalPort, extPortSide := .east, ports := #[(.west, ⟨0, 2⟩)] },
        { box := ⟨13, -12, 4, 0⟩, type := .externalPort, extPortSide := .north, ports := #[(.south, ⟨2, 0⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨40, 65⟩, ⟨40, 20⟩], #[]),
    (2, 7, #[], #[]),
    (6, 8, #[], #[]),
    (9, 5, #[⟨15, 10⟩], #[])]
  nodePositions := #[⟨-12, 68⟩, ⟨-12, 55⟩, ⟨38, 0⟩, ⟨38, 50⟩, ⟨68, 73⟩, ⟨-12, -12⟩]
  bendPoints := #[#[], #[⟨28, 65⟩, ⟨28, 20⟩], #[], #[], #[⟨-10, 10⟩]]
  labelPositions := #[#[], #[], #[], #[], #[]]
  portX := #[0, 30, 30, -0.0, -0.0, -0.0, 30, -0.0, 0, 2]
  size := ⟨80, 112⟩
  offset := ⟨12, 12⟩

/-- Oracle case `oracleH_right_scanline`. -/
def oracleH_right_scanline : OracleCase where
  name := "oracleH_right_scanline"
  strategy := .right
  constraints := .scanline
  layers := #[
      #[{ box := ⟨-12, 68, 0, 4⟩, type := .externalPort, extPortSide := .west, ports := #[(.east, ⟨0, 2⟩)] }],
      #[{ box := ⟨0, 55, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩), (.west, ⟨-0.0, 15⟩)] }],
      #[{ box := ⟨50, 0, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] },
        { box := ⟨50, 50, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] }],
      #[{ box := ⟨92, 73, 0, 4⟩, type := .externalPort, extPortSide := .east, ports := #[(.west, ⟨0, 2⟩)] },
        { box := ⟨13, -12, 4, 0⟩, type := .externalPort, extPortSide := .north, ports := #[(.south, ⟨2, 0⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨40, 65⟩, ⟨40, 20⟩], #[]),
    (2, 7, #[], #[]),
    (6, 8, #[], #[]),
    (9, 5, #[⟨15, 10⟩], #[])]
  nodePositions := #[⟨12, 68⟩, ⟨12, 55⟩, ⟨62, 0⟩, ⟨62, 50⟩, ⟨92, 73⟩, ⟨50, -12⟩]
  bendPoints := #[#[], #[⟨52, 65⟩, ⟨52, 20⟩], #[], #[], #[⟨52, 10⟩]]
  labelPositions := #[#[], #[], #[], #[], #[]]
  portX := #[0, 30, 30, -0.0, -0.0, -0.0, 30, -0.0, 0, 2]
  size := ⟨80, 112⟩
  offset := ⟨-12, 12⟩

/-- Oracle case `oracleI_edgeLength_scanline`. -/
def oracleI_edgeLength_scanline : OracleCase where
  name := "oracleI_edgeLength_scanline"
  strategy := .edgeLength
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 35, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨55, 30, 30, 30⟩, margin := ⟨30, 5, 0, 5⟩, ports := #[(.west, ⟨-0.0, 15⟩), (.west, ⟨15, 0⟩)] },
        { box := ⟨55, 80, 30, 60⟩, ports := #[(.west, ⟨-0.0, 30⟩)] },
        { box := ⟨50, 0, 40, 20⟩, comment := true, ports := #[(.east, ⟨20, 20⟩)] }]]
  edges := #[(0, 2, #[], #[]),
    (1, 4, #[⟨40, 55⟩, ⟨40, 110⟩], #[]),
    (5, 3, #[], #[])]
  nodePositions := #[⟨0, 35⟩, ⟨55, 30⟩, ⟨50, 80⟩, ⟨50, 0⟩]
  bendPoints := #[#[], #[⟨40, 55⟩, ⟨40, 110⟩], #[]]
  labelPositions := #[#[], #[], #[]]
  portX := #[30, 30, -0.0, 15, -0.0, 20]
  size := ⟨90, 140⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleI_leftRightConnectionLocking_scanline`. -/
def oracleI_leftRightConnectionLocking_scanline : OracleCase where
  name := "oracleI_leftRightConnectionLocking_scanline"
  strategy := .leftRightConnectionLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 35, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨55, 30, 30, 30⟩, margin := ⟨30, 5, 0, 5⟩, ports := #[(.west, ⟨-0.0, 15⟩), (.west, ⟨15, 0⟩)] },
        { box := ⟨55, 80, 30, 60⟩, ports := #[(.west, ⟨-0.0, 30⟩)] },
        { box := ⟨50, 0, 40, 20⟩, comment := true, ports := #[(.east, ⟨20, 20⟩)] }]]
  edges := #[(0, 2, #[], #[]),
    (1, 4, #[⟨40, 55⟩, ⟨40, 110⟩], #[]),
    (5, 3, #[], #[])]
  nodePositions := #[⟨0, 35⟩, ⟨55, 30⟩, ⟨50, 80⟩, ⟨50, 0⟩]
  bendPoints := #[#[], #[⟨40, 55⟩, ⟨40, 110⟩], #[]]
  labelPositions := #[#[], #[], #[]]
  portX := #[30, 30, -0.0, 15, -0.0, 20]
  size := ⟨90, 140⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleI_leftRightConstraintLocking_quadratic`. -/
def oracleI_leftRightConstraintLocking_quadratic : OracleCase where
  name := "oracleI_leftRightConstraintLocking_quadratic"
  strategy := .leftRightConstraintLocking
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 35, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨55, 30, 30, 30⟩, margin := ⟨30, 5, 0, 5⟩, ports := #[(.west, ⟨-0.0, 15⟩), (.west, ⟨15, 0⟩)] },
        { box := ⟨55, 80, 30, 60⟩, ports := #[(.west, ⟨-0.0, 30⟩)] },
        { box := ⟨50, 0, 40, 20⟩, comment := true, ports := #[(.east, ⟨20, 20⟩)] }]]
  edges := #[(0, 2, #[], #[]),
    (1, 4, #[⟨40, 55⟩, ⟨40, 110⟩], #[]),
    (5, 3, #[], #[])]
  nodePositions := #[⟨0, 35⟩, ⟨55, 30⟩, ⟨50, 80⟩, ⟨50, 0⟩]
  bendPoints := #[#[], #[⟨40, 55⟩, ⟨40, 110⟩], #[]]
  labelPositions := #[#[], #[], #[]]
  portX := #[30, 30, -0.0, 15, -0.0, 20]
  size := ⟨90, 140⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleI_left_scanline`. -/
def oracleI_left_scanline : OracleCase where
  name := "oracleI_left_scanline"
  strategy := .left
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 35, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨55, 30, 30, 30⟩, margin := ⟨30, 5, 0, 5⟩, ports := #[(.west, ⟨-0.0, 15⟩), (.west, ⟨15, 0⟩)] },
        { box := ⟨55, 80, 30, 60⟩, ports := #[(.west, ⟨-0.0, 30⟩)] },
        { box := ⟨50, 0, 40, 20⟩, comment := true, ports := #[(.east, ⟨20, 20⟩)] }]]
  edges := #[(0, 2, #[], #[]),
    (1, 4, #[⟨40, 55⟩, ⟨40, 110⟩], #[]),
    (5, 3, #[], #[])]
  nodePositions := #[⟨0, 35⟩, ⟨55, 30⟩, ⟨50, 80⟩, ⟨50, 0⟩]
  bendPoints := #[#[], #[⟨40, 55⟩, ⟨40, 110⟩], #[]]
  labelPositions := #[#[], #[], #[]]
  portX := #[30, 30, -0.0, 15, -0.0, 20]
  size := ⟨90, 140⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleI_right_scanline`. -/
def oracleI_right_scanline : OracleCase where
  name := "oracleI_right_scanline"
  strategy := .right
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 35, 30, 30⟩, ports := #[(.east, ⟨30, 10⟩), (.east, ⟨30, 20⟩)] }],
      #[{ box := ⟨55, 30, 30, 30⟩, margin := ⟨30, 5, 0, 5⟩, ports := #[(.west, ⟨-0.0, 15⟩), (.west, ⟨15, 0⟩)] },
        { box := ⟨55, 80, 30, 60⟩, ports := #[(.west, ⟨-0.0, 30⟩)] },
        { box := ⟨50, 0, 40, 20⟩, comment := true, ports := #[(.east, ⟨20, 20⟩)] }]]
  edges := #[(0, 2, #[], #[]),
    (1, 4, #[⟨40, 55⟩, ⟨40, 110⟩], #[]),
    (5, 3, #[], #[])]
  nodePositions := #[⟨0, 35⟩, ⟨55, 30⟩, ⟨60, 80⟩, ⟨50, 0⟩]
  bendPoints := #[#[], #[⟨40, 55⟩, ⟨40, 110⟩], #[]]
  labelPositions := #[#[], #[], #[]]
  portX := #[30, 30, -0.0, 15, -0.0, 20]
  size := ⟨90, 140⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleJ_edgeLength_quadratic`. -/
def oracleJ_edgeLength_quadratic : OracleCase where
  name := "oracleJ_edgeLength_quadratic"
  strategy := .edgeLength
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 0, 30, 30⟩, margin := ⟨0, 4, 0, 0⟩, ports := #[(.east, ⟨30, 13⟩)] }],
      #[{ box := ⟨58, 25, 30, 30⟩, margin := ⟨0, 4, 0, 4⟩, ports := #[(.east, ⟨30, 13⟩), (.west, ⟨-4, 13⟩)] }],
      #[{ box := ⟨112, 45, 30, 40⟩, ports := #[(.west, ⟨-0.0, 20⟩)] }]]
  edges := #[(0, 1, #[⟨102, 15⟩, ⟨102, 40⟩], #[]),
    (2, 3, #[⟨44, 40⟩, ⟨44, 65⟩], #[])]
  nodePositions := #[⟨1, 0⟩, ⟨59, 25⟩, ⟨113, 45⟩]
  bendPoints := #[#[⟨103, 15⟩, ⟨103, 40⟩], #[⟨45, 40⟩, ⟨45, 65⟩]]
  labelPositions := #[#[], #[]]
  portX := #[30, 30, -4, -0.0]
  size := ⟨142, 85⟩
  offset := ⟨-1, 0⟩

/-- Oracle case `oracleJ_edgeLength_scanline`. -/
def oracleJ_edgeLength_scanline : OracleCase where
  name := "oracleJ_edgeLength_scanline"
  strategy := .edgeLength
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 0, 30, 30⟩, margin := ⟨0, 4, 0, 0⟩, ports := #[(.east, ⟨30, 13⟩)] }],
      #[{ box := ⟨58, 25, 30, 30⟩, margin := ⟨0, 4, 0, 4⟩, ports := #[(.east, ⟨30, 13⟩), (.west, ⟨-4, 13⟩)] }],
      #[{ box := ⟨112, 45, 30, 40⟩, ports := #[(.west, ⟨-0.0, 20⟩)] }]]
  edges := #[(0, 1, #[⟨102, 15⟩, ⟨102, 40⟩], #[]),
    (2, 3, #[⟨44, 40⟩, ⟨44, 65⟩], #[])]
  nodePositions := #[⟨1, 0⟩, ⟨59, 25⟩, ⟨113, 45⟩]
  bendPoints := #[#[⟨103, 15⟩, ⟨103, 40⟩], #[⟨45, 40⟩, ⟨45, 65⟩]]
  labelPositions := #[#[], #[]]
  portX := #[30, 30, -4, -0.0]
  size := ⟨142, 85⟩
  offset := ⟨-1, 0⟩

/-- Oracle case `oracleJ_left_quadratic`. -/
def oracleJ_left_quadratic : OracleCase where
  name := "oracleJ_left_quadratic"
  strategy := .left
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 0, 30, 30⟩, margin := ⟨0, 4, 0, 0⟩, ports := #[(.east, ⟨30, 13⟩)] }],
      #[{ box := ⟨58, 25, 30, 30⟩, margin := ⟨0, 4, 0, 4⟩, ports := #[(.east, ⟨30, 13⟩), (.west, ⟨-4, 13⟩)] }],
      #[{ box := ⟨112, 45, 30, 40⟩, ports := #[(.west, ⟨-0.0, 20⟩)] }]]
  edges := #[(0, 1, #[⟨102, 15⟩, ⟨102, 40⟩], #[]),
    (2, 3, #[⟨44, 40⟩, ⟨44, 65⟩], #[])]
  nodePositions := #[⟨0, 0⟩, ⟨58, 25⟩, ⟨112, 45⟩]
  bendPoints := #[#[⟨102, 15⟩, ⟨102, 40⟩], #[⟨0, 40⟩, ⟨0, 65⟩]]
  labelPositions := #[#[], #[]]
  portX := #[30, 30, -4, -0.0]
  size := ⟨142, 85⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleJ_leftRightConnectionLocking_scanline`. -/
def oracleJ_leftRightConnectionLocking_scanline : OracleCase where
  name := "oracleJ_leftRightConnectionLocking_scanline"
  strategy := .leftRightConnectionLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 0, 30, 30⟩, margin := ⟨0, 4, 0, 0⟩, ports := #[(.east, ⟨30, 13⟩)] }],
      #[{ box := ⟨58, 25, 30, 30⟩, margin := ⟨0, 4, 0, 4⟩, ports := #[(.east, ⟨30, 13⟩), (.west, ⟨-4, 13⟩)] }],
      #[{ box := ⟨112, 45, 30, 40⟩, ports := #[(.west, ⟨-0.0, 20⟩)] }]]
  edges := #[(0, 1, #[⟨102, 15⟩, ⟨102, 40⟩], #[]),
    (2, 3, #[⟨44, 40⟩, ⟨44, 65⟩], #[])]
  nodePositions := #[⟨0, 0⟩, ⟨58, 25⟩, ⟨112, 45⟩]
  bendPoints := #[#[⟨142, 15⟩, ⟨142, 40⟩], #[⟨44, 40⟩, ⟨44, 65⟩]]
  labelPositions := #[#[], #[]]
  portX := #[30, 30, -4, -0.0]
  size := ⟨142, 85⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleJ_leftRightConstraintLocking_quadratic`. -/
def oracleJ_leftRightConstraintLocking_quadratic : OracleCase where
  name := "oracleJ_leftRightConstraintLocking_quadratic"
  strategy := .leftRightConstraintLocking
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 0, 30, 30⟩, margin := ⟨0, 4, 0, 0⟩, ports := #[(.east, ⟨30, 13⟩)] }],
      #[{ box := ⟨58, 25, 30, 30⟩, margin := ⟨0, 4, 0, 4⟩, ports := #[(.east, ⟨30, 13⟩), (.west, ⟨-4, 13⟩)] }],
      #[{ box := ⟨112, 45, 30, 40⟩, ports := #[(.west, ⟨-0.0, 20⟩)] }]]
  edges := #[(0, 1, #[⟨102, 15⟩, ⟨102, 40⟩], #[]),
    (2, 3, #[⟨44, 40⟩, ⟨44, 65⟩], #[])]
  nodePositions := #[⟨0, 0⟩, ⟨58, 25⟩, ⟨112, 45⟩]
  bendPoints := #[#[⟨102, 15⟩, ⟨102, 40⟩], #[⟨44, 40⟩, ⟨44, 65⟩]]
  labelPositions := #[#[], #[]]
  portX := #[30, 30, -4, -0.0]
  size := ⟨142, 85⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleJ_leftRightConstraintLocking_scanline`. -/
def oracleJ_leftRightConstraintLocking_scanline : OracleCase where
  name := "oracleJ_leftRightConstraintLocking_scanline"
  strategy := .leftRightConstraintLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 0, 30, 30⟩, margin := ⟨0, 4, 0, 0⟩, ports := #[(.east, ⟨30, 13⟩)] }],
      #[{ box := ⟨58, 25, 30, 30⟩, margin := ⟨0, 4, 0, 4⟩, ports := #[(.east, ⟨30, 13⟩), (.west, ⟨-4, 13⟩)] }],
      #[{ box := ⟨112, 45, 30, 40⟩, ports := #[(.west, ⟨-0.0, 20⟩)] }]]
  edges := #[(0, 1, #[⟨102, 15⟩, ⟨102, 40⟩], #[]),
    (2, 3, #[⟨44, 40⟩, ⟨44, 65⟩], #[])]
  nodePositions := #[⟨0, 0⟩, ⟨58, 25⟩, ⟨112, 45⟩]
  bendPoints := #[#[⟨102, 15⟩, ⟨102, 40⟩], #[⟨44, 40⟩, ⟨44, 65⟩]]
  labelPositions := #[#[], #[]]
  portX := #[30, 30, -4, -0.0]
  size := ⟨142, 85⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleJ_left_scanline`. -/
def oracleJ_left_scanline : OracleCase where
  name := "oracleJ_left_scanline"
  strategy := .left
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 0, 30, 30⟩, margin := ⟨0, 4, 0, 0⟩, ports := #[(.east, ⟨30, 13⟩)] }],
      #[{ box := ⟨58, 25, 30, 30⟩, margin := ⟨0, 4, 0, 4⟩, ports := #[(.east, ⟨30, 13⟩), (.west, ⟨-4, 13⟩)] }],
      #[{ box := ⟨112, 45, 30, 40⟩, ports := #[(.west, ⟨-0.0, 20⟩)] }]]
  edges := #[(0, 1, #[⟨102, 15⟩, ⟨102, 40⟩], #[]),
    (2, 3, #[⟨44, 40⟩, ⟨44, 65⟩], #[])]
  nodePositions := #[⟨0, 0⟩, ⟨58, 25⟩, ⟨112, 45⟩]
  bendPoints := #[#[⟨102, 15⟩, ⟨102, 40⟩], #[⟨0, 40⟩, ⟨0, 65⟩]]
  labelPositions := #[#[], #[]]
  portX := #[30, 30, -4, -0.0]
  size := ⟨142, 85⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleJ_right_scanline`. -/
def oracleJ_right_scanline : OracleCase where
  name := "oracleJ_right_scanline"
  strategy := .right
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 0, 30, 30⟩, margin := ⟨0, 4, 0, 0⟩, ports := #[(.east, ⟨30, 13⟩)] }],
      #[{ box := ⟨58, 25, 30, 30⟩, margin := ⟨0, 4, 0, 4⟩, ports := #[(.east, ⟨30, 13⟩), (.west, ⟨-4, 13⟩)] }],
      #[{ box := ⟨112, 45, 30, 40⟩, ports := #[(.west, ⟨-0.0, 20⟩)] }]]
  edges := #[(0, 1, #[⟨102, 15⟩, ⟨102, 40⟩], #[]),
    (2, 3, #[⟨44, 40⟩, ⟨44, 65⟩], #[])]
  nodePositions := #[⟨0, 0⟩, ⟨58, 25⟩, ⟨112, 45⟩]
  bendPoints := #[#[⟨142, 15⟩, ⟨142, 40⟩], #[⟨44, 40⟩, ⟨44, 65⟩]]
  labelPositions := #[#[], #[]]
  portX := #[30, 30, -4, -0.0]
  size := ⟨142, 85⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleK_edgeLength_quadratic`. -/
def oracleK_edgeLength_quadratic : OracleCase where
  name := "oracleK_edgeLength_quadratic"
  strategy := .edgeLength
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 10, 41, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨41, 13⟩), (.south, ⟨18.5, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨65, 74, 38, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨17, -4⟩), (.east, ⟨38, 15⟩)] }],
      #[{ box := ⟨123, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20.5, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨113, 89⟩, ⟨113, 35⟩], #[])]
  nodePositions := #[⟨0, 10⟩, ⟨65, 0⟩, ⟨57, 74⟩, ⟨115, 15⟩]
  bendPoints := #[#[], #[⟨20, 60⟩, ⟨76, 60⟩], #[], #[⟨105, 89⟩, ⟨105, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[41, 18, 30, -0.0, 17, 38, -0.0, -0.0]
  size := ⟨145, 104⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleK_edgeLength_scanline`. -/
def oracleK_edgeLength_scanline : OracleCase where
  name := "oracleK_edgeLength_scanline"
  strategy := .edgeLength
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 10, 41, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨41, 13⟩), (.south, ⟨18.5, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨65, 74, 38, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨17, -4⟩), (.east, ⟨38, 15⟩)] }],
      #[{ box := ⟨123, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20.5, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨113, 89⟩, ⟨113, 35⟩], #[])]
  nodePositions := #[⟨1, 10⟩, ⟨66, 0⟩, ⟨58, 74⟩, ⟨116, 15⟩]
  bendPoints := #[#[], #[⟨21, 60⟩, ⟨77, 60⟩], #[], #[⟨106, 89⟩, ⟨106, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[41, 18, 30, -0.0, 17, 38, -0.0, -0.0]
  size := ⟨145, 104⟩
  offset := ⟨-1, 0⟩

/-- Oracle case `oracleK_left_quadratic`. -/
def oracleK_left_quadratic : OracleCase where
  name := "oracleK_left_quadratic"
  strategy := .left
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 10, 41, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨41, 13⟩), (.south, ⟨18.5, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨65, 74, 38, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨17, -4⟩), (.east, ⟨38, 15⟩)] }],
      #[{ box := ⟨123, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20.5, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨113, 89⟩, ⟨113, 35⟩], #[])]
  nodePositions := #[⟨0, 10⟩, ⟨65, 0⟩, ⟨1.5, 74⟩, ⟨115, 15⟩]
  bendPoints := #[#[], #[⟨20.5, 60⟩, ⟨20.5, 60⟩], #[], #[⟨105, 89⟩, ⟨105, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[41, 18.5, 30, -0.0, 17, 38, -0.0, -0.0]
  size := ⟨145, 104⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleK_leftRightConnectionLocking_scanline`. -/
def oracleK_leftRightConnectionLocking_scanline : OracleCase where
  name := "oracleK_leftRightConnectionLocking_scanline"
  strategy := .leftRightConnectionLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 10, 41, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨41, 13⟩), (.south, ⟨18.5, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨65, 74, 38, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨17, -4⟩), (.east, ⟨38, 15⟩)] }],
      #[{ box := ⟨123, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20.5, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨113, 89⟩, ⟨113, 35⟩], #[])]
  nodePositions := #[⟨0, 10⟩, ⟨65, 0⟩, ⟨57, 74⟩, ⟨115, 15⟩]
  bendPoints := #[#[], #[⟨20.5, 60⟩, ⟨76, 60⟩], #[], #[⟨105, 89⟩, ⟨105, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[41, 18.5, 30, -0.0, 17, 38, -0.0, -0.0]
  size := ⟨145, 104⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleK_leftRightConstraintLocking_quadratic`. -/
def oracleK_leftRightConstraintLocking_quadratic : OracleCase where
  name := "oracleK_leftRightConstraintLocking_quadratic"
  strategy := .leftRightConstraintLocking
  constraints := .quadratic
  layers := #[
      #[{ box := ⟨0, 10, 41, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨41, 13⟩), (.south, ⟨18.5, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨65, 74, 38, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨17, -4⟩), (.east, ⟨38, 15⟩)] }],
      #[{ box := ⟨123, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20.5, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨113, 89⟩, ⟨113, 35⟩], #[])]
  nodePositions := #[⟨0, 10⟩, ⟨65, 0⟩, ⟨57, 74⟩, ⟨115, 15⟩]
  bendPoints := #[#[], #[⟨20.5, 60⟩, ⟨76, 60⟩], #[], #[⟨105, 89⟩, ⟨105, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[41, 18.5, 30, -0.0, 17, 38, -0.0, -0.0]
  size := ⟨145, 104⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleK_leftRightConstraintLocking_scanline`. -/
def oracleK_leftRightConstraintLocking_scanline : OracleCase where
  name := "oracleK_leftRightConstraintLocking_scanline"
  strategy := .leftRightConstraintLocking
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 10, 41, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨41, 13⟩), (.south, ⟨18.5, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨65, 74, 38, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨17, -4⟩), (.east, ⟨38, 15⟩)] }],
      #[{ box := ⟨123, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20.5, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨113, 89⟩, ⟨113, 35⟩], #[])]
  nodePositions := #[⟨0, 10⟩, ⟨65, 0⟩, ⟨57, 74⟩, ⟨115, 15⟩]
  bendPoints := #[#[], #[⟨20.5, 60⟩, ⟨76, 60⟩], #[], #[⟨105, 89⟩, ⟨105, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[41, 18.5, 30, -0.0, 17, 38, -0.0, -0.0]
  size := ⟨145, 104⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleK_left_scanline`. -/
def oracleK_left_scanline : OracleCase where
  name := "oracleK_left_scanline"
  strategy := .left
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 10, 41, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨41, 13⟩), (.south, ⟨18.5, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨65, 74, 38, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨17, -4⟩), (.east, ⟨38, 15⟩)] }],
      #[{ box := ⟨123, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20.5, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨113, 89⟩, ⟨113, 35⟩], #[])]
  nodePositions := #[⟨0, 10⟩, ⟨65, 0⟩, ⟨1.5, 74⟩, ⟨115, 15⟩]
  bendPoints := #[#[], #[⟨20.5, 60⟩, ⟨20.5, 60⟩], #[], #[⟨105, 89⟩, ⟨105, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[41, 18.5, 30, -0.0, 17, 38, -0.0, -0.0]
  size := ⟨145, 104⟩
  offset := ⟨0, 0⟩

/-- Oracle case `oracleK_right_scanline`. -/
def oracleK_right_scanline : OracleCase where
  name := "oracleK_right_scanline"
  strategy := .right
  constraints := .scanline
  layers := #[
      #[{ box := ⟨0, 10, 41, 30⟩, margin := ⟨0, 4, 4, 0⟩, ports := #[(.east, ⟨41, 13⟩), (.south, ⟨18.5, 30⟩)] }],
      #[{ box := ⟨69, 0, 30, 50⟩, ports := #[(.east, ⟨30, 25⟩), (.west, ⟨-0.0, 25⟩)] },
        { box := ⟨65, 74, 38, 30⟩, margin := ⟨4, 0, 0, 0⟩, ports := #[(.north, ⟨17, -4⟩), (.east, ⟨38, 15⟩)] }],
      #[{ box := ⟨123, 15, 30, 30⟩, ports := #[(.west, ⟨-0.0, 20⟩), (.west, ⟨-0.0, 10⟩)] }]]
  edges := #[(0, 3, #[], #[]),
    (1, 4, #[⟨20.5, 60⟩, ⟨84, 60⟩], #[]),
    (2, 7, #[], #[]),
    (5, 6, #[⟨113, 89⟩, ⟨113, 35⟩], #[])]
  nodePositions := #[⟨8, 10⟩, ⟨73, 0⟩, ⟨65, 74⟩, ⟨123, 15⟩]
  bendPoints := #[#[], #[⟨28.5, 60⟩, ⟨84, 60⟩], #[], #[⟨113, 89⟩, ⟨113, 35⟩]]
  labelPositions := #[#[], #[], #[], #[]]
  portX := #[41, 18.5, 30, -0.0, 17, 38, -0.0, -0.0]
  size := ⟨145, 104⟩
  offset := ⟨-8, 0⟩

/-- All oracle cases. -/
def oracleCases : Array OracleCase := #[
  oracleB_edgeLength_quadratic,
  oracleB_edgeLength_scanline,
  oracleB_left_quadratic,
  oracleB_leftRightConnectionLocking_scanline,
  oracleB_leftRightConstraintLocking_quadratic,
  oracleB_leftRightConstraintLocking_scanline,
  oracleB_left_scanline,
  oracleB_right_scanline,
  oracleC_edgeLength_quadratic,
  oracleC_edgeLength_scanline,
  oracleC_left_quadratic,
  oracleC_leftRightConnectionLocking_scanline,
  oracleC_leftRightConstraintLocking_quadratic,
  oracleC_leftRightConstraintLocking_scanline,
  oracleC_left_scanline,
  oracleC_right_scanline,
  oracleD_edgeLength_scanline,
  oracleD_leftRightConnectionLocking_scanline,
  oracleD_leftRightConstraintLocking_quadratic,
  oracleD_left_scanline,
  oracleD_right_scanline,
  oracleE_edgeLength_scanline,
  oracleE_leftRightConnectionLocking_scanline,
  oracleE_leftRightConstraintLocking_quadratic,
  oracleE_left_scanline,
  oracleE_right_scanline,
  oracleF_edgeLength_scanline,
  oracleF_leftRightConnectionLocking_scanline,
  oracleF_leftRightConstraintLocking_quadratic,
  oracleF_left_scanline,
  oracleF_right_scanline,
  oracleG_edgeLength_scanline,
  oracleG_leftRightConnectionLocking_scanline,
  oracleG_leftRightConstraintLocking_quadratic,
  oracleG_left_scanline,
  oracleG_right_scanline,
  oracleH_edgeLength_scanline,
  oracleH_leftRightConnectionLocking_scanline,
  oracleH_leftRightConstraintLocking_quadratic,
  oracleH_left_scanline,
  oracleH_right_scanline,
  oracleI_edgeLength_scanline,
  oracleI_leftRightConnectionLocking_scanline,
  oracleI_leftRightConstraintLocking_quadratic,
  oracleI_left_scanline,
  oracleI_right_scanline,
  oracleJ_edgeLength_quadratic,
  oracleJ_edgeLength_scanline,
  oracleJ_left_quadratic,
  oracleJ_leftRightConnectionLocking_scanline,
  oracleJ_leftRightConstraintLocking_quadratic,
  oracleJ_leftRightConstraintLocking_scanline,
  oracleJ_left_scanline,
  oracleJ_right_scanline,
  oracleK_edgeLength_quadratic,
  oracleK_edgeLength_scanline,
  oracleK_left_quadratic,
  oracleK_leftRightConnectionLocking_scanline,
  oracleK_leftRightConstraintLocking_quadratic,
  oracleK_leftRightConstraintLocking_scanline,
  oracleK_left_scanline,
  oracleK_right_scanline]

def oracleTests : Suite := suite "layered.intermediate.compaction.oracle" do
  for c in oracleCases do
    c.check

/-! ### Registration -/

def registrationTests : Suite := suite "layered.intermediate.compaction.registration" do
  check "HORIZONTAL_COMPACTOR is registered" (← IntermediateProcessorStrategy.isAvailable .horizontalCompactor)
  let p ← IntermediateProcessorStrategy.create .horizontalCompactor
  checkEq "processor name" p.name "HorizontalGraphCompactor"

def suites : Array Tests.Suite :=
  #[segmentTests, spacingsTests, transformerTests, strategyTests, networkSimplexTests, splineTests, oracleTests,
    registrationTests]

end Tests.Layered.IntermediateCompaction
