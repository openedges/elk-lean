import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.P5Edges.Orthogonal
import Elk.Alg.Layered.P5Edges.OrthogonalEdgeRouter
import Elk.Alg.Layered.P5Edges.PolylineEdgeRouter
import Tests.Layered.P5OrthogonalSegmentGraphRef
/-!
Tests of `org.eclipse.elk.alg.layered.p5edges` (orthogonal and polyline routers, the orthogonal routing
generator and its hyperedge segment machinery).

The elk-rs tests (`p5_edges/basic_edge_router_test.rs`) run the whole pipeline on ElkGraphs and assert
that orthogonal routes are axis-aligned; here hand-built, already placed layered graphs are routed
directly, the axis-alignment assertion is checked on the resulting routes, and the bend points, slots
and layer offsets are compared with values derived by hand from the generator's segment / dependency /
slot logic (comments "hand: …").

Common setup: nodes `30 × 30`, layers `30` wide, `SPACING_EDGE_EDGE(_BETWEEN_LAYERS) = 10`,
`SPACING_EDGE_NODE_BETWEEN_LAYERS = 10`, `SPACING_NODE_NODE_BETWEEN_LAYERS = 20`, `RANDOM = Random(1)`
(whose first `nextInt(2)` is `1`). East ports sit at `(30, 15)`, west ports at `(0, 15)` of their node
(size 0, so the anchor is `(0, 0)`).
-/
namespace Tests.Layered.P5Orthogonal

open Tests Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Alg Elk.Alg.Layered Elk.Alg.Layered.Graph
  Elk.Alg.Layered.Options Elk.Alg.Layered.P5Edges Elk.Alg.Layered.P5Edges.Orthogonal
  Elk.Alg.Layered.P5Edges.Orthogonal.Direction Elk.Alg.Layered.Intermediate
open Elk (ElkEnum EnumSet)

/-- A graph with the common spacings, `RANDOM = Random(seed)` and `internal.spacings`. -/
def mkGraph (seed : Int := 1) : LayeredM LGraphId := do
  let g ← LayeredM.createGraph
  LayeredM.modifyGraph g fun x =>
    let props := x.props
      |>.set LayeredOptions.SPACING_EDGE_EDGE 10.0
      |>.set LayeredOptions.SPACING_EDGE_EDGE_BETWEEN_LAYERS 10.0
      |>.set LayeredOptions.SPACING_EDGE_NODE_BETWEEN_LAYERS 10.0
      |>.set LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS 20.0
    { x with props := props,
             internal := { x.internal with random := some (Random.ofInt seed), spacings := some (Spacings.new props) } }
  return g

/-- Appends a layer of the given width. -/
def addLayer (g : LGraphId) (width : Float := 30.0) : LayeredM LayerId := do
  let l ← LayeredM.createLayer g
  LayeredM.modifyLayer l fun x => { x with size := ⟨width, 0.0⟩ }
  LayeredM.modifyGraph g fun x => { x with layers := x.layers.push l }
  return l

/-- A node at `y` (size `w × h`) appended to layer `l`. -/
def addNode (g : LGraphId) (l : LayerId) (y : Float) (w : Float := 30.0) (h : Float := 30.0) : LayeredM LNodeId := do
  let n ← LayeredM.createNode g { size := ⟨w, h⟩, position := ⟨0.0, y⟩ }
  LayeredM.setNodeLayer n (some l)
  return n

/-- A size-0 port on `side` at `(x, y)` relative to its node. -/
def addPort (n : LNodeId) (side : PortSide) (x y : Float) : LayeredM LPortId := do
  let p ← LayeredM.createPort
  LayeredM.setPortNode p (some n)
  LayeredM.modifyPort p fun pt => { pt.setSide side with position := ⟨x, y⟩ }
  return p

/-- An edge `s → t`. -/
def connect (s t : LPortId) : LayeredM LEdgeId := do
  let e ← LayeredM.createEdge
  LayeredM.setEdgeSource e (some s)
  LayeredM.setEdgeTarget e (some t)
  return e

def runPhase (phase : LayeredPhase) (g : LGraphId) : LayeredM Unit := phase.process g ProgressMonitor.null

def bends (a : LGraphArena) (e : LEdgeId) : Array KVector := (a.edge e).bendPoints

def junctions (a : LGraphArena) (e : LEdgeId) : Option KVectorChain := (a.edge e).props.get? LayeredOptions.JUNCTION_POINTS

def kv (x y : Float) : KVector := ⟨x, y⟩

/-- The Rust `check_edge_route_is_orthogonal` assertion on source anchor, bend points, target anchor:
consecutive points alternate between horizontal and vertical segments (tolerance 0.05). -/
def isOrthogonalRoute (a : LGraphArena) (e : LEdgeId) : Bool := Id.run do
  let ed := a.edge e
  let some s := ed.source.bind a.portAbsoluteAnchor | return false
  let some t := ed.target.bind a.portAbsoluteAnchor | return false
  let route := #[s] ++ ed.bendPoints ++ #[t]
  if route.size < 2 then return false
  let tol := 0.05
  let mut horizontal : Bool := (route[0]!.y - route[1]!.y).abs < tol
  for i in [1:route.size] do
    let prev := route[i - 1]!
    let curr := route[i]!
    if horizontal then
      if (prev.y - curr.y).abs > tol then return false
    else
      if (prev.x - curr.x).abs > tol then return false
    horizontal := !horizontal
  return true


/-! ## Orthogonal edge router on hand-built graphs -/

def straightEdgeTests : Suite := suite "layered.p5edges.orthogonal.straight" do
  -- hand: one degenerate segment [15, 15] → 0 slots; L1 at 30 + nodeNodeSpacing 20 = 50; width 50 + 30
  let ((e, b, g), a) ← LayeredM.run (do
      let g ← mkGraph
      let l0 ← addLayer g
      let l1 ← addLayer g
      let na ← addNode g l0 0.0
      let nb ← addNode g l1 0.0
      let pa ← addPort na .east 30.0 15.0
      let pb ← addPort nb .west 0.0 15.0
      let e ← connect pa pb
      runPhase OrthogonalEdgeRouter.phase g
      return (e, nb, g))
  checkEq "straight edge: no bend points" (bends a e).size 0
  checkFloat "straight edge: L1 x" (a.node b).position.x 50.0
  checkFloat "straight edge: graph width" (a.graph g).size.x 80.0
  check "straight edge: random untouched" ((a.graph g).internal.random == some (Random.ofInt 1))

/-- Two layers `[A(y 0), C(y 50)]`, `[B(y yB), D(y yD)]` with crossing edges `A → D`, `C → B`. -/
def crossing (yB yD : Float) : LayeredM (LGraphId × LEdgeId × LEdgeId × LNodeId) := do
  let g ← mkGraph
  let l0 ← addLayer g
  let l1 ← addLayer g
  let na ← addNode g l0 0.0
  let nc ← addNode g l0 50.0
  let nb ← addNode g l1 yB
  let nd ← addNode g l1 yD
  let pa ← addPort na .east 30.0 15.0
  let pc ← addPort nc .east 30.0 15.0
  let pb ← addPort nb .west 0.0 15.0
  let pd ← addPort nd .west 0.0 15.0
  let eAD ← connect pa pd
  let eCB ← connect pc pb
  return (g, eAD, eCB, nb)

def crossingRegularTests : Suite := suite "layered.p5edges.orthogonal.crossingRegular" do
  -- hand: S0 = A→D (in 15, out 75), S1 = C→B (in 65, out 25); no conflicts, crossings 1 : 1 → two
  -- zero-weight dependencies; the non-critical cycle breaker removes S0→S1 (S0 gets the higher mark),
  -- leaving S1→S0: S1 slot 0 (x 40), S0 slot 1 (x 50); 2 slots → width 0 + 10 + 10 + 10 = 30
  let ((g, eAD, eCB, nb), a) ← LayeredM.run (do
      let r ← crossing 10.0 60.0
      runPhase OrthogonalEdgeRouter.phase r.1
      return r)
  checkEq "A→D bend points" (bends a eAD) #[kv 50 15, kv 50 75]
  checkEq "C→B bend points" (bends a eCB) #[kv 40 65, kv 40 25]
  check "A→D orthogonal" (isOrthogonalRoute a eAD)
  check "C→B orthogonal" (isOrthogonalRoute a eCB)
  checkNone "no junction points" (junctions a eAD)
  checkFloat "L1 x after two slots" (a.node nb).position.x 60.0
  checkFloat "graph width" (a.graph g).size.x 90.0
  check "no random draw" ((a.graph g).internal.random == some (Random.ofInt 1))

def crossingCriticalTests : Suite := suite "layered.p5edges.orthogonal.crossingCritical" do
  -- hand: S0 = A→D (in 15, out 65), S1 = C→B (in 65, out 15); critical threshold 0.2 · 50 = 10, both
  -- orderings critical → critical dependencies S1→S0 (D0) and S0→S1 (D1). The critical cycle detector
  -- draws nextInt(2) = 1 among [S1, S0] → S0 gets the source mark, D0 (S1→S0) closes the cycle, so S1
  -- is split by S0 in the free area (25, 55) at 40: S1 = (65 → 40), partner S2 = (40 → 15).
  -- New critical dependencies S1→S0→S2 give slots S1 = 0, S0 = 1, S2 = 2 → 3 slots.
  let ((g, eAD, eCB, nb), a) ← LayeredM.run (do
      let r ← crossing 0.0 50.0
      runPhase OrthogonalEdgeRouter.phase r.1
      return r)
  checkEq "A→D bend points (slot 1)" (bends a eAD) #[kv 50 15, kv 50 65]
  checkEq "C→B bend points (split: slot 0, partner slot 2)" (bends a eCB) #[kv 40 65, kv 40 40, kv 60 40, kv 60 15]
  check "A→D orthogonal" (isOrthogonalRoute a eAD)
  check "C→B orthogonal" (isOrthogonalRoute a eCB)
  checkFloat "L1 x after three slots" (a.node nb).position.x 70.0
  checkFloat "graph width" (a.graph g).size.x 100.0
  check "one random draw" ((a.graph g).internal.random == some ((Random.ofInt 1).nextInt 2).2)

def hyperedgeTests : Suite := suite "layered.p5edges.orthogonal.hyperedge" do
  -- hand: one segment for pA (in 40) with pB (out 15) and pD (out 65): extent [15, 65], slot 0, x = 40.
  -- (40, 40) lies inside the extent → junction point on the first edge only (created-set).
  let ((g, eAB, eAD, nb), a) ← LayeredM.run (do
      let g ← mkGraph
      let l0 ← addLayer g
      let l1 ← addLayer g
      let na ← addNode g l0 25.0
      let nb ← addNode g l1 0.0
      let nd ← addNode g l1 50.0
      let pa ← addPort na .east 30.0 15.0
      let pb ← addPort nb .west 0.0 15.0
      let pd ← addPort nd .west 0.0 15.0
      let eAB ← connect pa pb
      let eAD ← connect pa pd
      runPhase OrthogonalEdgeRouter.phase g
      return (g, eAB, eAD, nb))
  checkEq "A→B bend points" (bends a eAB) #[kv 40 40, kv 40 15]
  checkEq "A→D bend points" (bends a eAD) #[kv 40 40, kv 40 65]
  checkEq "A→B junction point" ((junctions a eAB).getD #[]) #[kv 40 40]
  checkNone "A→D has no junction point" (junctions a eAD)
  check "A→B orthogonal" (isOrthogonalRoute a eAB)
  check "A→D orthogonal" (isOrthogonalRoute a eAD)
  checkFloat "L1 x after one slot (0 + 10 + 10)" (a.node nb).position.x 50.0
  checkFloat "graph width" (a.graph g).size.x 80.0

def layerOffsetTests : Suite := suite "layered.p5edges.orthogonal.layerOffsets" do
  -- hand: L0 x 0; A→B straight → +20 → L1 x 50; B→C one slot at 80 + 10 = 90, width 20 → L2 x 100; 130
  let ((g, nb, nc, eBC), a) ← LayeredM.run (do
      let g ← mkGraph
      let l0 ← addLayer g
      let l1 ← addLayer g
      let l2 ← addLayer g
      let na ← addNode g l0 0.0
      let nb ← addNode g l1 0.0
      let nc ← addNode g l2 40.0
      let pa ← addPort na .east 30.0 15.0
      let pbw ← addPort nb .west 0.0 15.0
      let pbe ← addPort nb .east 30.0 15.0
      let pc ← addPort nc .west 0.0 15.0
      let _ ← connect pa pbw
      let eBC ← connect pbe pc
      runPhase OrthogonalEdgeRouter.phase g
      return (g, nb, nc, eBC))
  checkFloat "L1 x" (a.node nb).position.x 50.0
  checkFloat "L2 x" (a.node nc).position.x 100.0
  checkEq "B→C bend points" (bends a eBC) #[kv 90 15, kv 90 55]
  checkFloat "graph width" (a.graph g).size.x 130.0
  -- f32 accumulation (Java `float xpos`): L0 30.1 wide → xpos = f32(30.1), then f32(xpos + 20)
  let ((g2, nb2), a2) ← LayeredM.run (do
      let g ← mkGraph
      let l0 ← addLayer g 30.1
      let l1 ← addLayer g
      let na ← addNode g l0 0.0 (w := 30.1)
      let nb ← addNode g l1 0.0
      let pa ← addPort na .east 30.1 15.0
      let pb ← addPort nb .west 0.0 15.0
      let _ ← connect pa pb
      runPhase OrthogonalEdgeRouter.phase g
      return (g, nb))
  let expectedX := Float.toF32 (Float.toF32 30.1 + 20.0)
  check "f32: L1 x is f32(f32(30.1) + 20)" ((a2.node nb2).position.x == expectedX)
  check "f32: L1 x differs from the f64 sum" ((a2.node nb2).position.x != 30.1 + 20.0)
  check "f32: graph width rounded" ((a2.graph g2).size.x == Float.toF32 (expectedX + 30.0))
  -- external west port dummy layer: no node spacing next to it
  let ((g3, nb3), a3) ← LayeredM.run (do
      let g ← mkGraph
      let l0 ← addLayer g 10.0
      let l1 ← addLayer g
      let ne ← addNode g l0 0.0 (w := 10.0) (h := 10.0)
      LayeredM.modifyNode ne fun x => { x with type := .externalPort, internal := { x.internal with extPortSide := .west } }
      let nb ← addNode g l1 (-10.0)
      let pe ← addPort ne .east 10.0 5.0
      let pb ← addPort nb .west 0.0 15.0
      let _ ← connect pe pb
      runPhase OrthogonalEdgeRouter.phase g
      return (g, nb))
  checkFloat "external layer: L1 directly after it" (a3.node nb3).position.x 10.0
  checkFloat "external layer: graph width" (a3.graph g3).size.x 40.0

/-! ## Routing directions through the generator API (hierarchical port router use) -/

def verticalTests : Suite := suite "layered.p5edges.orthogonal.vertical" do
  -- north to south: A's south port (abs 15, 30) → B's north port (abs 65, 100), start 50, slot 0
  let ((slots, e), a) ← LayeredM.run (do
      let g ← mkGraph
      let na ← LayeredM.createNode g { size := ⟨30, 30⟩, position := ⟨0, 0⟩ }
      let nb ← LayeredM.createNode g { size := ⟨10, 10⟩, position := ⟨60, 100⟩ }
      LayeredM.modifyGraph g fun x => { x with layerlessNodes := #[na, nb] }
      let pa ← addPort na .south 15.0 30.0
      let pb ← addPort nb .north 5.0 0.0
      let e ← connect pa pb
      let gen := OrthogonalRoutingGenerator.new .northToSouth 10.0 (some "extsouth")
      let slots ← gen.routeEdges g #[na] 0 #[nb] 50.0
      return (slots, e))
  checkEq "N→S: one slot" slots 1
  checkEq "N→S bend points" (bends a e) #[kv 15 50, kv 65 50]
  -- south to north with crossing edges (the x coordinates of `crossingRegular`): S0 = A→D slot 1,
  -- S1 = C→B slot 0; slots grow upwards: y = start - slot · 10
  let ((slots2, eAD, eCB), a2) ← LayeredM.run (do
      let g ← mkGraph
      let mk (x y : Float) : LayeredM LNodeId := LayeredM.createNode g { size := ⟨30, 30⟩, position := ⟨x, y⟩ }
      let na ← mk 0 100
      let nc ← mk 50 100
      let nb ← mk 10 0
      let nd ← mk 60 0
      LayeredM.modifyGraph g fun x => { x with layerlessNodes := #[na, nc, nb, nd] }
      let pa ← addPort na .north 15.0 0.0
      let pc ← addPort nc .north 15.0 0.0
      let pb ← addPort nb .south 15.0 30.0
      let pd ← addPort nd .south 15.0 30.0
      let eAD ← connect pa pd
      let eCB ← connect pc pb
      let gen := OrthogonalRoutingGenerator.new .southToNorth 10.0 (some "extnorth")
      let slots ← gen.routeEdges g #[na, nc] 0 #[nb, nd] 70.0
      return (slots, eAD, eCB))
  checkEq "S→N: two slots" slots2 2
  checkEq "S→N A→D bend points (slot 1)" (bends a2 eAD) #[kv 15 60, kv 75 60]
  checkEq "S→N C→B bend points (slot 0)" (bends a2 eCB) #[kv 65 70, kv 25 70]

/-! ## Polyline edge router -/

/-- `L0 = [A (w × 30, ALIGNMENT = LEFT, east port at (w, 15))]`, `L1 = [B (y 40), D (y 80)]` with
`A → B` and optionally `A → D`; layer width 30. -/
def polylineGraph (w : Float) (withD : Bool) (zone : Option Float := none) :
    LayeredM (LGraphId × LEdgeId × LEdgeId × LNodeId) := do
  let g ← mkGraph
  if let some z := zone then
    LayeredM.setGraphProp g LayeredOptions.EDGE_ROUTING_POLYLINE_SLOPED_EDGE_ZONE_WIDTH z
  let l0 ← addLayer g
  let l1 ← addLayer g
  let na ← addNode g l0 0.0 (w := w)
  LayeredM.setNodeProp na CoreOptions.ALIGNMENT Alignment.left
  let nb ← addNode g l1 40.0
  let pa ← addPort na .east w 15.0
  let pb ← addPort nb .west 0.0 15.0
  let eAB ← connect pa pb
  let eAD ← if withD then do
      let nd ← addNode g l1 80.0
      let pd ← addPort nd .west 0.0 15.0
      connect pa pd
    else pure eAB
  runPhase PolylineEdgeRouter.phase g
  return (g, eAB, eAD, nb)

def polylineTests : Suite := suite "layered.p5edges.polyline" do
  -- hand: edge space factor min(10/20, 1) = 0.5; layer spacing 0.4 · 0.5 · 40 + 20 = 28 → L1 at 58.
  -- Full-width node: port anchor x 30 = layer border → inside the sloped edge zone (2) → no bend point.
  let ((g, e, _, nb), a) ← LayeredM.run (polylineGraph 30.0 false)
  checkEq "inside zone: no bend points" (bends a e).size 0
  checkFloat "inside zone: L1 x" (a.node nb).position.x 58.0
  checkFloat "inside zone: graph width" (a.graph g).size.x 88.0
  -- Narrow left-aligned node: anchor x 10, border 30 → 20 > 2 → bend point on the border (prepended)
  let ((_, e2, _, _), a2) ← LayeredM.run (polylineGraph 10.0 false)
  checkEq "outside zone: bend point on the layer border" (bends a2 e2) #[kv 30 15]
  checkNone "outside zone: single edge, no junction point" (junctions a2 e2)
  -- Same with a sloped edge zone of 25 ≥ 20 → no bend point
  let ((_, e3, _, _), a3) ← LayeredM.run (polylineGraph 10.0 false (zone := some 25.0))
  checkEq "zone 25: no bend point" (bends a3 e3).size 0
  -- Two edges from the port: both get the bend point, the junction point only once.
  -- hand: max vertical diff 80 → layer spacing 0.4 · 0.5 · 80 + 20 = 36 → L1 at 66, width 96
  let ((g4, eAB, eAD, nb4), a4) ← LayeredM.run (polylineGraph 10.0 true)
  checkEq "hyperedge: A→B bend point" (bends a4 eAB) #[kv 30 15]
  checkEq "hyperedge: A→D bend point" (bends a4 eAD) #[kv 30 15]
  checkEq "hyperedge: junction point on the first edge" ((junctions a4 eAB).getD #[]) #[kv 30 15]
  checkNone "hyperedge: no second junction point" (junctions a4 eAD)
  checkFloat "hyperedge: L1 x" (a4.node nb4).position.x 66.0
  checkFloat "hyperedge: graph width" (a4.graph g4).size.x 96.0

/-! ## Segment machinery -/

/-- A segment with the given coordinates (extent recomputed). -/
def seg (incoming outgoing : Array Float) : HyperEdgeSegment :=
  ({ incomingConnectionCoordinates := incoming, outgoingConnectionCoordinates := outgoing } : HyperEdgeSegment).recomputeExtent


def segmentTests : Suite := suite "layered.p5edges.orthogonal.segment" do
  checkEq "insertSorted into empty" (HyperEdgeSegment.insertSorted #[] 5.0) #[5.0]
  checkEq "insertSorted middle" (HyperEdgeSegment.insertSorted #[1.0, 3.0] 2.0) #[1.0, 2.0, 3.0]
  checkEq "insertSorted duplicate ignored" (HyperEdgeSegment.insertSorted #[1.0, 3.0] 3.0) #[1.0, 3.0]
  checkEq "insertSorted end" (HyperEdgeSegment.insertSorted #[1.0, 3.0] 4.0) #[1.0, 3.0, 4.0]
  let s := seg #[10.0, 20.0] #[5.0, 30.0]
  checkFloat "extent start" s.startPosition 5.0
  checkFloat "extent end" s.endPosition 30.0
  checkFloat "length" s.length 25.0
  check "represents hyperedge (4 coordinates)" s.representsHyperedge
  check "two coordinates: no hyperedge" !(seg #[1.0] #[2.0]).representsHyperedge
  check "empty extent is NaN" (seg #[] #[]).startPosition.isNaN
  check "split partner without splitBy is a dummy" ({ splitPartner := some 1 } : HyperEdgeSegment).isDummy
  check "split segment is not a dummy" !({ splitPartner := some 1, splitBy := some 2 } : HyperEdgeSegment).isDummy
  -- ordering by mark (HyperEdgeSegment.compareTo, used for the unprocessed list)
  let segs : Array HyperEdgeSegment := #[{ mark := 3 }, { mark := -1 }, { mark := 2 }, { mark := -1 }]
  let order := stableSort (Array.range segs.size) fun i j => HyperEdgeSegment.compareByMark segs[i]! segs[j]!
  checkEq "sorted by mark (stable)" order #[1, 3, 2, 0]
  let (p1, p2) := (seg #[10.0] #[30.0, 50.0]).simulateSplit
  checkEq "simulateSplit: first keeps incoming" p1.incomingConnectionCoordinates #[10.0]
  checkEq "simulateSplit: second keeps outgoing" p2.outgoingConnectionCoordinates #[30.0, 50.0]
  checkFloat "simulateSplit: second extent start" p2.startPosition 30.0

def dependencyTests : Suite := suite "layered.p5edges.orthogonal.dependency" do
  -- swap_remove semantics (Rust) of the dependency lists
  let g : SegmentGraph := { segments := #[seg #[0] #[1], seg #[2] #[3], seg #[4] #[5], seg #[6] #[7]] }
  let (g, d0) := g.createAndAddRegular 0 1 1
  let (g, d1) := g.createAndAddRegular 0 2 1
  let (g, d2) := g.createAndAddRegular 0 3 1
  let g := g.removeDependency d0
  checkEq "remove: last moved into the hole" (g.segment 0).outgoingSegmentDependencies #[d2, d1]
  checkEq "remove: target list" (g.segment 1).incomingSegmentDependencies #[]
  check "remove: detached" ((g.dependency d0).source.isNone && (g.dependency d0).target.isNone)
  let g := g.reverseDependency d1
  checkEq "reverse: source lists" (g.segment 2).outgoingSegmentDependencies #[d1]
  checkEq "reverse: target lists" (g.segment 0).incomingSegmentDependencies #[d1]
  check "reverse: swapped" ((g.dependency d1).source == some 2 && (g.dependency d1).target == some 0)
  -- splitAt: S0 (10 → 30, 50) split at 25, all dependencies of S0 removed
  let h : SegmentGraph := { segments := #[seg #[10] #[30, 50], seg #[20] #[60]] }
  let (h, _) := h.createAndAddRegular 1 0 5
  let (h, _) := h.createAndAddRegular 0 1 7
  let (h, partner) := h.splitAt 0 25.0
  checkEq "splitAt: partner appended" partner 2
  checkEq "splitAt: segment outgoing" (h.segment 0).outgoingConnectionCoordinates #[25.0]
  checkFloat "splitAt: segment extent end" (h.segment 0).endPosition 25.0
  checkEq "splitAt: partner incoming" (h.segment 2).incomingConnectionCoordinates #[25.0]
  checkEq "splitAt: partner outgoing" (h.segment 2).outgoingConnectionCoordinates #[30.0, 50.0]
  check "splitAt: partner links" ((h.segment 0).splitPartner == some 2 && (h.segment 2).splitPartner == some 0)
  check "splitAt: dependencies removed" ((h.segment 0).incomingSegmentDependencies.isEmpty &&
    (h.segment 0).outgoingSegmentDependencies.isEmpty && (h.segment 1).outgoingSegmentDependencies.isEmpty &&
    (h.segment 1).incomingSegmentDependencies.isEmpty)

def cycleDetectorTests : Suite := suite "layered.p5edges.orthogonal.cycleDetector" do
  -- S0 →(2) S1 →(3) S2 →(1) S0. hand: no sinks/sources; max outflow 1 for S1 and S0 (unprocessed order
  -- by mark: S2, S1, S0); nextInt(2) = 1 picks S0 (mark 4); S2 becomes a sink (mark 2 → 6 after the
  -- shift), S1 a source (mark 5) → only S2 → S0 points backwards.
  let g : SegmentGraph := { segments := #[seg #[0] #[10], seg #[1] #[11], seg #[2] #[12]] }
  let (g, _) := g.createAndAddRegular 0 1 2
  let (g, _) := g.createAndAddRegular 1 2 3
  let (g, d2) := g.createAndAddRegular 2 0 1
  let (cycles, g', r) := HyperEdgeCycleDetector.detectCycles g false (Random.ofInt 1)
  checkEq "cycle dependency" cycles #[d2]
  checkEq "marks" (g'.segments.map (·.mark)) #[4, 5, 6]
  check "one draw" (r == ((Random.ofInt 1).nextInt 2).2)
  let (critical, _, r2) := HyperEdgeCycleDetector.detectCycles g true (Random.ofInt 1)
  checkEq "critical only: no critical dependencies" critical #[]
  check "critical only: no draw" (r2 == Random.ofInt 1)
  -- breakNonCriticalCycles reverses the weighted cycle dependency S2 → S0
  let (g3, _) := OrthogonalRoutingGenerator.breakNonCriticalCycles g (Random.ofInt 1)
  check "reversed to S0 → S2" ((g3.dependency d2).source == some 0 && (g3.dependency d2).target == some 2)
  checkEq "S0 outgoing after reversal" (g3.segment 0).outgoingSegmentDependencies #[0, d2]
  checkEq "S2 outgoing after reversal" (g3.segment 2).outgoingSegmentDependencies #[]

/-! ### Differential test of the packed `SegmentGraph` (ORM) against the six-column reference -/

/-- Whether the new and the reference graph agree on every segment (coordinates, extent, split
partner, dependency lists in order) and every dependency (ends, weight, type). -/
def segmentGraphsAgree (g : SegmentGraph) (r : Tests.Layered.SegmentGraphRef.SegmentGraph) : Bool :=
  g.segments.size == r.segments.size && g.dependencyCount == r.dependencyCount &&
    (Array.range g.segments.size).all (fun i =>
      let a := g.segment i
      let b := r.segment i
      a.outgoingSegmentDependencies == b.outgoingSegmentDependencies &&
        a.incomingSegmentDependencies == b.incomingSegmentDependencies &&
        a.incomingConnectionCoordinates == b.incomingConnectionCoordinates &&
        a.outgoingConnectionCoordinates == b.outgoingConnectionCoordinates &&
        a.splitPartner == b.splitPartner && a.startPosition.toBits == b.startPosition.toBits &&
        a.endPosition.toBits == b.endPosition.toBits) &&
    (Array.range g.dependencyCount).all (fun d =>
      let x := g.dependency d
      let y := r.dependency d
      x.source == y.source && x.target == y.target && x.weight == y.weight &&
        (x.dependencyType == .critical) == (y.dependencyType == .critical))

/-- One step of a 64-bit LCG (Knuth's MMIX constants). -/
def lcgNext (x : UInt64) : UInt64 := x * 6364136223846793005 + 1442695040888963407

/-- Applies `steps` random operations (add, remove, reverse, split; remove and reverse also on
already removed dependencies) to both graphs; `false` as soon as they disagree. -/
partial def segmentGraphDiffRun (g : SegmentGraph) (r : Tests.Layered.SegmentGraphRef.SegmentGraph) (rng : UInt64)
    (steps : Nat) : Bool :=
  if steps == 0 then true
  else
    let rng := lcgNext rng
    let op := (rng >>> 33) % 20
    let rng2 := lcgNext rng
    let a := ((rng2 >>> 33) % 1000).toNat
    let rng3 := lcgNext rng2
    let b := ((rng3 >>> 33) % 1000).toNat
    let n := g.segments.size
    let count := g.dependencyCount
    let (g', r') :=
      if op < 10 then
        let critical := op < 2
        let weight : Int := (b / 7) % 40
        (g.addDependency critical (a % n) (b % n) weight, r.addDependency critical (a % n) (b % n) weight)
      else if count == 0 then (g, r)
      else if op < 14 then (g.removeDependency (a % count), r.removeDependency (a % count))
      else if op < 19 then (g.reverseDependency (a % count), r.reverseDependency (a % count))
      else
        let pos := (b.toFloat) / 10.0
        ((g.splitAt (a % n) pos).1, (r.splitAt (a % n) pos).1)
    segmentGraphsAgree g' r' && segmentGraphDiffRun g' r' rng3 (steps - 1)

def segmentGraphDiffTests : Suite := suite "layered.p5edges.orthogonal.segmentGraphDiff" do
  let segs := #[seg #[0] #[10], seg #[1] #[11, 30], seg #[2, 5] #[12], seg #[3] #[13], seg #[4] #[14, 20], seg #[6] #[7]]
  let g : SegmentGraph := { segments := segs }
  let r : Tests.Layered.SegmentGraphRef.SegmentGraph := { segments := segs }
  let mut allAgree := true
  for seed in [0:200] do
    if !segmentGraphDiffRun g r (seed.toUInt64 * 7919 + 1) 300 then allAgree := false
  check "200 random sequences of 300 operations agree with the reference" allAgree
  -- larger graphs: many dependencies per segment
  let big := (Array.range 40).map fun i => seg #[i.toFloat] #[(i * 3 % 17).toFloat + 0.5]
  let mut bigAgree := true
  for seed in [0:10] do
    if !segmentGraphDiffRun { segments := big } { segments := big } (seed.toUInt64 * 104729 + 3) 1500 then
      bigAgree := false
  check "10 random sequences of 1500 operations on 40 segments agree with the reference" bigAgree

def generatorTests : Suite := suite "layered.p5edges.orthogonal.generator" do
  checkEq "countCrossings" (OrthogonalRoutingGenerator.countCrossings #[10, 20, 30, 40] 15 30) 2
  check "minimumDifference with NaN (Rust test)"
    (OrthogonalRoutingGenerator.minimumDifference #[1.0, Float.nan, 3.0, Float.nan]).isNaN
  checkFloat "minimumDifference" (OrthogonalRoutingGenerator.minimumDifference #[5.0, 1.0, 3.0]) 2.0
  check "minimumDifference of duplicates" (OrthogonalRoutingGenerator.minimumDifference #[1.0, 1.0] == Float.maxValue)
  let gen := { OrthogonalRoutingGenerator.new .westToEast 10.0 with criticalConflictThreshold := 2.0 }
  -- hand: S0 (10 → 30), S1 (20 → 40): no conflicts; crossings 2 (S0 left) vs 0 (S1 left) → S1 → S0, weight 32
  let g : SegmentGraph := { segments := #[seg #[10] #[30], seg #[20] #[40]] }
  let (g1, critical) := gen.createDependencyIfNecessary g 0 1
  checkEq "regular: no critical dependency" critical 0
  checkEq "regular: one dependency" g1.dependencies.size 1
  check "regular: S1 → S0 weight 32" ((g1.dependency 0).source == some 1 && (g1.dependency 0).target == some 0 &&
    (g1.dependency 0).weight == 32 && (g1.dependency 0).dependencyType == .regular)
  -- coinciding coordinates in both orderings → two critical dependencies
  let c : SegmentGraph := { segments := #[seg #[10] #[30], seg #[30] #[10]] }
  let (c1, critical2) := gen.createDependencyIfNecessary c 0 1
  checkEq "critical: two critical dependencies" critical2 2
  check "critical: S1 → S0 then S0 → S1" ((c1.dependency 0).source == some 1 && (c1.dependency 1).source == some 0 &&
    (c1.dependency 0).dependencyType == .critical)

/-! ## Processor configurations and registration -/

def configurationTests : Suite := suite "layered.p5edges.configuration" do
  let ((ortho, orthoNs, poly), _) ← LayeredM.run (do
      let g ← mkGraph
      LayeredM.modifyGraph g fun x => { x with internal := { x.internal with
        graphProperties := EnumSet.empty.insert GraphProperties.hyperedges } }
      let ortho ← OrthogonalEdgeRouter.getLayoutProcessorConfiguration g
      LayeredM.modifyGraph g fun x => { x with internal := { x.internal with
        graphProperties := (EnumSet.empty.insert GraphProperties.nonFreePorts).insert GraphProperties.northSouthPorts } }
      let orthoNs ← OrthogonalEdgeRouter.getLayoutProcessorConfiguration g
      LayeredM.modifyGraph g fun x => { x with internal := { x.internal with
        graphProperties := EnumSet.empty.insert GraphProperties.selfLoops } }
      let poly ← PolylineEdgeRouter.getLayoutProcessorConfiguration g
      return (ortho.getD {}, orthoNs.getD {}, poly.getD {}))
  checkEq "ortho hyperedges: before P4" (ortho.processorsBefore LayeredPhases.p4NodePlacement)
    #[IntermediateProcessorStrategy.hyperedgeDummyMerger]
  checkEq "ortho hyperedges: before P3" (ortho.processorsBefore LayeredPhases.p3NodeOrdering)
    #[IntermediateProcessorStrategy.invertedPortProcessor]
  checkEq "ortho north/south: before P3" (orthoNs.processorsBefore LayeredPhases.p3NodeOrdering)
    #[IntermediateProcessorStrategy.invertedPortProcessor, .northSouthPortPreprocessor]
  checkEq "ortho north/south: after P5" (orthoNs.processorsAfter LayeredPhases.p5EdgeRouting)
    #[IntermediateProcessorStrategy.northSouthPortPostprocessor]
  checkEq "polyline baseline: before P3" (poly.processorsBefore LayeredPhases.p3NodeOrdering)
    #[IntermediateProcessorStrategy.invertedPortProcessor]
  checkEq "polyline self loops: before P4" (poly.processorsBefore LayeredPhases.p4NodePlacement)
    #[IntermediateProcessorStrategy.selfLoopPortRestorer, .selfLoopRouter]
  checkEq "polyline self loops: after P5" (poly.processorsAfter LayeredPhases.p5EdgeRouting)
    #[IntermediateProcessorStrategy.selfLoopPostprocessor]
  let orthoPhase ← (EdgeRouterFactory.factoryFor .orthogonal).create
  checkEq "factory: orthogonal" orthoPhase.name "OrthogonalEdgeRouter"
  let undefinedPhase ← (EdgeRouterFactory.factoryFor .undefined).create
  checkEq "factory: undefined → orthogonal" undefinedPhase.name "OrthogonalEdgeRouter"
  let polyPhase ← (EdgeRouterFactory.factoryFor .polyline).create
  checkEq "factory: polyline" polyPhase.name "PolylineEdgeRouter"

def suites : Array Tests.Suite :=
  #[straightEdgeTests, crossingRegularTests, crossingCriticalTests, hyperedgeTests, layerOffsetTests, verticalTests,
    polylineTests, segmentTests, dependencyTests, cycleDetectorTests, segmentGraphDiffTests, generatorTests, configurationTests]

end Tests.Layered.P5Orthogonal
