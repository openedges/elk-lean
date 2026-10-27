import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.P5Edges.Splines
import Elk.Alg.Layered.Intermediate.SplineProcessors
import Tests.Layered.P5Splines
/-! Tests of `org.eclipse.elk.alg.layered.intermediate.FinalSplineBendpointsCalculator` on hand-built
graphs routed by `SplineEdgeRouter` (elk-rs has no test of this processor). The NUB control points of
each segment (first pass) are derived by hand ("hand: …"); the final bend points are the Bezier
control points of the hand-derived NUB control polygon computed with P5b's verified `NubSpline`
("NubSpline of …"), except where the polygon is already in Bezier form (≤ 4 points, also by hand).

Spacings (layered defaults): edge-edge and edge-node between layers 10, node-node between layers 20. -/
namespace Tests.Layered.IntermediateFinalSpline

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Alg Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate Elk.Alg.Layered.P5Edges
  Elk.Alg.Layered.P5Edges.Splines Tests.Layered.P5Splines

/-- The Bezier control points (without the first/last point) of the clamped cubic NUB spline of
`cps` (P5b `NubSpline`, what `calculateBezierBendPoints` appends). -/
def bezierOf (cps : Array KVector) : Array KVector :=
  match NubSpline.new true 3 cps with
  | .ok s => s.getBezierCPDefault.1
  | .error _ => #[]

/-- Routes `g` (`SplineEdgeRouter.phase`) and runs the processor. -/
def routeAndFinish (g : LGraphId) : LayeredM Unit := do
  SplineEdgeRouter.phase.process g ProgressMonitor.null
  FinalSplineBendpointsCalculator.processor.process g ProgressMonitor.null

/-- The configuration `process` reads from a graph without explicit options (`mode` aside). -/
def cfgOf (mode : SplineRoutingMode) (compaction : GraphCompactionStrategy := .none) :
    FinalSplineBendpointsCalculator.Config :=
  { edgeEdgeSpacing := 10.0, edgeNodeSpacing := 10.0, splineRoutingMode := mode, compactionStrategy := compaction }

-- straight and sloped single edges -------------------------------------------------------------------

def singleEdgeTests : Suite := suite "layered.intermediate.FinalSplineBendpointsCalculator.singleEdge" do
  -- straight: A port (20,10) → B port (40,10); segment box x 20, width 20, center y 10
  -- hand: first pass adds the halfway point (30,10); NUB polygon (20,10) (30,10) (40,10) is padded
  -- to (20,10) (20,10) (30,10) (40,10) (already Bezier) → inner points (20,10) (30,10)
  let ((g, a, b, e), ar) ← LayeredM.run (do
      let r ← twoNodes 0.0
      routeAndFinish r.1
      return r)
  checkChain "hand: straight edge: bend points" (ar.edge e).bendPoints #[⟨20, 10⟩, ⟨30, 10⟩]
  checkNone "SPLINE_ROUTE_START removed" (ar.edge e).internal.splineRouteStart
  checkEq "SPLINE_EDGE_CHAIN removed" (ar.edge e).internal.splineEdgeChain.size 0
  check "segment handled" ((ar.graph g).internal.splineSegments.all (·.handled))
  checkEq "indexNodesPerLayer: ids" ((ar.node a).id, (ar.node b).id) ((0 : Int), (0 : Int))
  -- SLOPPY sloped: B port at y 500, B.x 69 (P5b: sloppy gap 49); in/out degrees 1/1 → center y 255;
  -- hand: center x (20 + 69)/2 = 44.5; no neighbours → both shortcuts → single point (44.5,255);
  -- polygon (20,10) (44.5,255) (69,500) padded → inner (20,10) (44.5,255)
  let ((_, _, b2, e2), ar2) ← LayeredM.run (do
      let r ← twoNodes 490.0 (some .sloppy)
      routeAndFinish r.1
      return r)
  checkFloat "router: B.x (sloppy)" (ar2.node b2).position.x 69.0
  checkChain "hand: SLOPPY sloped edge: single center control point" (ar2.edge e2).bendPoints #[⟨20, 10⟩, ⟨44.5, 255⟩]
  -- CONSERVATIVE sloped: B.x 40; hand: first pass (20,10) (30,10) (30,500) (40,500) (center x
  -- 20 + edgeNode 10 + rank 0); straightening points equal the anchors (the anchor and its
  -- neighbour coincide: absMin(±5, 0) = 0)
  let ((g3, _, _, e3), ar3) ← LayeredM.run (do
      let r ← twoNodes 490.0 (some .conservative)
      SplineEdgeRouter.phase.process r.1 ProgressMonitor.null
      FinalSplineBendpointsCalculator.indexNodesPerLayer r.1
      FinalSplineBendpointsCalculator.calculateControlPoints (cfgOf .conservative) r.1 ⟨0⟩
      return r)
  checkChain "hand: CONSERVATIVE first pass: four control points" (ar3.edge e3).bendPoints
    #[⟨20, 10⟩, ⟨30, 10⟩, ⟨30, 500⟩, ⟨40, 500⟩]
  check "first pass marks the segment handled" (ar3.graph g3).internal.splineSegments[0]!.handled
  let ((_, _, _, e4), ar4) ← LayeredM.run (do
      let r ← twoNodes 490.0 (some .conservative)
      routeAndFinish r.1
      return r)
  checkChain "CONSERVATIVE sloped edge: NubSpline of (20,10)×3 (30,10) (30,500) (40,500)×3"
    (ar4.edge e4).bendPoints
    (bezierOf #[⟨20, 10⟩, ⟨20, 10⟩, ⟨20, 10⟩, ⟨30, 10⟩, ⟨30, 500⟩, ⟨40, 500⟩, ⟨40, 500⟩, ⟨40, 500⟩])
  check "CONSERVATIVE differs from SLOPPY" ((ar4.edge e4).bendPoints.size != (ar2.edge e2).bendPoints.size)

-- long edge chain --------------------------------------------------------------------------------------

def longEdgeTests : Suite := suite "layered.intermediate.FinalSplineBendpointsCalculator.longEdge" do
  -- A(L0, port y 10) → D(L1 long-edge dummy at y 30) → B(L2, port y 60), CONSERVATIVE; D.x 40, B.x 60.
  -- The long edge joiner is simulated: e1 gets B's port as target, e2 is disconnected, D removed.
  -- hand first pass: s0 (box 20..40): (20,10) (30,10) (30,30) (40,30) on e1;
  --                  s1 (box 40..60): (40,30) (50,30) (50,60) (60,60) on e2.
  -- hand polygon: anchor (20,10), e1's points, midpoint ((40,30)+(40,30))/2 = (40,30), e2's points,
  -- anchor (60,60); straightening points equal the anchors
  let ((e1, e2), ar) ← LayeredM.run (do
      let g ← graphWith (some .conservative)
      let l0 ← addLayer g
      let l1 ← addLayer g
      let l2 ← addLayer g
      let a ← addNode g l0 0.0
      let d ← addNode g l1 30.0 ⟨0, 0⟩ .longEdge
      let b ← addNode g l2 50.0
      let pa ← addPort a .east ⟨20.0, 10.0⟩
      let pdIn ← addPort d .west ⟨0, 0⟩
      let pdOut ← addPort d .east ⟨0, 0⟩
      let pb ← addPort b .west ⟨0.0, 10.0⟩
      let e1 ← connect pa pdIn
      let e2 ← connect pdOut pb
      SplineEdgeRouter.phase.process g ProgressMonitor.null
      LayeredM.setEdgeTarget e1 (some pb)
      LayeredM.setEdgeSource e2 none
      LayeredM.setEdgeTarget e2 none
      LayeredM.setNodeLayer d none
      FinalSplineBendpointsCalculator.processor.process g ProgressMonitor.null
      return (e1, e2))
  checkChain "long edge: NubSpline of the joined polygon" (ar.edge e1).bendPoints
    (bezierOf #[⟨20, 10⟩, ⟨20, 10⟩, ⟨20, 10⟩, ⟨30, 10⟩, ⟨30, 30⟩, ⟨40, 30⟩, ⟨40, 30⟩, ⟨40, 30⟩, ⟨50, 30⟩,
      ⟨50, 60⟩, ⟨60, 60⟩, ⟨60, 60⟩, ⟨60, 60⟩])
  checkEq "long edge: the chain's second edge is cleared" (ar.edge e2).bendPoints.size 0
  checkEq "long edge: chain removed" (ar.edge e1).internal.splineEdgeChain.size 0
  -- surviving edge: the Bezier points go to SPLINE_SURVIVING_EDGE instead of the first chain edge
  let ((s1, s2), ar2) ← LayeredM.run (do
      let (g, _, _, e) ← twoNodes 0.0
      let (_, _, _, other) ← twoNodes 0.0
      SplineEdgeRouter.phase.process g ProgressMonitor.null
      LayeredM.modifyEdge e fun x => { x with internal := { x.internal with splineSurvivingEdge := some other } }
      FinalSplineBendpointsCalculator.processor.process g ProgressMonitor.null
      return (e, other))
  checkEq "surviving edge: chain edge cleared" (ar2.edge s1).bendPoints.size 0
  -- hand: the other graph is not routed (its B stays at x 0): polygon (20,10) (30,10) (0,10), padded
  -- with (20,10) → inner points (20,10) (30,10)
  checkChain "hand: surviving edge receives the Bezier points" (ar2.edge s2).bendPoints #[⟨20, 10⟩, ⟨30, 10⟩]

-- hyperedges ---------------------------------------------------------------------------------------------

def hyperedgeTests : Suite := suite "layered.intermediate.FinalSplineBendpointsCalculator.hyperedge" do
  -- A's east port (20,10) feeds B (port y 40) and C (port y 80): one hyperedge segment (box 20..40,
  -- center y 25, rank 0). Hyperedges are never sloppy → conservative points plus the center point.
  let build : LayeredM (LGraphId × LEdgeId × LEdgeId) := do
    let g ← graphWith
    let l0 ← addLayer g
    let l1 ← addLayer g
    let a ← addNode g l0 0.0
    let b ← addNode g l1 30.0
    let c ← addNode g l1 70.0
    let pa ← addPort a .east ⟨20.0, 10.0⟩
    let pb ← addPort b .west ⟨0.0, 10.0⟩
    let pc ← addPort c .west ⟨0.0, 10.0⟩
    let e1 ← connect pa pb
    let e2 ← connect pa pc
    return (g, e1, e2)
  let ((_, e1, e2), ar) ← LayeredM.run (do
      let r ← build
      SplineEdgeRouter.phase.process r.1 ProgressMonitor.null
      FinalSplineBendpointsCalculator.indexNodesPerLayer r.1
      -- both start edges reach the shared segment: the second call is a no-op (`handled`)
      FinalSplineBendpointsCalculator.calculateControlPoints (cfgOf .sloppy) r.1 ⟨0⟩
      FinalSplineBendpointsCalculator.calculateControlPoints (cfgOf .sloppy) r.1 ⟨0⟩
      return r)
  checkChain "hand: hyperedge e1: conservative points with center (30,25)" (ar.edge e1).bendPoints
    #[⟨20, 10⟩, ⟨30, 10⟩, ⟨30, 25⟩, ⟨30, 40⟩, ⟨40, 40⟩]
  checkChain "hand: hyperedge e2" (ar.edge e2).bendPoints #[⟨20, 10⟩, ⟨30, 10⟩, ⟨30, 25⟩, ⟨30, 80⟩, ⟨40, 80⟩]
  let ((_, f1, f2), ar2) ← LayeredM.run (do
      let r ← build
      routeAndFinish r.1
      return r)
  checkChain "hyperedge e1: NubSpline of (20,10)×2 (30,10) (30,25) (30,40) (40,40)×2" (ar2.edge f1).bendPoints
    (bezierOf #[⟨20, 10⟩, ⟨20, 10⟩, ⟨30, 10⟩, ⟨30, 25⟩, ⟨30, 40⟩, ⟨40, 40⟩, ⟨40, 40⟩])
  checkChain "hyperedge e2: NubSpline of (20,10)×2 (30,10) (30,25) (30,80) (40,80)×2" (ar2.edge f2).bendPoints
    (bezierOf #[⟨20, 10⟩, ⟨20, 10⟩, ⟨30, 10⟩, ⟨30, 25⟩, ⟨30, 80⟩, ⟨40, 80⟩, ⟨40, 80⟩])

-- north/south ports ------------------------------------------------------------------------------------

def northSouthTests : Suite := suite "layered.intermediate.FinalSplineBendpointsCalculator.northSouth" do
  -- The router only sees EAST/WEST ports (north/south ports reach it through their dummies), so the
  -- edge is routed from A's EAST port (20,10) to B's WEST port (abs (40,110)), CONSERVATIVE, and then
  -- moved to A's SOUTH port (10,20) with SPLINE_NS_PORT_Y_COORD 35 (as after the north/south
  -- postprocessing). hand first pass (routing-time edge information): (20,10) (30,10) (30,110) (40,110)
  -- hand polygon: anchor (10,20), NS point (10,35), the four points, anchor (40,110);
  -- straightening at the SOUTH source: v = 5·(cos π/2, sin π/2) ≈ (3e-16, 5), v2 = (0, 15) →
  -- (absMin(3e-16, 0), absMin(5, 15)) + (10,20) = (10,25); at the target: (40,110)
  let ((ps, e), ar) ← LayeredM.run (do
      let g ← graphWith (some .conservative)
      let l0 ← addLayer g
      let l1 ← addLayer g
      let a ← addNode g l0 0.0
      let b ← addNode g l1 100.0
      let pe ← addPort a .east ⟨20.0, 10.0⟩
      let ps ← addPort a .south ⟨10.0, 20.0⟩
      LayeredM.modifyPort ps fun p => { p with internal := { p.internal with splineNsPortYCoord := some 35.0 } }
      let pb ← addPort b .west ⟨0.0, 10.0⟩
      let e ← connect pe pb
      SplineEdgeRouter.phase.process g ProgressMonitor.null
      LayeredM.setEdgeSource e (some ps)
      FinalSplineBendpointsCalculator.processor.process g ProgressMonitor.null
      return (ps, e))
  checkEq "edge leaves the SOUTH port" (ar.edge e).source (some ps)
  checkChain "north/south: NubSpline of (10,20) (10,25) (10,35) (20,10) (30,10) (30,110) (40,110)×3"
    (ar.edge e).bendPoints
    (bezierOf #[⟨10, 20⟩, ⟨10, 25⟩, ⟨10, 35⟩, ⟨20, 10⟩, ⟨30, 10⟩, ⟨30, 110⟩, ⟨40, 110⟩, ⟨40, 110⟩, ⟨40, 110⟩])
  -- without SPLINE_NS_PORT_Y_COORD the NS point falls back to the anchor's y (Rust)
  let ((_, a2), ar2) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let n ← LayeredM.createNode g { position := ⟨5, 5⟩, size := ⟨20, 20⟩ }
      let p ← addPort n .north ⟨10, 0⟩
      return (g, p))
  checkEq "hand: NS control point falls back to the anchor (15,5)"
    (FinalSplineBendpointsCalculator.northSouthControlPoint ar2 a2 ⟨15, 5⟩) (some ⟨15, 5⟩)

-- direct tests of the variants ---------------------------------------------------------------------

/-- A graph with nodes A (L0) and B (L1), one edge and the given segment as table entry 0. -/
def withSegment (seg : LEdgeId → SplineSegment) : LayeredM (LGraphId × LEdgeId) := do
  let (g, _, _, e) ← twoNodes 0.0
  LayeredM.modifyGraph g fun x => { x with internal := { x.internal with splineSegments := #[seg e] } }
  return (g, e)

def variantTests : Suite := suite "layered.intermediate.FinalSplineBendpointsCalculator.variants" do
  let info : EdgeInformation := { startY := 10, endY := 50, normalSourceNode := true, normalTargetNode := true }
  let base (e : LEdgeId) : SplineSegment :=
    { edges := #[e], boundingBox := ⟨100, 0, 40, 60⟩, rank := 2, xDelta := 3, edgeInformation := #[(e, info)] }
  -- hand: center x = 100 + 10 + (3 + 2·10) = 133
  let ((_, e), ar) ← LayeredM.run (do
      let r ← withSegment fun e => { base e with edgeInformation := #[(e, { info with invertedLeft := true })] }
      FinalSplineBendpointsCalculator.calculateControlPoints (cfgOf .conservative) r.1 ⟨0⟩
      return r)
  checkChain "hand: inverted WEST source: source straight point at the right end" (ar.edge e).bendPoints
    #[⟨140, 10⟩, ⟨133, 10⟩, ⟨133, 50⟩, ⟨140, 50⟩]
  let ((_, e), ar) ← LayeredM.run (do
      let r ← withSegment fun e => { base e with edgeInformation := #[(e, { info with invertedRight := true })],
                                                 isWestOfInitialLayer := true }
      FinalSplineBendpointsCalculator.calculateControlPoints (cfgOf .sloppy) r.1 ⟨0⟩
      return r)
  -- hand: west of the initial layer → no edge-node spacing: center x = 100 + 23 = 123
  checkChain "hand: inverted EAST target (even when sloppy)" (ar.edge e).bendPoints
    #[⟨100, 10⟩, ⟨123, 10⟩, ⟨123, 50⟩, ⟨100, 50⟩]
  let ((_, e), ar) ← LayeredM.run (do
      let r ← withSegment fun e => { base e with inverseOrder := true }
      FinalSplineBendpointsCalculator.calculateControlPoints (cfgOf .conservative) r.1 ⟨0⟩
      return r)
  checkChain "hand: inverseOrder reverses the conservative points" (ar.edge e).bendPoints
    #[⟨140, 50⟩, ⟨133, 50⟩, ⟨133, 10⟩, ⟨100, 10⟩]
  let ((_, e), ar) ← LayeredM.run (do
      let r ← withSegment fun e => { base e with edgeInformation := #[] }
      FinalSplineBendpointsCalculator.calculateControlPoints (cfgOf .conservative) r.1 ⟨0⟩
      return r)
  checkEq "edge without EdgeInformation is skipped (Rust)" (ar.edge e).bendPoints.size 0
  let ((_, e), ar) ← LayeredM.run (do
      let r ← withSegment fun e => { base e with isStraight := true, centerControlPointY := 7 }
      FinalSplineBendpointsCalculator.calculateControlPoints (cfgOf .conservative) r.1 ⟨0⟩
      return r)
  checkChain "hand: straight segment: halfway point (120, 7)" (ar.edge e).bendPoints #[⟨120, 7⟩]
  -- insertStraighteningControlPoints: (0,0) (2,3) (10,10), EAST source, WEST target
  -- hand: v = (5,0), v2 = (2,3) → (2,0); end: w = (-5, 6e-16), w2 = (-8,-7) → (-5, 6e-16) + (10,10)
  checkChain "hand: straightening control points"
    (FinalSplineBendpointsCalculator.insertStraighteningControlPoints #[⟨0, 0⟩, ⟨2, 3⟩, ⟨10, 10⟩] .east .west)
    #[⟨0, 0⟩, ⟨2, 0⟩, ⟨2, 3⟩, ⟨5, 10⟩, ⟨10, 10⟩] 1e-12
  checkFloat "absMin picks the smaller magnitude" (FinalSplineBendpointsCalculator.absMin (-1.0) 2.0) (-1.0)
  checkFloat "absMin ties → second" (FinalSplineBendpointsCalculator.absMin (-2.0) 2.0) 2.0

def sloppyTests : Suite := suite "layered.intermediate.FinalSplineBendpointsCalculator.sloppy" do
  -- layer L0: A (10,0) 20×20 with east port (20,10) → abs (30,10); C (0,30) 40×20 below it.
  -- A → B (L1) and A → B2 (L1): out-degree of A 2, in-degree of B 1.
  let ((pa, e, a), ar) ← LayeredM.run (do
      let g ← graphWith
      let l0 ← addLayer g
      let l1 ← addLayer g
      let a ← LayeredM.createNode g { position := ⟨10, 0⟩, size := ⟨20, 20⟩ }
      LayeredM.setNodeLayer a (some l0)
      let c ← LayeredM.createNode g { position := ⟨0, 30⟩, size := ⟨40, 20⟩ }
      LayeredM.setNodeLayer c (some l0)
      let b ← LayeredM.createNode g { position := ⟨100, 200⟩, size := ⟨20, 20⟩ }
      LayeredM.setNodeLayer b (some l1)
      let b2 ← LayeredM.createNode g { position := ⟨100, 300⟩, size := ⟨20, 20⟩ }
      LayeredM.setNodeLayer b2 (some l1)
      let pa ← addPort a .east ⟨20, 10⟩
      let pb ← addPort b .west ⟨0, 10⟩
      let pb2 ← addPort b2 .west ⟨0, 10⟩
      let e ← connect pa pb
      let _ ← connect pa pb2
      FinalSplineBendpointsCalculator.indexNodesPerLayer g
      return (pa, e, a))
  checkEq "hand: ids of L0" (ar.node a).id 0
  -- hand: (yT + yS)/2 + (yT - yS)·0.4·sign(2 - 1) = 115 + 200·0.4 = 195
  checkFloat "hand: computeSloppyCenterY (out 2 > in 1)" (FinalSplineBendpointsCalculator.computeSloppyCenterY ar e 15.0 215.0) 195.0
  -- downwards from A: the neighbour C (box [0,40]×[30,50]) is crossed by (30,10)–(35,100)
  check "hand: shortcut blocked by the crossed neighbour"
    (!FinalSplineBendpointsCalculator.shortCut ar (some pa) true true ⟨30, 10⟩ ⟨35, 100⟩)
  check "hand: shortcut when the line passes the neighbour"
    (FinalSplineBendpointsCalculator.shortCut ar (some pa) true true ⟨30, 10⟩ ⟨100, 12⟩)
  check "upwards from the first node: nothing to check → shortcut"
    (FinalSplineBendpointsCalculator.shortCut ar (some pa) true false ⟨30, 10⟩ ⟨35, 100⟩)
  check "abnormal node: no shortcut" (!FinalSplineBendpointsCalculator.shortCut ar (some pa) false true ⟨30, 10⟩ ⟨100, 12⟩)
  check "no port: no shortcut" (!FinalSplineBendpointsCalculator.shortCut ar none true true ⟨30, 10⟩ ⟨100, 12⟩)
  -- sloppy points with a blocked source: hand: segment box 30..100, start y 10, end y 210; centre x 65;
  -- center y = 110 + 200·0.4·sign(2 - 1) = 190; v1 (30,10), v2 (65,190), v3 (100,210):
  -- approx centre = (v1 + 2 v2 + v3)/4 = (65, 150); (30,10)–(65,150) crosses C's top edge at x 35
  -- → source pair (30,10) (65,10); target: B is the first node of L1 and the edge points down → shortcut
  let seg : SplineSegment := { edges := #[e], boundingBox := ⟨30, 0, 70, 210⟩, sourcePort := some pa,
                               targetPort := (ar.edge e).target }
  let info : EdgeInformation := { startY := 10, endY := 210, normalSourceNode := true, normalTargetNode := true }
  checkChain "hand: sloppy with a blocked source"
    (FinalSplineBendpointsCalculator.sloppyControlPoints ar e seg info) #[⟨30, 10⟩, ⟨65, 10⟩]
  -- segmentAllowsSloppyRouting: only with post-compaction; A ends at 30, layer width 0 (unset) →
  -- threshold 0 - 20/2 = -10 → a segment starting at 30 (distance 0 > -10) is refused
  let initial : SplineSegment := { seg with initialSegment := true, sourceNode := some a }
  check "no compaction: sloppy allowed" (FinalSplineBendpointsCalculator.segmentAllowsSloppyRouting (cfgOf .sloppy) ar initial)
  check "hand: compaction + initial segment beyond the threshold: refused"
    (!FinalSplineBendpointsCalculator.segmentAllowsSloppyRouting (cfgOf .sloppy .left) ar initial)
  check "compaction without initial/last flags: allowed"
    (FinalSplineBendpointsCalculator.segmentAllowsSloppyRouting (cfgOf .sloppy .left) ar seg)

-- start edges, errors, registration ---------------------------------------------------------------------

def processTests : Suite := suite "layered.intermediate.FinalSplineBendpointsCalculator.process" do
  -- self loops and edges without SPLINE_ROUTE_START are not start edges
  let ((loopEdge, plain), ar) ← LayeredM.run (do
      let (g, a, _, e) ← twoNodes 0.0
      let p1 ← addPort a .north ⟨5, 0⟩
      let p2 ← addPort a .north ⟨15, 0⟩
      let loopEdge ← connect p1 p2
      LayeredM.modifyEdge loopEdge fun x => { x with
        internal := { x.internal with splineRouteStart := some #[⟨0⟩], splineEdgeChain := #[loopEdge] } }
      LayeredM.modifyEdge e fun x => { x with bendPoints := #[⟨1, 1⟩] }
      FinalSplineBendpointsCalculator.processor.process g ProgressMonitor.null
      return (loopEdge, e))
  checkEq "self loop is no start edge (route kept)" ((ar.edge loopEdge).internal.splineRouteStart.map (·.size)) (some 1)
  checkChain "edge without SPLINE_ROUTE_START untouched" (ar.edge plain).bendPoints #[⟨1, 1⟩]
  -- the chain's surviving edge starts at a long-edge dummy: IllegalArgumentException
  checkThrows "non-qualified start node throws" (do
    let _ ← LayeredM.run (do
      let (g, a, _, e) ← twoNodes 0.0
      LayeredM.modifyNode a fun n => { n with type := .longEdge }
      LayeredM.modifyEdge e fun x => { x with internal := { x.internal with splineRouteStart := some #[], splineEdgeChain := #[e] } }
      FinalSplineBendpointsCalculator.processor.process g ProgressMonitor.null)
    pure ())
  check "registered" (← IntermediateProcessorStrategy.isAvailable .finalSplineBendpointsCalculator)
  checkEq "name" (← IntermediateProcessorStrategy.create .finalSplineBendpointsCalculator).name "FinalSplineBendpointsCalculator"

def suites : Array Suite :=
  #[singleEdgeTests, longEdgeTests, hyperedgeTests, northSouthTests, variantTests, sloppyTests, processTests]

end Tests.Layered.IntermediateFinalSpline
