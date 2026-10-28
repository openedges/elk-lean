import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.P5Edges.Splines
/-! Tests of `org.eclipse.elk.alg.layered.p5edges.splines`: `SplinesMath`, `Rectangle`, `NubSpline`,
`NubsSelfLoop`, the `SplineSegment` data and `SplineEdgeRouter` on hand-built graphs. Expected values
are derived by hand ("hand: …"); the only elk-rs test (`p5_edges/spline_routing_test.rs`
`spline_edge_routing_no_panic`, a pipeline run with a 1:2 hyperedge) is replayed on a hand-built
two-layer graph with its assertions made explicit. -/
namespace Tests.Layered.P5Splines

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Core.Util Elk.Core.Alg Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate Elk.Alg.Layered.P5Edges
  Elk.Alg.Layered.P5Edges.Splines

/-- Approximate `KVector` comparison. -/
def checkVec (name : String) (actual expected : KVector) (eps : Float := 1e-9) : TestM Unit :=
  report name ((actual.x - expected.x).abs <= eps && (actual.y - expected.y).abs <= eps)
    s!"expected {expected}, got {actual}"

/-- Approximate comparison of vector chains. -/
def checkChain (name : String) (actual expected : Array KVector) (eps : Float := 1e-9) : TestM Unit :=
  let ok := actual.size == expected.size &&
    (actual.zip expected).all fun (a, e) => (a.x - e.x).abs <= eps && (a.y - e.y).abs <= eps
  report name ok s!"expected {expected}, got {actual}"

def isError {α : Type} (r : Except String α) : Bool :=
  match r with
  | .error _ => true
  | .ok _ => false

-- graph building helpers --------------------------------------------------------------------------

def addLayer (g : LGraphId) : LayeredM LayerId := do
  let l ← LayeredM.createLayer g
  LayeredM.modifyGraph g fun x => { x with layers := x.layers.push l }
  return l

def addNode (g : LGraphId) (l : LayerId) (y : Float) (size : KVector := ⟨20.0, 20.0⟩)
    (type : NodeType := .normal) : LayeredM LNodeId := do
  let n ← LayeredM.createNode g { position := ⟨0.0, y⟩, size := size, type := type }
  LayeredM.setNodeLayer n (some l)
  return n

def addPort (n : LNodeId) (side : PortSide) (pos : KVector) : LayeredM LPortId := do
  let p ← LayeredM.createPort { side := side, position := pos }
  LayeredM.setPortNode p (some n)
  return p

def connect (s t : LPortId) : LayeredM LEdgeId := do
  let e ← LayeredM.createEdge
  LayeredM.setEdgeSource e (some s)
  LayeredM.setEdgeTarget e (some t)
  return e

def graphWith (mode : Option SplineRoutingMode := none) (nodeNodeBetweenLayers : Option Float := none) :
    LayeredM LGraphId := do
  let mut props : PropertyMap := {}
  if let some m := mode then props := props.set LayeredOptions.EDGE_ROUTING_SPLINES_MODE m
  if let some s := nodeNodeBetweenLayers then props := props.set LayeredOptions.SPACING_NODE_NODE_BETWEEN_LAYERS s
  LayeredM.createGraph { props := props }

/-- Two layers `A | B`, one edge from `A`'s east port (abs y 10) to `B`'s west port (abs y `10 + dy`). -/
def twoNodes (dy : Float) (mode : Option SplineRoutingMode := none) (nn : Option Float := none) :
    LayeredM (LGraphId × LNodeId × LNodeId × LEdgeId) := do
  let g ← graphWith mode nn
  let l0 ← addLayer g
  let l1 ← addLayer g
  let a ← addNode g l0 0.0
  let b ← addNode g l1 dy
  let pa ← addPort a .east ⟨20.0, 10.0⟩
  let pb ← addPort b .west ⟨0.0, 10.0⟩
  let e ← connect pa pb
  return (g, a, b, e)

-- SplinesMath --------------------------------------------------------------------------------------

def mathTests : Suite := suite "layered.p5splines.SplinesMath" do
  checkFloat "portSideToDirection NORTH = 3π/2" (SplinesMath.portSideToDirection .north) (3.0 * Float.pi / 2.0)
  checkFloat "portSideToDirection EAST = 0" (SplinesMath.portSideToDirection .east) 0.0
  checkFloat "portSideToDirection SOUTH = π/2" (SplinesMath.portSideToDirection .south) (Float.pi / 2.0)
  checkFloat "portSideToDirection WEST = π" (SplinesMath.portSideToDirection .west) Float.pi
  check "isBetween 5 in [0,10]" (SplinesMath.isBetween 5.0 0.0 10.0)
  check "isBetween 5 in [10,0] (either order)" (SplinesMath.isBetween 5.0 10.0 0.0)
  check "isBetween boundary within epsilon" (SplinesMath.isBetween 10.000000001 0.0 10.0)
  check "isBetween 11 not in [0,10]" (!SplinesMath.isBetween 11.0 0.0 10.0)
  check "isBetweenInt 5 0 10" (SplinesMath.isBetweenInt 5 0 10)
  check "hand: isBetweenInt -1 0 10 (value < b0 → b1 ≤ value)" (!SplinesMath.isBetweenInt (-1) 0 10)
  check "hand: isBetweenInt 5 10 0" (SplinesMath.isBetweenInt 5 10 0)
  -- hand: divisor = (0-2)(2-0) - (0-2)(0-2) = -8, first = 0, second = -4 → x = y = (0 - 8) / -8 = 1
  checkEq "hand: intersect of the diagonals of [0,2]²" (SplinesMath.intersect ⟨0, 0⟩ ⟨2, 2⟩ ⟨0, 2⟩ ⟨2, 0⟩) (some ⟨1, 1⟩)
  check "intersect of parallel lines is none" (SplinesMath.intersect ⟨0, 0⟩ ⟨1, 1⟩ ⟨0, 1⟩ ⟨1, 2⟩).isNone
  match SplinesMath.intersectDir ⟨0, 0⟩ ⟨1, 5⟩ 0.0 (Float.pi / 2.0) with
  | some p => checkVec "hand: intersectDir horizontal through (0,0) × vertical through (1,5) = (1,0)" p ⟨1, 0⟩
  | none => check "intersectDir horizontal × vertical exists" false
  checkFloat "innerAngleVec (1,0),(0,1) = π/2" (SplinesMath.innerAngleVec ⟨1, 0⟩ ⟨0, 1⟩) (Float.pi / 2.0)
  -- hand: |3π/2 - 0| % π = π/2 (exact fmod)
  checkFloat "innerAngle 3π/2 0 = π/2" (SplinesMath.innerAngle SplinesMath.THREE_HALF_PI 0.0) SplinesMath.HALF_PI 1e-15
  checkFloat "fmodRust 7.5 2 = 1.5" (SplinesMath.fmodRust 7.5 2.0) 1.5
  checkFloat "fmodRust -7.5 2 = -1.5 (sign of dividend)" (SplinesMath.fmodRust (-7.5) 2.0) (-1.5)
  checkFloat "fmodRust 1 3 = 1" (SplinesMath.fmodRust 1.0 3.0) 1.0
  check "fmodRust x 0 = NaN" (SplinesMath.fmodRust 1.0 0.0).isNaN
  -- hand: point (3,4): angle asin(4/5), not > π/2 → cos(angle) · 5 = 3
  checkFloat "hand: lengthToOrthogonal 0 (3,4) = 3" (SplinesMath.lengthToOrthogonal 0.0 ⟨3, 4⟩) 3.0
  -- Rust `{:.1}`: exact value, ties to even
  checkEq "formatFixed1 0.15 (= 0.1499…)" (SplinesMath.formatFixed1 0.15) "0.1"
  checkEq "formatFixed1 0.25 (tie → even)" (SplinesMath.formatFixed1 0.25) "0.2"
  checkEq "formatFixed1 1.05 (= 1.0500…04)" (SplinesMath.formatFixed1 1.05) "1.1"
  checkEq "formatFixed1 -3.25 (tie → even)" (SplinesMath.formatFixed1 (-3.25)) "-3.2"
  checkEq "formatFixed1 -0.0" (SplinesMath.formatFixed1 (-0.0)) "-0.0"
  checkEq "formatFixed1 12" (SplinesMath.formatFixed1 12.0) "12.0"
  checkEq "convertKVectorToString" (SplinesMath.convertKVectorToString (some ⟨1.25, -3.0⟩)) "(1.2,-3.0)"
  checkEq "convertKVectorToString null" (SplinesMath.convertKVectorToString none) "(null)"
  checkEq "convertKVectorSliceToString" (SplinesMath.convertKVectorSliceToString #[⟨1, 2⟩, ⟨3.5, 4⟩]) "(1.0,2.0), (3.5,4.0)"
  checkEq "convertKVectorSliceToString empty" (SplinesMath.convertKVectorSliceToString #[]) "(null)"
  -- node 30×20, port at (25,8) with anchor (5,2) → anchor at (30,10)
  let ((n, p), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let n ← LayeredM.createNode g { size := ⟨30, 20⟩, margin := { top := 1, right := 2, bottom := 3, left := 4 } }
      let p ← LayeredM.createPort { side := .east, position := ⟨25, 8⟩, anchor := ⟨5, 2⟩ }
      LayeredM.setPortNode p (some n)
      return (n, p))
  checkFloat "hand: distPortToNodeEdge NORTH = -10" (SplinesMath.distPortToNodeEdge a p .north) (-10.0)
  checkFloat "hand: distPortToNodeEdge EAST = 0" (SplinesMath.distPortToNodeEdge a p .east) 0.0
  checkFloat "hand: distPortToNodeEdge SOUTH = 10" (SplinesMath.distPortToNodeEdge a p .south) 10.0
  checkFloat "hand: distPortToNodeEdge WEST = -30" (SplinesMath.distPortToNodeEdge a p .west) (-30.0)
  checkFloat "getMarginOnPortSide EAST = right" (SplinesMath.getMarginOnPortSide a n .east) 2.0
  checkFloat "getMarginOnPortSide WEST = left" (SplinesMath.getMarginOnPortSide a n .west) 4.0

-- Rectangle ----------------------------------------------------------------------------------------

def rectangleTests : Suite := suite "layered.p5splines.Rectangle" do
  match Rectangle.new 0 0 10 5 with
  | .ok r =>
    checkFloat "new: width" r.width 10.0
    checkFloat "new: height" r.height 5.0
    checkFloat "getFromPortSide EAST = right" (r.getFromPortSide .east) 10.0
    checkFloat "getFromPortSide SOUTH = bottom" (r.getFromPortSide .south) 5.0
    let e := r.enlarge 1.0
    check "enlarge 1" (e.top == -1.0 && e.left == -1.0 && e.right == 11.0 && e.bottom == 6.0)
  | .error _ => check "Rectangle.new 0 0 10 5 succeeds" false
  check "new rejects top > bottom" (isError (Rectangle.new 0 5 10 0))
  check "new rejects left > right" (isError (Rectangle.new 10 0 0 5))
  match Rectangle.fromVectors #[⟨1, 2⟩, ⟨5, -1⟩, ⟨3, 7⟩] with
  | .ok r => check "hand: fromVectors bounds (top -1, bottom 7, left 1, right 5)" (r == ⟨-1, 7, 1, 5⟩)
  | .error _ => check "fromVectors succeeds" false
  check "fromVectors rejects an empty list" (isError (Rectangle.fromVectors #[]))
  match Rectangle.fromVectorsIter #[⟨1, 2⟩, ⟨5, -1⟩] with
  | .ok r => check "fromVectorsIter = fromVectors" (r == ⟨-1, 2, 1, 5⟩)
  | .error _ => check "fromVectorsIter succeeds" false
  let s := Rectangle.fromShape ⟨2, 3⟩ ⟨4, 5⟩
  check "hand: fromShape (2,3)+(4,5) → top 3 bottom 8 left 2 right 6" (s == ⟨3, 8, 2, 6⟩)
  check "unionVector extends" ((s.unionVector ⟨10, 0⟩) == ⟨0, 8, 2, 10⟩)
  check "unionShape" ((Rectangle.fromVector ⟨0, 0⟩).unionShape ⟨2, 3⟩ ⟨4, 5⟩ == ⟨0, 8, 0, 6⟩)
  check "union of two rectangles" (Rectangle.union s (Rectangle.fromVector ⟨-1, 9⟩) == ⟨3, 9, -1, 6⟩)
  check "unionAll rejects an empty list" (isError (Rectangle.unionAll #[]))
  -- hand: rect [-3, 9] × [-2, 12] around a 10×8 shape → margins top 3, left 2, bottom 1, right 2
  let m := (⟨-3, 9, -2, 12⟩ : Rectangle).toNodeMargins ⟨10, 8⟩
  check "hand: toNodeMargins" (m.top == 3.0 && m.left == 2.0 && m.bottom == 1.0 && m.right == 2.0)
  checkEq "toString (Rust Display, {:.1})" (toString (⟨2, 4, 1.25, 3⟩ : Rectangle)) "[top= 2.0,left= 1.2,bottom= 4.0,right= 3.0]"

-- NubSpline ----------------------------------------------------------------------------------------

def cubic : Array KVector := #[⟨0, 0⟩, ⟨4, 8⟩, ⟨8, 8⟩, ⟨12, 0⟩]
def quintPoints : Array KVector := #[⟨0, 0⟩, ⟨10, 0⟩, ⟨20, 10⟩, ⟨30, 20⟩, ⟨40, 20⟩]

def nubSplineTests : Suite := suite "layered.p5splines.NubSpline" do
  check "dimension 0 rejected" (isError (NubSpline.new true 0 cubic))
  check "no control points rejected" (isError (NubSpline.new true 3 #[]))
  match NubSpline.new true 3 cubic with
  | .error e => check s!"cubic spline: {e}" false
  | .ok s =>
    -- hand: 4 CPs, dim 3, clamped → knots [0,0,0,1,1,1]; polar (0,0,0) (0,0,1) (0,1,1) (1,1,1)
    checkEq "hand: clamped cubic knot vector" s.getKnotVector #[0, 0, 0, 1, 1, 1]
    checkEq "hand: polar coordinates" (s.controlPoints.map (·.polarCoordinate)) #[#[0, 0, 0], #[0, 0, 1], #[0, 1, 1], #[1, 1, 1]]
    checkEq "getDim" s.getDim 3
    checkEq "already Bezier: inner control points" s.getBezierCPDefault.1 #[⟨4, 8⟩, ⟨8, 8⟩]
    checkEq "getBezierCP with source and target" (s.getBezierCP true true).1 cubic
    checkEq "getPointOnCurve 0 = first CP" (s.getPointOnCurve 0.0 false).1 ⟨0, 0⟩
    checkEq "getPointOnCurve 1 = last CP" (s.getPointOnCurve 1.0 false).1 ⟨12, 0⟩
    match s.getOuterBox with
    | .ok (box, s') =>
      check "hand: outer box of the control points" (box == ⟨0, 8, 0, 12⟩)
      check "outer box cached" s'.outerBox.isSome
    | .error _ => check "getOuterBox succeeds" false
    -- hand: derivative = 3 (P_{i+1} - P_i), dim 2, knots [0,0,1,1]
    let d := NubSpline.generateDerivedNubs s
    checkEq "hand: derived control points" d.getControlPoints #[⟨12, 24⟩, ⟨12, 0⟩, ⟨12, -24⟩]
    checkEq "derived dim" d.getDim 2
    checkEq "derived knots" d.getKnotVector #[0, 0, 1, 1]
    -- hand: the second CP has y = 0 → t = mean of its polar coordinates (0,1) = 0.5
    checkFloat "hand: zero of the derivative's y control polygon" (NubSpline.getZeroYOfControlPolygon d) 0.5
    let inv := NubSpline.generateInvertedNubs s
    checkEq "inverted: reversed control points" inv.getControlPoints cubic.reverse
    checkEq "inverted: mirrored knots" inv.getKnotVector #[0, 0, 0, 1, 1, 1]
    -- Rust quirk: insert_knot passes knot_index - 1 → 0.25 is inserted before the last 0 (Java: after)
    let k := s.insertKnot 0.25 1
    checkEq "hand: insertKnot 0.25 (Rust index)" k.getKnotVector #[0, 0, 0.25, 0, 1, 1, 1]
    -- hand: de Boor with t = 0.25: A_i = 0.75 P_i + 0.25 P_{i+1}
    checkEq "hand: insertKnot 0.25 control points" k.getControlPoints #[⟨0, 0⟩, ⟨1, 2⟩, ⟨5, 8⟩, ⟨9, 6⟩, ⟨12, 0⟩]
  match NubSpline.new true 3 quintPoints with
  | .error e => check s!"5-point spline: {e}" false
  | .ok s =>
    checkEq "hand: 5 CPs → knots [0,0,0,0.5,1,1,1]" s.getKnotVector #[0, 0, 0, 0.5, 1, 1, 1]
    -- hand: Bezier conversion inserts 0.5 twice: Q1 = (P1+P2)/2 = (15,5), Q2 = (P2+P3)/2 = (25,15),
    -- R = (Q1+Q2)/2 = (20,10)
    let (bezier, s') := s.getBezierCPDefault
    checkEq "hand: Bezier control points (without source/target)" bezier #[⟨10, 0⟩, ⟨15, 5⟩, ⟨20, 10⟩, ⟨25, 15⟩, ⟨30, 20⟩]
    checkEq "hand: Bezier knot vector" s'.getKnotVector #[0, 0, 0, 0.5, 0.5, 0.5, 1, 1, 1]
    check "toBezier sets isBezier and isClamped" (s'.isBezier && s'.isClamped)
    checkEq "hand: getPointOnCurve 0.5 = R" (s.getPointOnCurve 0.5 false).1 ⟨20, 10⟩
    checkEq "getPointOnCurve without modify keeps the spline" (s.getPointOnCurve 0.5 false).2.getKnotVector s.getKnotVector
    checkEq "getPointOnCurve 1 = last CP" (s.getPointOnCurve 1.0 false).1 ⟨40, 20⟩
  match NubSpline.new true 3 #[⟨1, 1⟩, ⟨2, 2⟩] with
  | .ok s =>
    checkEq "padding: first CP repeated up to dim + 1 points" s.getControlPointsSize 4
    checkEq "padding: Bezier inner points" s.getBezierCPDefault.1 #[⟨1, 1⟩, ⟨1, 1⟩]
  | .error e => check s!"padded spline: {e}" false
  let nice := NubSpline.generateNiceCurve
  checkEq "generateNiceCurve: 21 control points" nice.getControlPointsSize 21
  checkEq "hand: generateNiceCurve first CP = 5·(5.5,23) - (50,80)" (nice.getControlPoint 0) ⟨-22.5, 35⟩
  checkEq "generateNiceCurve knot vector size = 21 + 3 - 1" nice.getKnotVector.size 23

-- NubsSelfLoop --------------------------------------------------------------------------------------

def selfLoopTests : Suite := suite "layered.p5splines.NubsSelfLoop" do
  let ((ps, pt, pe, pso), a) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      let n ← LayeredM.createNode g { size := ⟨20, 20⟩ }
      let ps ← addPort n .north ⟨5, 0⟩
      let pt ← addPort n .north ⟨15, 0⟩
      let pe ← addPort n .east ⟨20, 5⟩
      let pso ← addPort n .south ⟨10, 20⟩
      return (ps, pt, pe, pso))
  match NubsSelfLoop.createSideSelfLoop a ps pt 10.0 with
  | .ok l =>
    -- hand: direction 3π/2 → first (5,-10), third (15,-10), mid (-5,0), second (10,-10) + 5·(0,-1) = (10,-15)
    checkChain "hand: side self loop control points" l.spline.getControlPoints
      #[⟨5, 0⟩, ⟨5, -10⟩, ⟨10, -15⟩, ⟨15, -10⟩, ⟨15, 0⟩]
    -- hand: Bezier of 5 CPs: (C1+C2)/2 = (7.5,-12.5), center (10,-12.5), (C2+C3)/2 = (12.5,-12.5)
    checkChain "hand: side self loop Bezier points" (l.spline.getBezierCP true true).1
      #[⟨5, 0⟩, ⟨5, -10⟩, ⟨7.5, -12.5⟩, ⟨10, -12.5⟩, ⟨12.5, -12.5⟩, ⟨15, -10⟩, ⟨15, 0⟩]
    checkEq "first label position defaults to (0,0)" l.firstLabelPosition ⟨0, 0⟩
  | .error e => check s!"side self loop: {e}" false
  match NubsSelfLoop.createCornerSelfLoop a pe pso 4.0 6.0 with
  | .ok l =>
    -- hand: first = (20 + 1.3·4, 5) = (25.2, 5); third = (10, 20 + 1.3·6) = (10, 27.8);
    -- EAST source: x = 2(20+4) - (25.2+10)/2 = 30.4; SOUTH target: y = 2(20+6) - (27.8+5)/2 = 35.6
    checkChain "hand: corner self loop control points" l.spline.getControlPoints
      #[⟨20, 5⟩, ⟨25.2, 5⟩, ⟨30.4, 35.6⟩, ⟨10, 27.8⟩, ⟨10, 20⟩]
  | .error e => check s!"corner self loop: {e}" false
  check "across self loop needs two corner points" (isError (NubsSelfLoop.createAcrossSelfLoop a ps pt ⟨0, 0⟩ #[⟨1, 1⟩] ⟨2, 2⟩))
  match NubsSelfLoop.createAcrossSelfLoop a ps pso ⟨5, -5⟩ #[⟨-5, -5⟩, ⟨-5, 25⟩] ⟨10, 25⟩ with
  | .ok l => checkEq "hand: across self loop: middle CP = corner midpoint (-5,10)" (l.spline.getControlPoint 3) ⟨-5, 10⟩
  | .error e => check s!"across self loop: {e}" false
  check "three side self loop needs three corner points" (isError (NubsSelfLoop.createThreeSideSelfLoop a ps pt ⟨0, 0⟩ #[] ⟨2, 2⟩))
  match NubsSelfLoop.createFourSideSelfLoop a ps pt ⟨5, -5⟩ #[⟨-5, -5⟩, ⟨-5, 25⟩, ⟨25, 25⟩, ⟨25, -5⟩] ⟨15, -5⟩ with
  | .ok l => checkEq "four side self loop: 8 control points" l.spline.getControlPointsSize 8
  | .error e => check s!"four side self loop: {e}" false

-- SplineSegment data ---------------------------------------------------------------------------------

def segmentTests : Suite := suite "layered.p5splines.SplineSegment" do
  -- hand: source 10 below targets [40,80]: center 25, top 0.1·25 + 0.9·10 = 11.5, bottom 2.5 + 36 = 38.5
  let s := ({} : SplineSegment).setRelevantPositions 10.0 40.0 80.0
  checkFloat "hand: box y = min(source, targetMin)" s.boundingBox.y 10.0
  checkFloat "hand: box height = max(source, targetMax) - y" s.boundingBox.height 70.0
  checkFloat "hand: center control point" s.centerControlPointY 25.0
  checkFloat "hand: hyperedge top" s.hyperEdgeTopYPos 11.5
  checkFloat "hand: hyperedge bottom" s.hyperEdgeBottomYPos 38.5
  -- source above the targets: center (50 + 10)/2 = 30, top 3 + 9 = 12, bottom 3 + 45 = 48
  let s2 := ({} : SplineSegment).setRelevantPositions 50.0 10.0 10.0
  checkFloat "hand: upward segment top" s2.hyperEdgeTopYPos 12.0
  checkFloat "hand: upward segment bottom" s2.hyperEdgeBottomYPos 48.0
  check "single edge is no hyperedge" (!({ edges := #[⟨0⟩] } : SplineSegment).isHyperEdge)
  check "two edges form a hyperedge" ({ edges := #[⟨0⟩, ⟨1⟩] } : SplineSegment).isHyperEdge
  checkEq "insertUniquePort keeps order, no duplicates"
    (SplineSegment.insertUniquePort (SplineSegment.insertUniquePort #[⟨3⟩, ⟨1⟩] ⟨3⟩) ⟨2⟩) #[⟨3⟩, ⟨1⟩, ⟨2⟩]
  check "isStraight below 0.2" (SplineEdgeRouter.isStraight 10.0 10.19)
  check "isStraight not at exactly 0.2" (!SplineEdgeRouter.isStraight 0.0 0.2)
  check "hand: isStraight 10 10.2 (10.2 - 10 = 0.19999999999999929 < 0.2)" (SplineEdgeRouter.isStraight 10.0 10.2)
  check "isNormalNode: BREAKING_POINT" (SplineEdgeRouter.isNormalNode { type := .breakingPoint })
  check "isNormalNode: not LONG_EDGE" (!SplineEdgeRouter.isNormalNode { type := .longEdge })
  check "isQualifiedAsStartingNode: NORTH_SOUTH_PORT" (SplineEdgeRouter.isQualifiedAsStartingNode { type := .northSouthPort })
  check "isQualifiedAsStartingNode: not LABEL" (!SplineEdgeRouter.isQualifiedAsStartingNode { type := .label })

-- SplineEdgeRouter -----------------------------------------------------------------------------------

def routerStraightTests : Suite := suite "layered.p5splines.SplineEdgeRouter.straight" do
  -- hand: gap 0 (before L0): nothing; gap 1: one straight segment → nodeNodeSpacing 20 → B.x = 20 + 20;
  -- gap 2 (after L1): nothing → width 40 + 20
  let ((g, a, b, e, st), ar) ← LayeredM.run (do
      let (g, a, b, e) ← twoNodes 0.0
      let st ← SplineEdgeRouter.route g
      return (g, a, b, e, st))
  checkFloat "A.x = 0" (ar.node a).position.x 0.0
  checkFloat "hand: B.x = 20 + nodeNodeSpacing" (ar.node b).position.x 40.0
  checkFloat "hand: graph width = 60" (ar.graph g).size.x 60.0
  checkEq "one segment" st.segments.size 1
  let s := st.segments[0]!
  check "segment is straight" s.isStraight
  checkFloat "segment box x = end of L0" s.boundingBox.x 20.0
  checkFloat "segment box width = gap" s.boundingBox.width 20.0
  checkFloat "center control point y" s.centerControlPointY 10.0 1e-12
  check "initial and last segment" (s.initialSegment && s.lastSegment)
  checkEq "source node" s.sourceNode (some a)
  checkEq "target node" s.targetNode (some b)
  checkEq "SPLINE_ROUTE_START of the start edge" st.routeStarts #[(e, #[⟨0⟩])]
  checkEq "SPLINE_EDGE_CHAIN of the start edge" (ar.edge e).internal.splineEdgeChain #[e]
  checkEq "edge information: start y" ((s.edgeInformationOf e).map (·.startY)) (some 10.0)
  check "edge information: normal ends, not inverted" (((s.edgeInformationOf e).map fun i =>
    i.normalSourceNode && i.normalTargetNode && !i.invertedLeft && !i.invertedRight).getD false)
  -- the phase itself (monitor + name) on a fresh graph
  let (_, ar2) ← LayeredM.run (do
      let (g, _, _, _) ← twoNodes 0.0
      SplineEdgeRouter.phase.process g ProgressMonitor.null
      return g)
  checkFloat "phase.process sets the width too" (ar2.graph ⟨0⟩).size.x 60.0
  -- empty graph
  let (_, ar3) ← LayeredM.run (do
      let g ← LayeredM.createGraph { size := ⟨99, 5⟩ }
      SplineEdgeRouter.phase.process g ProgressMonitor.null)
  checkFloat "no layers: width 0" (ar3.graph ⟨0⟩).size.x 0.0

def routerModeTests : Suite := suite "layered.p5splines.SplineEdgeRouter.modes" do
  -- hand: A port y 10, B port y 500 (dy 490): one slot → increment edgeNode + edgeNode = 20;
  -- SLOPPY: 0.2 · min(10/20, 1) · 490 = 49 > 20 → B.x = 20 + 49
  let ((g, _, b, _), ar) ← LayeredM.run (do
      let r ← twoNodes 490.0 (some .sloppy)
      let _ ← SplineEdgeRouter.route r.1
      return r)
  checkFloat "hand: SLOPPY gap = sloppy spacing 49" (ar.node b).position.x 69.0
  checkFloat "hand: SLOPPY width" (ar.graph g).size.x 89.0
  let ((g2, _, b2, _), ar2) ← LayeredM.run (do
      let r ← twoNodes 490.0 (some .conservative)
      let _ ← SplineEdgeRouter.route r.1
      return r)
  checkFloat "hand: CONSERVATIVE gap = 2 · edgeNodeSpacing" (ar2.node b2).position.x 40.0
  checkFloat "hand: CONSERVATIVE width" (ar2.graph g2).size.x 60.0
  -- hand: nodeNodeSpacing 50 > increment 20 → xDelta (50 - 20)/2 = 15 and gap 50
  let ((_, _, b3, _, st3), ar3) ← LayeredM.run (do
      let (g, a, b, e) ← twoNodes 50.0 (some .conservative) (some 50.0)
      let st ← SplineEdgeRouter.route g
      return (g, a, b, e, st))
  checkFloat "hand: gap widened to nodeNodeSpacing" (ar3.node b3).position.x 70.0
  checkFloat "hand: xDelta = (50 - 20) / 2" st3.segments[0]!.xDelta 15.0
  check "non-straight segment" (!st3.segments[0]!.isStraight)
  checkEq "rank 0" st3.segments[0]!.rank 0

def routerCrossingTests : Suite := suite "layered.p5splines.SplineEdgeRouter.crossing" do
  -- A(10) → D(50) and C(50) → B(10): both segments span [12, 48], no port lies strictly inside the
  -- other's range → counters 0/0 → zero-weight dependencies S1→S0 and S0→S1. Both are sinks:
  -- S0 mark 1, S1 mark 0 → shifted 4 and 3 → S0→S1 points left and is dropped (weight 0).
  -- Ranks: S1 = 0, S0 = 1 → two slots: 10 + 10 + 10 = 30 → L1 at 20 + 30.
  let ((g, nodes, st), ar) ← LayeredM.run (do
      let g ← graphWith
      let l0 ← addLayer g
      let l1 ← addLayer g
      let a ← addNode g l0 0.0
      let c ← addNode g l0 40.0
      let b ← addNode g l1 0.0
      let d ← addNode g l1 40.0
      let pa ← addPort a .east ⟨20, 10⟩
      let pc ← addPort c .east ⟨20, 10⟩
      let pb ← addPort b .west ⟨0, 10⟩
      let pd ← addPort d .west ⟨0, 10⟩
      let _ ← connect pa pd
      let _ ← connect pc pb
      let st ← SplineEdgeRouter.route g
      return (g, #[a, b, c, d], st))
  checkEq "two segments" st.segments.size 2
  let s0 := st.segments[0]!
  let s1 := st.segments[1]!
  checkFloat "hand: S0 top" s0.hyperEdgeTopYPos 12.0
  checkFloat "hand: S1 bottom" s1.hyperEdgeBottomYPos 48.0
  checkEq "hand: S0 rank" s0.rank 1
  checkEq "hand: S1 rank" s1.rank 0
  checkEq "hand: S0 → S1 dropped" s0.outgoing.size 0
  checkEq "hand: S1 → S0 kept" s1.outgoing.size 1
  checkEq "hand: S0 incoming S1 → S0" s0.incoming.size 1
  checkEq "hand: final marks (S0, S1)" (s0.mark, s1.mark) (4, 3)
  checkEq "two zero-weight dependencies created" (st.dependencies.map (·.weight)) #[0, 0]
  checkFloat "hand: B.x = 20 + 30" (ar.node nodes[1]!).position.x 50.0
  checkFloat "hand: D.x = 20 + 30" (ar.node nodes[3]!).position.x 50.0
  checkFloat "hand: width = 50 + 20" (ar.graph g).size.x 70.0
  checkEq "two start edges" st.routeStarts.size 2

def routerHyperedgeTests : Suite := suite "layered.p5splines.SplineEdgeRouter.hyperedge" do
  -- spline_routing_test.rs `spline_edge_routing_no_panic`: A's east port feeds B and C (1:2 hyperedge)
  -- hand: pA y 10, pB y 40, pC y 80 → both edges go down → one hyperedge segment
  -- box y 10, height 70; center 25; top 11.5; bottom 38.5; rank 0 → one slot → L1 at 20 + 20
  let ((g, a, b, c, es, st), ar) ← LayeredM.run (do
      let g ← graphWith
      let l0 ← addLayer g
      let l1 ← addLayer g
      let a ← addNode g l0 0.0
      let b ← addNode g l1 30.0
      let c ← addNode g l1 70.0
      let pa ← addPort a .east ⟨20, 10⟩
      let pb ← addPort b .west ⟨0, 10⟩
      let pc ← addPort c .west ⟨0, 10⟩
      let e1 ← connect pa pb
      let e2 ← connect pa pc
      let st ← SplineEdgeRouter.route g
      return (g, a, b, c, #[e1, e2], st))
  checkEq "spline_edge_routing_no_panic: one hyperedge segment" st.segments.size 1
  let h := st.segments[0]!
  check "hyperedge" (h.isHyperEdge && !h.isStraight)
  checkEq "hyperedge edges in order" h.edges es
  checkEq "left ports = [pA]" h.leftPorts.size 1
  checkEq "right ports = [pB, pC]" h.rightPorts.size 2
  checkFloat "hand: hyperedge box y" h.boundingBox.y 10.0
  checkFloat "hand: hyperedge box height" h.boundingBox.height 70.0
  checkFloat "hand: hyperedge center" h.centerControlPointY 25.0
  checkFloat "hand: hyperedge top" h.hyperEdgeTopYPos 11.5
  checkFloat "hand: hyperedge bottom" h.hyperEdgeBottomYPos 38.5
  checkEq "edge information of e2: end y" ((h.edgeInformationOf es[1]!).map (·.endY)) (some 80.0)
  checkEq "both edges start a route through the same segment" st.routeStarts #[(es[0]!, #[⟨0⟩]), (es[1]!, #[⟨0⟩])]
  checkEq "target port of the shared segment = last processed edge's" h.targetPort ((ar.edge es[1]!).target)
  checkEq "target node from the first edge" h.targetNode (some b)
  checkEq "source node" h.sourceNode (some a)
  checkFloat "hand: B.x" (ar.node b).position.x 40.0
  checkFloat "hand: C.x" (ar.node c).position.x 40.0
  checkFloat "hand: width" (ar.graph g).size.x 60.0
  -- configuration (Rust static tables)
  let base := SplineEdgeRouter.layoutProcessorConfiguration EnumSet.empty
  checkEq "baseline: FINAL_SPLINE_BENDPOINTS_CALCULATOR after P5" (base.processorsAfter .p5EdgeRouting) #[.finalSplineBendpointsCalculator]
  checkEq "baseline: INVERTED_PORT_PROCESSOR before P3" (base.processorsBefore .p3NodeOrdering) #[.invertedPortProcessor]
  let loops := SplineEdgeRouter.layoutProcessorConfiguration (EnumSet.singleton GraphProperties.selfLoops)
  checkEq "self loops: before P4" (loops.processorsBefore .p4NodePlacement) #[.selfLoopPortRestorer, .selfLoopRouter]
  checkEq "self loops: after P5" (loops.processorsAfter .p5EdgeRouting) #[.finalSplineBendpointsCalculator, .selfLoopPostprocessor]
  checkEq "self loops: before P1" (loops.processorsBefore .p1CycleBreaking) #[.selfLoopPreprocessor]
  let ns := SplineEdgeRouter.layoutProcessorConfiguration (EnumSet.of #[GraphProperties.northSouthPorts, .endLabels])
  checkEq "north/south ports + end labels: before P5" (ns.processorsBefore .p5EdgeRouting) #[.northSouthPortPostprocessor]
  checkEq "north/south ports + end labels: before P4" (ns.processorsBefore .p4NodePlacement) #[.labelSideSelector, .endLabelPreprocessor]
  -- registration under EdgeRouting.SPLINES
  let phase ← (EdgeRouterFactory.factoryFor .splines).create
  checkEq "EdgeRouterFactory SPLINES → SplineEdgeRouter" phase.name "SplineEdgeRouter"

def routerLongEdgeTests : Suite := suite "layered.p5splines.SplineEdgeRouter.longEdge" do
  -- A(10) → dummy D(30) → B(60): e1 continues as e2 (successor of an edge into a dummy).
  -- hand: gap 1: slot 1 → 20 → L1 at 40 (D has width 0); gap 2: slot 1 → L2 at 40 + 20 = 60; width 80
  let ((g, nodes, e1, e2, st), ar) ← LayeredM.run (do
      let g ← graphWith (some .conservative)
      let l0 ← addLayer g
      let l1 ← addLayer g
      let l2 ← addLayer g
      let a ← addNode g l0 0.0
      let d ← addNode g l1 30.0 ⟨0, 0⟩ .longEdge
      let b ← addNode g l2 50.0
      let pa ← addPort a .east ⟨20, 10⟩
      let pdIn ← addPort d .west ⟨0, 0⟩
      let pdOut ← addPort d .east ⟨0, 0⟩
      let pb ← addPort b .west ⟨0, 10⟩
      let e1 ← connect pa pdIn
      let e2 ← connect pdOut pb
      -- a surviving edge set by an earlier processor must stay untouched
      LayeredM.modifyEdge e1 fun x => { x with internal := { x.internal with splineSurvivingEdge := some e1 } }
      let st ← SplineEdgeRouter.route g
      return (g, #[a, d, b], e1, e2, st))
  checkEq "two segments" st.segments.size 2
  checkEq "SPLINE_EDGE_CHAIN on the start edge" (ar.edge e1).internal.splineEdgeChain #[e1, e2]
  checkEq "no chain on the dummy's edge" (ar.edge e2).internal.splineEdgeChain #[]
  checkEq "SPLINE_SURVIVING_EDGE untouched" (ar.edge e1).internal.splineSurvivingEdge (some e1)
  checkEq "only e1 starts a route" st.routeStarts #[(e1, #[⟨0⟩, ⟨1⟩])]
  check "successor e1 → e2" (st.successingEdge[e1]? == some e2)
  let s0 := st.segments[0]!
  let s1 := st.segments[1]!
  check "first segment initial, not last" (s0.initialSegment && !s0.lastSegment)
  check "second segment last, not initial" (s1.lastSegment && !s1.initialSegment)
  checkEq "spline source node" s0.sourceNode (some nodes[0]!)
  checkEq "spline target node" s1.targetNode (some nodes[2]!)
  check "EdgeInformation: dummy target is not normal" (!(((s0.edgeInformationOf e1).map (·.normalTargetNode)).getD true))
  checkFloat "hand: D.x" (ar.node nodes[1]!).position.x 40.0
  checkFloat "hand: B.x" (ar.node nodes[2]!).position.x 60.0
  checkFloat "hand: width" (ar.graph g).size.x 80.0
  checkFloat "hand: second segment box x" s1.boundingBox.x 40.0
  checkFloat "hand: second segment box width" s1.boundingBox.width 20.0

def routerCycleTests : Suite := suite "layered.p5splines.SplineEdgeRouter.cycles" do
  -- hand: 3-cycle S0→S1→S2→S0 (weights 1): no sources/sinks, all outflows 0 →
  -- Random(0).nextInt(3) = 0 picks S0 (mark 4); S1 becomes a source, S2 a sink; S2 mark 2, S1 mark 5;
  -- shift: S2 → 2 + 4 = 6. S2→S0 points left → reversed to S0→S2.
  -- Ranks: S0 0, S1 1, S2 2 (S2 is a rightward target with the max rank; moving left keeps them).
  let ((g, st), ar) ← LayeredM.run (do
      let g ← LayeredM.createGraph
      LayeredM.modifyGraph g fun x => { x with internal := { x.internal with random := some (Random.ofInt 0) } }
      let body : SplineEdgeRouter.RouterM Unit := do
        let s0 ← SplineEdgeRouter.addSegment {}
        let s1 ← SplineEdgeRouter.addSegment {}
        let s2 ← SplineEdgeRouter.addSegment {}
        -- `new Dependency(S0, S1, 1)`, `(S1, S2, 1)`, `(S2, S0, 1)`; no segment has left ports
        let deps := SplineEdgeRouter.GapDeps.ofTable 3 0 #[0, 1, 2] #[1, 2, 0] #[1, 1, 1]
        SplineEdgeRouter.rankGap g #[s0, s1, s2] deps #[true, true, true]
      let ((), st) ← body.run { random := Random.ofInt 0, sharedRandom := true }
      return (g, st))
  let marks := st.segments.map (·.mark)
  checkEq "hand: marks after cycle breaking" marks #[4, 5, 6]
  let d2 := st.dependencies[2]!
  checkEq "hand: S2→S0 reversed to S0→S2" (d2.source, d2.target) ((⟨0⟩ : SplineSegmentId), (⟨2⟩ : SplineSegmentId))
  checkEq "S0 outgoing: S0→S1, reversed S0→S2" (st.segments[0]!.outgoing.map (·.idx)) #[0, 2]
  checkEq "S2 incoming: S1→S2, reversed S0→S2" (st.segments[2]!.incoming.map (·.idx)) #[1, 2]
  checkEq "hand: ranks" (st.segments.map (·.rank)) #[0, 1, 2]
  check "graph RANDOM advanced by one nextInt(3)" ((ar.graph g).internal.random == some ((Random.ofInt 0).nextInt 3).2)

def routerDenseTests : Suite := suite "layered.p5splines.SplineEdgeRouter.dense" do
  -- 4 layers × 5 nodes; every node's east port feeds the nodes (i + 1) % 5 and (i + 3) % 5 of the next
  -- layer, every third edge is flagged REVERSED: hyperedges, crossings and dependency cycles.
  let ((g, layers, edges, st), ar) ← LayeredM.run (do
      let g ← graphWith
      LayeredM.modifyGraph g fun x => { x with internal := { x.internal with random := some (Random.ofInt 7) } }
      let mut layers : Array (Array LNodeId) := #[]
      let mut westPorts : Array (Array LPortId) := #[]
      let mut eastPorts : Array (Array LPortId) := #[]
      for li in [0:4] do
        let l ← addLayer g
        let mut ns := #[]
        let mut ws := #[]
        let mut es := #[]
        for i in [0:5] do
          let n ← addNode g l (30.0 * i.toFloat + 7.0 * li.toFloat)
          ws := ws.push (← addPort n .west ⟨0, 10⟩)
          es := es.push (← addPort n .east ⟨20, 5.0 + i.toFloat⟩)
          ns := ns.push n
        layers := layers.push ns
        westPorts := westPorts.push ws
        eastPorts := eastPorts.push es
      let mut edges := #[]
      for li in [0:3] do
        for i in [0:5] do
          for k in #[1, 3] do
            let e ← connect eastPorts[li]![i]! westPorts[li + 1]![(i + k) % 5]!
            if edges.size % 3 == 0 then
              LayeredM.modifyEdge e fun x => { x with internal := { x.internal with reversed := true } }
            edges := edges.push e
      let st ← SplineEdgeRouter.route g
      return (g, layers, edges, st))
  let xs := layers.map fun ns => ns.map fun n => (ar.node n).position.x
  check "nodes of a layer share their x" (xs.all fun row => row.all (· == row[0]!))
  check "layers move right" ((List.range 3).all fun i => xs[i]![0]! < xs[i + 1]![0]!)
  checkEq "every edge starts a route" st.routeStarts.size edges.size
  check "every edge is covered by exactly one segment of its gap"
    (edges.all fun e => (st.segments.filter (·.edges.contains e)).size == 1)
  check "ranks are non-negative" (st.segments.all (·.rank >= 0))
  check "dependencies point from lower to higher rank" (st.segments.all fun seg =>
    seg.outgoing.all fun d => seg.rank < st.segments[(st.dependencies[d.idx]!).target.idx]!.rank)
  check "width = last layer end" ((ar.graph g).size.x == xs[3]![0]! + 20.0)

def routerCycleGuardTests : Suite := suite "layered.p5splines.SplineEdgeRouter.successorCycle" do
  -- N (NORTH_SOUTH_PORT dummy, L0) → D (LONG_EDGE dummy, L1) via e1, and D's west port back to N's
  -- east port via e2: successor(e1) = e2 and successor(e2) = e1. Rust/Java never terminate here;
  -- the Lean walk stops at the repeated edge.
  let ((e1, e2, st), ar) ← LayeredM.run (do
      let g ← graphWith
      let l0 ← addLayer g
      let l1 ← addLayer g
      let n ← addNode g l0 0.0 ⟨0, 0⟩ .northSouthPort
      let d ← addNode g l1 20.0 ⟨0, 0⟩ .longEdge
      let pn ← addPort n .east ⟨0, 0⟩
      let pd ← addPort d .west ⟨0, 0⟩
      let e1 ← connect pn pd
      let e2 ← connect pd pn
      let st ← SplineEdgeRouter.route g
      return (e1, e2, st))
  checkEq "edge chain stops at the repeated edge" (ar.edge e1).internal.splineEdgeChain #[e1, e2]
  checkEq "spline path stops at the repeated edge" (st.routeStarts.map (·.2.size)) #[2]
  check "successors form the cycle" (st.successingEdge[e1]? == some e2 && st.successingEdge[e2]? == some e1)

def suites : Array Suite :=
  #[mathTests, rectangleTests, nubSplineTests, selfLoopTests, segmentTests, routerStraightTests,
    routerModeTests, routerCrossingTests, routerHyperedgeTests, routerLongEdgeTests, routerCycleTests,
    routerDenseTests, routerCycleGuardTests]

end Tests.Layered.P5Splines
