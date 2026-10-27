import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Graph.Transform
import Elk.Alg.Layered.Intermediate
/-!
# Tests for `org.eclipse.elk.alg.layered.graph.transform.ElkGraphLayoutTransferrer`

Each scenario builds an `ElkGraph` and a matching layered arena by hand (origins, positions,
sizes, bend points, external port dummies), runs `ElkGraphLayoutTransferrer.applyLayout` and
checks the ElkGraph. Expected values are derived by hand from elk-rs
`elk_graph_layout_transferrer.rs` ("hand: …" in the check names).

Main scenario (root `R` at `(0, 0)`, root `LGraph` `G0`: offset `(2, 3)`, padding
top/right/bottom/left `5/6/7/8`, size `200 × 100`, `EXTERNAL_PORTS`; base offset
`(2 + 8, 3 + 5) = (10, 8)`). Nested graph `G1` of `H`: offset `(1, 1)`, padding `4` → offset
`(5, 5)`.
-/
namespace Tests.Layered.Transform

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Options Elk.Alg.Layered.Graph Elk.Alg.Layered.Options
open Elk.Alg.Layered.Graph.Transform Elk.Alg.Layered.Intermediate

def checkVec (name : String) (actual expected : KVector) : TestM Unit := do
  checkFloat s!"{name} x" actual.x expected.x
  checkFloat s!"{name} y" actual.y expected.y

/-- Ids of the main scenario's ElkGraph. -/
structure ElkIds where
  root : NodeId
  a : NodeId
  b : NodeId
  h : NodeId
  i : NodeId
  pA : PortId
  pB : PortId
  pH : PortId
  pR : PortId
  lA : LabelId
  lB : LabelId
  lB2 : LabelId
  lpA : LabelId
  lpB : LabelId
  leAB : LabelId
  leRA : LabelId
  eAB : EdgeId
  eRA : EdgeId
  eF : EdgeId
  eIB : EdgeId
  eHI : EdgeId
  eIF : EdgeId
  eYo : EdgeId
  sAB0 : SectionId
  sAB1 : SectionId
  sYo : SectionId

private def named (n : NodeId) (ident : String) (w h : Float := 0) : ElkM Unit :=
  ElkM.modifyNode n fun x => { x with identifier := some ident, width := w, height := h }

private def namedPort (p : PortId) (ident : String) (w h : Float := 0) : ElkM Unit :=
  ElkM.modifyPort p fun x => { x with identifier := some ident, width := w, height := h }

private def edgeBetween (container : NodeId) (s t : ConnectableId) : ElkM EdgeId := do
  let e ← ElkM.createEdge (some container)
  ElkM.addEdgeSource e s
  ElkM.addEdgeTarget e t
  return e

/-- The ElkGraph: root `R` (port `pR`) with children `A` (port `pA`), `B` (port `pB`) and the
hierarchical `H` (port `pH`, child `I`); edges `eAB` (pA→pB, two old sections, label), `eRA`
(pR→A, label), `eF` (A→pB, no layered edge), `eIB` (I→pB, hierarchical), `eYo` (pA→pA,
`INSIDE_SELF_LOOPS_YO` with geometry) in `R`, and `eHI` (pH→I), `eIF` (I→pH, no layered edge)
in `H`. -/
def buildElk : ElkM ElkIds := do
  let root ← ElkM.createNode none
  named root "R"
  ElkM.setNodeProp root CoreOptions.NODE_SIZE_OPTIONS (EnumSet.of #[SizeOptions.computePadding])
  ElkM.setNodeProp root CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.portLabels])
  ElkM.setNodeProp root CoreOptions.EDGE_ROUTING EdgeRouting.orthogonal
  let a ← ElkM.createNode (some root)
  named a "A" 1 1
  ElkM.setNodeProp a CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.minimumSize])
  let b ← ElkM.createNode (some root)
  named b "B" 30 20
  let h ← ElkM.createNode (some root)
  named h "H"
  ElkM.setNodeProp h CoreOptions.EDGE_ROUTING EdgeRouting.splines
  let i ← ElkM.createNode (some h)
  named i "I" 15 10
  let pA ← ElkM.createPort (some a)
  namedPort pA "pA"
  let pB ← ElkM.createPort (some b)
  namedPort pB "pB"
  let pH ← ElkM.createPort (some h)
  namedPort pH "pH"
  let pR ← ElkM.createPort (some root)
  namedPort pR "pR" 6 4
  let lA ← ElkM.createLabel (some (.node a)) "A"
  let lB ← ElkM.createLabel (some (.node b)) "B"
  ElkM.modifyLabel lB fun l => { l with x := 77, y := 88 }
  let lB2 ← ElkM.createLabel (some (.node b)) "B2"
  let lpA ← ElkM.createLabel (some (.port pA)) "pa"
  let lpB ← ElkM.createLabel (some (.port pB)) "pb"
  ElkM.modifyLabel lpB fun l => { l with x := 66, y := 66 }
  let eAB ← edgeBetween root (.port pA) (.port pB)
  ElkM.modifyEdge eAB fun e => { e with props := e.props.set CoreOptions.EDGE_ROUTING EdgeRouting.splines }
  let sAB0 ← ElkM.createSection (some eAB)
  ElkM.modifySection sAB0 fun s => { s with identifier := some "s0", startX := 9, endY := 9, bendPoints := #[⟨1, 1⟩] }
  let sAB1 ← ElkM.createSection (some eAB)
  let leAB ← ElkM.createLabel (some (.edge eAB)) "e"
  let eRA ← edgeBetween root (.port pR) (.node a)
  let leRA ← ElkM.createLabel (some (.edge eRA)) "r"
  let eF ← edgeBetween root (.node a) (.port pB)
  let eIB ← edgeBetween root (.node i) (.port pB)
  let eYo ← edgeBetween root (.port pA) (.port pA)
  ElkM.modifyEdge eYo fun e => { e with props := e.props.set CoreOptions.INSIDE_SELF_LOOPS_YO true }
  let sYo ← ElkM.createSection (some eYo)
  ElkM.modifySection sYo fun s => { s with startX := 1, startY := 1, endX := 2, endY := 2 }
  let eHI ← edgeBetween h (.port pH) (.node i)
  let eIF ← edgeBetween h (.node i) (.port pH)
  return { root, a, b, h, i, pA, pB, pH, pR, lA, lB, lB2, lpA, lpB, leAB, leRA,
           eAB, eRA, eF, eIB, eHI, eIF, eYo, sAB0, sAB1, sYo }

private def originNode (n : NodeId) : LNodeInternals := { origin := some (.elkNode n) }
private def originPort (p : PortId) : LPortInternals := { origin := some (.elkPort p) }
private def originEdge (e : EdgeId) : LEdgeInternals := { origin := some (.elkEdge e) }
private def originLabel (l : LabelId) : LLabelInternals := { origin := some (.elkLabel l) }

private def addPort (n : LNodeId) (p : LPort) : LayeredM LPortId := do
  let id ← LayeredM.createPort p
  LayeredM.setPortNode id (some n)
  return id

private def connect (e : LEdge) (s t : LPortId) : LayeredM LEdgeId := do
  let id ← LayeredM.createEdge e
  LayeredM.setEdgeSource id (some s)
  LayeredM.setEdgeTarget id (some t)
  return id

/-- The layered arena of the main scenario; returns the root graph. -/
def buildArena (e : ElkIds) : LayeredM LGraphId := do
  let g0 ← LayeredM.createGraph
    { padding := { top := 5, right := 6, bottom := 7, left := 8 }, offset := ⟨2, 3⟩, size := ⟨200, 100⟩ }
  LayeredM.modifyGraph g0 fun g =>
    { g with internal := { g.internal with graphProperties := EnumSet.of #[GraphProperties.externalPorts] } }
  let l0 ← LayeredM.createLayer g0
  let l1 ← LayeredM.createLayer g0
  LayeredM.modifyGraph g0 fun g => { g with layers := #[l0, l1] }
  -- external port dummy of `pR` (west side) and `A`
  let ld ← LayeredM.createNode g0
    { position := ⟨0, 50⟩, type := .externalPort, internal := { origin := some (.elkPort e.pR), extPortSide := .west } }
  let lpD ← addPort ld { side := .east }
  let la ← LayeredM.createNode g0 { position := ⟨20, 30⟩, size := ⟨40, 25⟩, internal := originNode e.a }
  LayeredM.setNodeProp la LayeredOptions.LAYERING_LAYER_ID 0
  LayeredM.setNodeProp la LayeredOptions.CROSSING_MINIMIZATION_POSITION_ID 1
  LayeredM.setNodeProp la LayeredOptions.NODE_LABELS_PLACEMENT (EnumSet.of #[NodeLabelPlacement.hCenter, .vTop])
  let lpA ← addPort la
    { position := ⟨40, 10⟩, size := ⟨4, 6⟩, side := .east, anchor := ⟨4, 3⟩, internal := originPort e.pA }
  let lpA2 ← addPort la { position := ⟨0, 12⟩, side := .west }
  let llpA ← LayeredM.createLabel "pa" { position := ⟨5, -12⟩, size := ⟨10, 8⟩, internal := originLabel e.lpA }
  LayeredM.modifyPort lpA fun p => { p with labels := p.labels.push llpA }
  let llA ← LayeredM.createLabel "A" { position := ⟨3, -15⟩, size := ⟨12, 9⟩, internal := originLabel e.lA }
  LayeredM.modifyNode la fun n => { n with labels := n.labels.push llA }
  -- `B` with fixed port label placement
  let lb ← LayeredM.createNode g0 { position := ⟨120, 40⟩, size := ⟨31, 21⟩, internal := originNode e.b }
  LayeredM.setNodeProp lb CoreOptions.PORT_LABELS_PLACEMENT EnumSet.noneOf
  let lpB ← addPort lb
    { position := ⟨-4, 7⟩, size := ⟨4, 6⟩, side := .west, anchor := ⟨0, 3⟩, internal := originPort e.pB }
  let llpB ← LayeredM.createLabel "pb" { position := ⟨1, 1⟩, size := ⟨1, 1⟩, internal := originLabel e.lpB }
  LayeredM.modifyPort lpB fun p => { p with labels := p.labels.push llpB }
  let llB ← LayeredM.createLabel "B" { position := ⟨1, 2⟩, size := ⟨3, 4⟩, internal := originLabel e.lB }
  let llB2 ← LayeredM.createLabel "B2"
    { position := ⟨2, 3⟩, size := ⟨4, 5⟩, internal := originLabel e.lB2,
      props := ({} : PropertyMap).set LayeredOptions.NODE_LABELS_PLACEMENT (EnumSet.of #[NodeLabelPlacement.inside]) }
  LayeredM.modifyNode lb fun n => { n with labels := #[llB, llB2] }
  LayeredM.setNodeLayer ld (some l0)
  LayeredM.setNodeLayer la (some l0)
  LayeredM.setNodeLayer lb (some l1)
  -- hierarchical `H` (layerless) with nested graph `G1`
  let lh ← LayeredM.createNode g0 { position := ⟨60, 70⟩, size := ⟨50, 40⟩, internal := originNode e.h }
  let lpH ← addPort lh
    { position := ⟨-5, 15⟩, size := ⟨5, 5⟩, side := .west, anchor := ⟨0, 2.5⟩, internal := originPort e.pH }
  LayeredM.modifyGraph g0 fun g => { g with layerlessNodes := #[lh] }
  let g1 ← LayeredM.createGraph
    { padding := ElkPadding.ofAny 4, offset := ⟨1, 1⟩, size := ⟨40, 30⟩, parentNode := some lh }
  LayeredM.modifyNode lh fun n => { n with nestedGraph := some g1 }
  let li ← LayeredM.createNode g1 { position := ⟨10, 5⟩, size := ⟨15, 10⟩, internal := originNode e.i }
  let lpI ← addPort li { position := ⟨0, 5⟩, side := .west }
  let lpI2 ← addPort li { position := ⟨15, 5⟩, side := .east }
  -- nested external port dummy of `pH`: must not be moved (graph has a parent node)
  let ldh ← LayeredM.createNode g1
    { position := ⟨-3, 8⟩, type := .externalPort, internal := { origin := some (.elkPort e.pH), extPortSide := .west } }
  LayeredM.modifyGraph g1 fun g => { g with layerlessNodes := #[li, ldh] }
  -- edges
  let leAB ← connect { bendPoints := #[⟨80, 43⟩, ⟨100, 50⟩], internal := originEdge e.eAB } lpA lpB
  LayeredM.setEdgeProp leAB LayeredOptions.JUNCTION_POINTS #[⟨90, 45⟩]
  let lleAB ← LayeredM.createLabel "e"
    { position := ⟨85, 30⟩, size := ⟨20, 10⟩, internal := originLabel e.leAB,
      props := ({} : PropertyMap).set LabelDummySwitcher.INCLUDE_LABEL true }
  LayeredM.modifyEdge leAB fun x => { x with labels := #[lleAB] }
  let _ ← connect { internal := originEdge e.eYo } lpA lpA
  let leRA ← connect { internal := originEdge e.eRA } lpD lpA2
  let lleRA ← LayeredM.createLabel "r" { size := ⟨5, 5⟩, internal := originLabel e.leRA }
  LayeredM.modifyEdge leRA fun x => { x with labels := #[lleRA] }
  let _ ← connect { bendPoints := #[⟨2, 10⟩], internal := originEdge e.eHI } lpH lpI
  let _ ← connect
    { internal := { origin := some (.elkEdge e.eIB), coordinateSystemOrigin := some g0, targetOffset := some ⟨-70, -78⟩ } }
    lpI2 lpB
  return g0

def mainScenario : Suite := suite "layered.transform.transferrer" do
  let (e, g) ← ElkM.run buildElk {}
  let (g0, arena) ← LayeredM.run (buildArena e)
  let ((), g) ← ElkM.run (ElkGraphLayoutTransferrer.applyLayout arena {} g0 e.root) g
  -- root graph: computed padding, resize to the actual size, constraints
  let rootPadding := (g.node e.root).props.get CoreOptions.PADDING |>.getD {}
  checkFloat "hand: COMPUTE_PADDING top = lpadding.top 5" rootPadding.top 5
  checkFloat "hand: COMPUTE_PADDING right 6" rootPadding.right 6
  checkFloat "hand: COMPUTE_PADDING bottom 7" rootPadding.bottom 7
  checkFloat "hand: COMPUTE_PADDING left 8" rootPadding.left 8
  checkFloat "hand: root width = 200 + 8 + 6" (g.node e.root).width 214
  checkFloat "hand: root height = 100 + 5 + 7" (g.node e.root).height 112
  check "hand: EXTERNAL_PORTS → PORT_CONSTRAINTS = FIXED_POS"
    ((g.node e.root).props.get? CoreOptions.PORT_CONSTRAINTS == some PortConstraints.fixedPos)
  check "hand: root size constraints reset to {PORT_LABELS}"
    ((g.node e.root).props.get? CoreOptions.NODE_SIZE_CONSTRAINTS == some (EnumSet.of #[SizeConstraint.portLabels]))
  -- nodes
  checkVec "hand: A position = (20, 30) + (10, 8)" (g.node e.a).position ⟨30, 38⟩
  checkVec "hand: A size set (MINIMUM_SIZE constraint)" (g.node e.a).size ⟨40, 25⟩
  checkEq "hand: A layer id" ((g.node e.a).props.get? LayeredOptions.LAYERING_LAYER_ID) (some 0)
  checkEq "hand: A position id" ((g.node e.a).props.get? LayeredOptions.CROSSING_MINIMIZATION_POSITION_ID) (some 1)
  checkVec "hand: B position = (120, 40) + (10, 8)" (g.node e.b).position ⟨130, 48⟩
  checkVec "hand: B size kept (no constraints)" (g.node e.b).size ⟨30, 20⟩
  checkEq "hand: B layer id default -1" ((g.node e.b).props.get? LayeredOptions.LAYERING_LAYER_ID) (some (-1))
  checkVec "hand: H position = (60, 70) + (10, 8)" (g.node e.h).position ⟨70, 78⟩
  checkVec "hand: H size set (nested graph)" (g.node e.h).size ⟨50, 40⟩
  check "hand: nested H constraints reset to fixed (no resize)"
    ((g.node e.h).props.get? CoreOptions.NODE_SIZE_CONSTRAINTS == some SizeConstraint.fixed)
  checkVec "hand: I position = (10, 5) + nested offset (1 + 4, 1 + 4)" (g.node e.i).position ⟨15, 10⟩
  -- ports
  checkVec "hand: pA position" (g.port e.pA).position ⟨40, 10⟩
  checkVec "hand: pA size" (g.port e.pA).size ⟨4, 6⟩
  check "hand: pA PORT_SIDE east" ((g.port e.pA).props.get? CoreOptions.PORT_SIDE == some PortSide.east)
  checkVec "hand: pB position" (g.port e.pB).position ⟨-4, 7⟩
  checkVec "hand: pH position from LH's port, not moved as nested dummy" (g.port e.pH).position ⟨-5, 15⟩
  checkVec "hand: root external port pR west = (-6 - 0, 50 + 5 + 3 - 4/2)" (g.port e.pR).position ⟨-6, 56⟩
  -- labels
  checkVec "hand: node label lA (node has label placement)" (g.label e.lA).position ⟨3, -15⟩
  checkVec "hand: node label lA size" (g.label e.lA).size ⟨12, 9⟩
  checkVec "hand: node label lB untouched (no placement)" (g.label e.lB).position ⟨77, 88⟩
  checkVec "hand: node label lB2 (label has placement)" (g.label e.lB2).position ⟨2, 3⟩
  checkVec "hand: port label lpA (placement outside)" (g.label e.lpA).position ⟨5, -12⟩
  checkVec "hand: port label lpB untouched (fixed placement)" (g.label e.lpB).position ⟨66, 66⟩
  -- edge eAB: first section reused, bend points, label, junction points, routing
  let eAB := g.edge e.eAB
  checkEq "hand: eAB keeps only its first section" eAB.sections #[e.sAB0]
  check "hand: dropped section detached" ((g.edgeSection e.sAB1).parent.isNone)
  let sAB := g.edgeSection e.sAB0
  checkEq "hand: reused section keeps identifier" sAB.identifier (some "s0")
  checkVec "hand: eAB start = (20 + 40 + 4, 30 + 10 + 3) + (10, 8)" sAB.startPoint ⟨74, 51⟩
  checkEq "hand: eAB bend count" sAB.bendPoints.size 2
  checkVec "hand: eAB bend 0 = (80, 43) + (10, 8)" (sAB.bendPoints[0]?.getD {}) ⟨90, 51⟩
  checkVec "hand: eAB bend 1 = (100, 50) + (10, 8)" (sAB.bendPoints[1]?.getD {}) ⟨110, 58⟩
  checkVec "hand: eAB end = (120 - 4 + 0, 40 + 7 + 3) + (10, 8)" sAB.endPoint ⟨126, 58⟩
  checkEq "hand: eAB incoming shape" sAB.incomingShape (some (.port e.pA))
  checkEq "hand: eAB outgoing shape" sAB.outgoingShape (some (.port e.pB))
  let jp := eAB.props.get? CoreOptions.JUNCTION_POINTS |>.getD #[]
  checkEq "hand: eAB junction point count" jp.size 1
  checkVec "hand: eAB junction (90, 45) + (10, 8)" (jp[0]?.getD {}) ⟨100, 53⟩
  check "hand: non-spline routing removes EDGE_ROUTING" (!eAB.props.has CoreOptions.EDGE_ROUTING)
  checkVec "hand: eAB label = (85, 30) + (10, 8)" (g.label e.leAB).position ⟨95, 38⟩
  checkVec "hand: eAB label size" (g.label e.leAB).size ⟨20, 10⟩
  checkEq "hand: INCLUDE_LABEL true copied" ((g.label e.leAB).props.get? LabelDummySwitcher.INCLUDE_LABEL) (some true)
  -- edge eRA from the moved external port dummy (x = -(8 + 0 + 2))
  let sRA := g.edgeSection ((g.edge e.eRA).sections[0]?.getD default)
  checkEq "hand: eRA got one section" (g.edge e.eRA).sections.size 1
  checkVec "hand: eRA start = moved dummy (-10, 50) + (10, 8)" sRA.startPoint ⟨0, 58⟩
  checkVec "hand: eRA end = (20 + 0, 30 + 12) + (10, 8)" sRA.endPoint ⟨30, 50⟩
  checkEq "hand: eRA outgoing shape is node A" sRA.outgoingShape (some (.node e.a))
  checkEq "hand: eRA default junction points stored empty"
    (((g.edge e.eRA).props.get? CoreOptions.JUNCTION_POINTS).map (·.size)) (some 0)
  checkVec "hand: eRA label = (0, 0) + (10, 8)" (g.label e.leRA).position ⟨10, 8⟩
  checkEq "hand: INCLUDE_LABEL default false stored" ((g.label e.leRA).props.get? LabelDummySwitcher.INCLUDE_LABEL) (some false)
  -- INSIDE_SELF_LOOPS_YO edge with geometry is untouched
  checkEq "hand: eYo section kept" (g.edge e.eYo).sections #[e.sYo]
  checkVec "hand: eYo start untouched" (g.edgeSection e.sYo).startPoint ⟨1, 1⟩
  check "hand: eYo junction points untouched" (!(g.edge e.eYo).props.has CoreOptions.JUNCTION_POINTS)
  -- fallback section for eF (no layered edge): A center → pB west anchor
  checkEq "hand: eF fallback section created" (g.edge e.eF).sections.size 1
  let sF := g.edgeSection ((g.edge e.eF).sections[0]?.getD default)
  checkVec "hand: eF start = A (30, 38) + (40/2, 25/2)" sF.startPoint ⟨50, 50.5⟩
  checkVec "hand: eF end = B (130, 48) + pB (-4, 7 + 6/2)" sF.endPoint ⟨126, 58⟩
  checkEq "hand: eF no bend points" sF.bendPoints.size 0
  checkEq "hand: eF incoming shape" sF.incomingShape (some (.node e.a))
  -- descendant edge eHI from H's port into its nested graph (processed with offset (5, 5))
  let sHI := g.edgeSection ((g.edge e.eHI).sections[0]?.getD default)
  checkVec "hand: eHI start = pH (-5, 15) + anchor (0, 2.5) - (5, 5) + (5, 5)" sHI.startPoint ⟨-5, 17.5⟩
  checkVec "hand: eHI bend = (2, 10) + (5, 5)" (sHI.bendPoints[0]?.getD {}) ⟨7, 15⟩
  checkVec "hand: eHI end = I (10, 5) + (0, 5) + (5, 5)" sHI.endPoint ⟨15, 15⟩
  check "hand: eHI SPLINES from H" ((g.edge e.eHI).props.get? CoreOptions.EDGE_ROUTING == some EdgeRouting.splines)
  -- hierarchical offset: (5, 5) + LH (60, 70) + G0 offset (2, 3) + padding (8, 5) = (75, 83)
  checkEq "hand: eIB reuses its earlier fallback section" (g.edge e.eIB).sections.size 1
  let sIB := g.edgeSection ((g.edge e.eIB).sections[0]?.getD default)
  checkVec "hand: eIB start = (10 + 15, 5 + 5) + (75, 83)" sIB.startPoint ⟨100, 93⟩
  checkVec "hand: eIB end = (116 - 70, 50 - 78) + (75, 83)" sIB.endPoint ⟨121, 55⟩
  -- recursive fallback inside H: I center → container port pH (inner border)
  let sIF := g.edgeSection ((g.edge e.eIF).sections[0]?.getD default)
  checkVec "hand: eIF start = I (85, 88) + (7.5, 5) - H (70, 78)" sIF.startPoint ⟨22.5, 15⟩
  checkVec "hand: eIF end = pH (-5 + 5, 15 + 2.5) on container" sIF.endPoint ⟨0, 17.5⟩

/-- Content alignment with an explicit minimum size, fixed graph size, network simplex sizes. -/
def contentAlignmentScenario : Suite := suite "layered.transform.contentAlignment" do
  -- explicit minimum (100, 80), H_RIGHT/V_BOTTOM, fixed graph size
  let ((root, n), g) ← ElkM.run (do
      let root ← ElkM.createNode none
      named root "R2" 33 44
      ElkM.setNodeProp root CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE true
      let n ← ElkM.createNode (some root)
      named n "N" 1 1
      return (root, n)) {}
  let (lg, arena) ← LayeredM.run (do
      let lg ← LayeredM.createGraph { padding := ElkPadding.ofAny 10, size := ⟨40, 20⟩ }
      LayeredM.setGraphProp lg LayeredOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.minimumSize])
      LayeredM.setGraphProp lg LayeredOptions.NODE_SIZE_MINIMUM ⟨100, 80⟩
      LayeredM.setGraphProp lg CoreOptions.CONTENT_ALIGNMENT (EnumSet.of #[ContentAlignment.hRight, .vBottom])
      let ln ← LayeredM.createNode lg { position := ⟨5, 5⟩, size := ⟨7, 7⟩, internal := originNode n }
      LayeredM.modifyGraph lg fun x => { x with layerlessNodes := #[ln] }
      return lg)
  let ((), g) ← ElkM.run (ElkGraphLayoutTransferrer.applyLayout arena {} lg root) g
  checkVec "hand: (5, 5) + (10, 10) + (100 - 60, 80 - 40)" (g.node n).position ⟨55, 55⟩
  checkVec "hand: N size kept (BRANDES_KOEPF, no constraints)" (g.node n).size ⟨1, 1⟩
  checkVec "hand: fixed graph size keeps R2" (g.node root).size ⟨33, 44⟩
  check "hand: R2 constraints fixed" ((g.node root).props.get? CoreOptions.NODE_SIZE_CONSTRAINTS == some SizeConstraint.fixed)
  -- default minimum size (20, 20), centered; network simplex flexible node sizes
  let ((root, n, m), g) ← ElkM.run (do
      let root ← ElkM.createNode none
      named root "R3"
      ElkM.setNodeProp root CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.minimumSize])
      let n ← ElkM.createNode (some root)
      named n "N" 1 1
      let m ← ElkM.createNode (some root)
      named m "M" 1 1
      return (root, n, m)) {}
  let (lg, arena) ← LayeredM.run (do
      let lg ← LayeredM.createGraph { padding := ElkPadding.ofAny 2 }
      LayeredM.setGraphProp lg LayeredOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.minimumSize])
      LayeredM.setGraphProp lg CoreOptions.CONTENT_ALIGNMENT ContentAlignment.centerCenter
      LayeredM.setGraphProp lg LayeredOptions.NODE_PLACEMENT_STRATEGY NodePlacementStrategy.networkSimplex
      LayeredM.setGraphProp lg LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY_DEFAULT NodeFlexibility.nodeSize
      let ln ← LayeredM.createNode lg { position := ⟨1, 1⟩, size := ⟨7, 9⟩, internal := originNode n }
      let lm ← LayeredM.createNode lg { position := ⟨3, 4⟩, size := ⟨5, 6⟩, internal := originNode m }
      LayeredM.setNodeProp lm LayeredOptions.NODE_PLACEMENT_NETWORK_SIMPLEX_NODE_FLEXIBILITY NodeFlexibility.portPosition
      LayeredM.modifyGraph lg fun x => { x with layerlessNodes := #[ln, lm] }
      return lg)
  let ((), g) ← ElkM.run (ElkGraphLayoutTransferrer.applyLayout arena {} lg root) g
  checkVec "hand: (1, 1) + (2, 2) + ((20 - 4) / 2, (20 - 4) / 2)" (g.node n).position ⟨11, 11⟩
  checkVec "hand: graph default NODE_SIZE flexibility sets N's size" (g.node n).size ⟨7, 9⟩
  checkVec "hand: M position (3, 4) + (10, 10)" (g.node m).position ⟨13, 14⟩
  checkVec "hand: M's own PORT_POSITION flexibility keeps its size" (g.node m).size ⟨1, 1⟩
  checkVec "hand: R3 resized to max((4, 4), default minimum (20, 20))" (g.node root).size ⟨20, 20⟩

/-- An empty graph: only the parent node layout (the root origin comes from the argument). -/
def emptyGraphScenario : Suite := suite "layered.transform.emptyGraph" do
  let (root, g) ← ElkM.run (do
      let root ← ElkM.createNode none
      named root "R4"
      ElkM.setNodeProp root CoreOptions.NODE_SIZE_OPTIONS (EnumSet.of #[SizeOptions.computePadding])
      return root) {}
  let (lg, arena) ← LayeredM.run (LayeredM.createGraph { padding := ElkPadding.ofAny 12 })
  let ((), g) ← ElkM.run (ElkGraphLayoutTransferrer.applyLayout arena {} lg root) g
  checkVec "hand: empty graph size = padding 12 + 12" (g.node root).size ⟨24, 24⟩
  checkFloat "hand: computed padding left 12" ((g.node root).props.get? CoreOptions.PADDING |>.getD {}).left 12
  check "hand: no external ports → PORT_CONSTRAINTS untouched" (!(g.node root).props.has CoreOptions.PORT_CONSTRAINTS)

/-- `LabelDummySwitcher.INCLUDE_LABEL`. -/
def includeLabelTests : Suite := suite "layered.intermediate.includeLabel" do
  checkEq "INCLUDE_LABEL id" LabelDummySwitcher.INCLUDE_LABEL.id "edgelabelcenterednessanalysis.includelabel"
  checkEq "INCLUDE_LABEL default false" (({} : PropertyMap).get LabelDummySwitcher.INCLUDE_LABEL) (some false)
  checkEq "INCLUDE_LABEL set true" ((({} : PropertyMap).set LabelDummySwitcher.INCLUDE_LABEL true).get LabelDummySwitcher.INCLUDE_LABEL) (some true)

def suites : Array Tests.Suite :=
  #[mainScenario, contentAlignmentScenario, emptyGraphScenario, includeLabelTests]

end Tests.Layered.Transform
