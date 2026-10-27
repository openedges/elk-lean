import Tests.Framework
import Elk.Alg.Layered
import Elk.Alg.Layered.Intermediate.HierarchicalPortOrthogonalEdgeRouter
/-!
Tests of `HierarchicalPortOrthogonalEdgeRouter` (elk-rs
`intermediate/hierarchical_port_orthogonal_edge_router.rs`). Neither elk-rs nor Java has unit tests
for this processor, so all graphs are hand-built in the state `HierarchicalPortConstraintProcessor`
and phases 4/5 leave them in (replacement dummies with a `WEST` input and an `EAST` output port in
the layers, the original north/south dummies removed and listed in `EXT_PORT_REPLACED_DUMMIES`) and
the expected values are derived by hand from the processor and the routing generator's slot logic
("hand: …"; see `P5Orthogonal` for the slot → coordinate mapping: south-to-north slots lie at
`startPos - slot · edgeSpacing`, north-to-south slots at `startPos + slot · edgeSpacing`).

Common setup: `SPACING_NODE_NODE = 20`, `SPACING_EDGE_EDGE = 10`, `SPACING_PORT_PORT = 10`; all ports
have size 0 (anchor `(0, 0)`); original dummies are `10 × 10` with their port at `(5, 0)` and
`PORT_ANCHOR = (5, 0)`.
-/
namespace Tests.Layered.IntermediateHierarchicalPortRouting

open Tests Elk.Graph Elk.Core.Util Elk.Core.Alg Elk.Core.Math Elk.Core.Options Elk.Alg.Layered
  Elk.Alg.Layered.Graph Elk.Alg.Layered.Options Elk.Alg.Layered.Intermediate
open Elk (ElkEnum EnumSet)

open HierarchicalPortOrthogonalEdgeRouter

def kv (x y : Float) : KVector := ⟨x, y⟩
def pos (a : LGraphArena) (n : LNodeId) : KVector := (a.node n).position
def bends (a : LGraphArena) (e : LEdgeId) : Array KVector := (a.edge e).bendPoints
def junctions (a : LGraphArena) (e : LEdgeId) : Array KVector := (a.edge e).props.getD LayeredOptions.JUNCTION_POINTS #[]

/-- A graph with the common spacings, the given port constraints and geometry. -/
def mkGraph (pc : PortConstraints) (size : KVector) (padding : LPadding := {}) (offset : KVector := {}) :
    LayeredM LGraphId := do
  let g ← LayeredM.createGraph
  LayeredM.modifyGraph g fun x =>
    let props := x.props
      |>.set LayeredOptions.SPACING_NODE_NODE 20.0
      |>.set LayeredOptions.SPACING_EDGE_EDGE 10.0
      |>.set LayeredOptions.SPACING_PORT_PORT 10.0
      |>.set LayeredOptions.PORT_CONSTRAINTS pc
    { x with props := props, size := size, padding := padding, offset := offset }
  return g

/-- Appends a new layer. -/
def addLayer (g : LGraphId) : LayeredM LayerId := do
  let l ← LayeredM.createLayer g
  LayeredM.modifyGraph g fun x => { x with layers := x.layers.push l }
  return l

/-- A size-0 port of `n` at `(x, y)` on `side`. -/
def addPort (n : LNodeId) (side : PortSide) (x y : Float) : LayeredM LPortId := do
  let p ← LayeredM.createPort
  LayeredM.setPortNode p (some n)
  LayeredM.modifyPort p fun pt => { pt.setSide side with position := ⟨x, y⟩ }
  return p

/-- A normal `30 × 30` node at `(x, y)` in `layer`. -/
def addNode (g : LGraphId) (layer : LayerId) (x y : Float) : LayeredM LNodeId := do
  let n ← LayeredM.createNode g { size := ⟨30, 30⟩, position := ⟨x, y⟩ }
  LayeredM.setNodeLayer n (some layer)
  return n

/-- An original north/south dummy (not in a layer): `10 × 10`, port at `(5, 0)`, `PORT_ANCHOR (5, 0)`. -/
def addOriginal (g : LGraphId) (side : PortSide) (ratio : Float := 0.0) (margin : LMargin := {}) :
    LayeredM (LNodeId × LPortId) := do
  let n ← LayeredM.createNode g { size := ⟨10, 10⟩, type := .externalPort, margin := margin }
  LayeredM.modifyNode n fun x => { x with
    props := x.props.set LayeredOptions.PORT_ANCHOR (kv 5 0)
    internal := { x.internal with extPortSide := side, portRatioOrPosition := ratio } }
  let p ← addPort n side 5.0 0.0
  return (n, p)

/-- A replacement dummy of `original` at `(x, y)` in `layer` (size 0, `WEST` input and `EAST` output
port at `(0, 0)`, like `HierarchicalPortConstraintProcessor.createDummy`). -/
def addTemp (g : LGraphId) (layer : LayerId) (original : LNodeId) (side : PortSide) (x y : Float) :
    LayeredM (LNodeId × LPortId × LPortId) := do
  let n ← LayeredM.createNode g { position := ⟨x, y⟩, type := .externalPort }
  LayeredM.modifyNode n fun nd => { nd with
    internal := { nd.internal with extPortSide := side, extPortReplacedDummy := some original } }
  LayeredM.setNodeLayer n (some layer)
  let pw ← addPort n .west 0.0 0.0
  let pe ← addPort n .east 0.0 0.0
  return (n, pw, pe)

/-- An edge with bend points. -/
def connect (s t : LPortId) (bps : Array KVector := #[]) : LayeredM LEdgeId := do
  let e ← LayeredM.createEdge
  LayeredM.setEdgeSource e (some s)
  LayeredM.setEdgeTarget e (some t)
  LayeredM.modifyEdge e fun x => { x with bendPoints := bps }
  return e

def setReplaced (g : LGraphId) (ds : Array LNodeId) : LayeredM Unit :=
  LayeredM.modifyGraph g fun x => { x with internal := { x.internal with extPortReplacedDummies := ds } }

/-! ## Two dummies per side (FIXED_SIDE) -/

/-- Handles of the two-dummies-per-side graph. -/
structure G1 where
  g : LGraphId
  layers : Array LayerId
  b : LNodeId
  temps : Array LNodeId
  originals : Array LNodeId
  originalPorts : Array LPortId
  eA : LEdgeId
  eB : LEdgeId
  eU : LEdgeId
  base : Nat

/-- `FIXED_SIDE`, size `(110, 60)`, padding 10, offset `(2, 4)`. `L0 = [a (0, 0)]`,
`L1 = [t1 (50, 0) → N, t2 (50, 10) → M, u1 (50, 60) → S, u2 (50, 70) → R]`, `L2 = [b (80, 0)]`;
north originals `N, M`, south originals `S, R`; edges `eA: a → t1`, `eB: t1 → b`, `eU: u1 → b`. -/
def g1 : LayeredM G1 := do
  let g ← mkGraph .fixedSide (kv 110 60) { top := 10, bottom := 10, left := 10, right := 10 } (kv 2 4)
  let l0 ← addLayer g
  let l1 ← addLayer g
  let l2 ← addLayer g
  let a ← addNode g l0 0 0
  let pa ← addPort a .east 30.0 15.0
  let (nN, pN) ← addOriginal g .north
  let (nM, pM) ← addOriginal g .north
  let (nS, pS) ← addOriginal g .south
  let (nR, pR) ← addOriginal g .south
  let (t1, pw1, pe1) ← addTemp g l1 nN .north 50 0
  let (t2, _, _) ← addTemp g l1 nM .north 50 10
  let (u1, _, peu1) ← addTemp g l1 nS .south 50 60
  let (u2, _, _) ← addTemp g l1 nR .south 50 70
  let b ← addNode g l2 80 0
  let pb ← addPort b .west 0.0 15.0
  let eA ← connect pa pw1 #[kv 40 15, kv 40 0]
  let eB ← connect pe1 pb #[kv 65 0, kv 65 15]
  let eU ← connect peu1 pb #[kv 65 60, kv 65 15]
  setReplaced g #[nN, nM, nS, nR]
  let base := (← get).edges.size
  return { g, layers := #[l0, l1, l2], b, temps := #[t1, t2, u1, u2], originals := #[nN, nM, nS, nR],
           originalPorts := #[pN, pM, pS, pR], eA, eB, eU, base }

def stepTests : Suite := suite "layered.intermediate.hierarchicalPortRouting.steps" do
  let ((h, restored, height), a) ← LayeredM.run (do
    let h ← g1
    let restored ← restoreNorthSouthDummies h.g
    setNorthSouthDummyCoordinates h.g restored
    let height ← routeEdges h.g restored
    return (h, restored, height))
  checkEq "hand: restored dummies in EXT_PORT_REPLACED_DUMMIES order" restored h.originals
  checkEq "hand: originals appended to the last layer" (a.layer h.layers[2]!).nodes
    (#[h.b] ++ h.originals)
  checkEq "hand: northern dummy port flipped to SOUTH" (a.port h.originalPorts[0]!).side PortSide.south
  checkEq "hand: southern dummy port flipped to NORTH" (a.port h.originalPorts[2]!).side PortSide.north
  checkEq "hand: replacement dummy gets an origin port on its EXT_PORT_SIDE"
    ((a.node h.temps[0]!).ports.map fun p => (a.port p).side) #[PortSide.west, .east, .north]
  checkEq "hand: origin edge t1 → N" ((a.edge ⟨h.base⟩).target) (some h.originalPorts[0]!)
  -- hand: x = connected anchor 50 - PORT_ANCHOR 5 = 45; M (equal x, sorted after N) moved to
  -- 45 + 10 + 0 + 10 = 65; north y = -padding.top - offset.y = -14, south y = 60 + 20 - 4 = 76
  checkEq "hand: N at (45, -14)" (pos a h.originals[0]!) (kv 45 (-14))
  checkEq "hand: M moved right to (65, -14)" (pos a h.originals[1]!) (kv 65 (-14))
  checkEq "hand: S at (45, 76)" (pos a h.originals[2]!) (kv 45 76)
  checkEq "hand: R moved right to (65, 76)" (pos a h.originals[3]!) (kv 65 76)
  -- hand: t1 → N straight (50 = 45 + 5), t2 → M one slot at startPos = -20 - 4
  checkEq "hand: straight t1 → N edge has no bend points" (bends a ⟨h.base⟩) #[]
  checkEq "hand: t2 → M routed in slot 0 at y -24" (bends a ⟨h.base + 1⟩) #[kv 50 (-24), kv 70 (-24)]
  checkFloat "hand: northern routing height 20 + 0 · 10" height 20.0
  -- hand: south start = (60 + 20) + 20 - 24 = 76
  checkEq "hand: u2 → R routed in slot 0 at y 76" (bends a ⟨h.base + 3⟩) #[kv 50 76, kv 70 76]
  checkEq "hand: offset.y grows by the northern height" (a.graph h.g).offset (kv 2 24)
  checkEq "hand: size grows by both routing heights" (a.graph h.g).size (kv 110 100)

def fullTests : Suite := suite "layered.intermediate.hierarchicalPortRouting.fixedSide" do
  let (h, a) ← LayeredM.run (do
    let h ← g1
    HierarchicalPortOrthogonalEdgeRouter.processor.process h.g ProgressMonitor.null
    return h)
  let pN := h.originalPorts[0]!
  let pS := h.originalPorts[2]!
  checkEq "hand: eA retargeted to N with [t1 position] appended" ((a.edge h.eA).target) (some pN)
  checkEq "hand: eA bends" (bends a h.eA) #[kv 40 15, kv 40 0, kv 50 0]
  checkEq "hand: eB starts at N with [t1 position] prepended" ((a.edge h.eB).source) (some pN)
  checkEq "hand: eB bends" (bends a h.eB) #[kv 50 0, kv 65 0, kv 65 15]
  checkEq "hand: eU starts at S" ((a.edge h.eU).source) (some pS)
  checkEq "hand: eU bends" (bends a h.eU) #[kv 50 60, kv 65 60, kv 65 15]
  checkEq "hand: N's port edges after restoration" ((a.port pN).incomingEdges ++ (a.port pN).outgoingEdges)
    #[h.eA, h.eB]
  check "hand: origin edges disconnected"
    ((List.range 4).all fun i => let e := a.edge ⟨h.base + i⟩; e.source.isNone && e.target.isNone)
  checkEq "hand: replacement dummies removed (L1 empty)" (a.layer h.layers[1]!).nodes #[]
  check "hand: replacement dummies have no layer" (h.temps.all fun t => (a.node t).layer.isNone)
  checkEq "hand: last layer holds b and the originals" (a.layer h.layers[2]!).nodes (#[h.b] ++ h.originals)
  -- hand: final y: north -offset.y - padding.top = -34, south size.y + padding.bottom - offset.y = 86
  checkEq "hand: N final (45, -34)" (pos a h.originals[0]!) (kv 45 (-34))
  checkEq "hand: M final (65, -34)" (pos a h.originals[1]!) (kv 65 (-34))
  checkEq "hand: S final (45, 86)" (pos a h.originals[2]!) (kv 45 86)
  checkEq "hand: R final (65, 86)" (pos a h.originals[3]!) (kv 65 86)
  checkEq "hand: graph size (110, 100)" (a.graph h.g).size (kv 110 100)
  checkEq "hand: graph offset (2, 24)" (a.graph h.g).offset (kv 2 24)

/-! ## Hyperedge with junction point -/

def junctionTests : Suite := suite "layered.intermediate.hierarchicalPortRouting.junction" do
  -- `L0 = [a (0, 20)]`, `L1 = [t1 (50, 20)]`, `L2 = [t3 (150, 20)]`, both replacing N; `eA: a → t1`
  let ((g, eA, nN, pN, base, layers), a) ← LayeredM.run (do
    let g ← mkGraph .fixedSide (kv 200 50)
    let l0 ← addLayer g
    let l1 ← addLayer g
    let l2 ← addLayer g
    let na ← addNode g l0 0 20
    let pa ← addPort na .east 30.0 15.0
    let (nN, pN) ← addOriginal g .north
    let (_, pw1, _) ← addTemp g l1 nN .north 50 20
    let _ ← addTemp g l2 nN .north 150 20
    let eA ← connect pa pw1
    setReplaced g #[nN]
    let base := (← get).edges.size
    HierarchicalPortOrthogonalEdgeRouter.processor.process g ProgressMonitor.null
    return (g, eA, nN, pN, base, #[l0, l1, l2]))
  -- hand: N.x = (50 + 150) / 2 - 5 = 95; one segment [50, 150] with outgoing 100, slot 0 at -20
  checkEq "hand: t1 → N bends" (bends a ⟨base⟩) #[kv 50 (-20), kv 100 (-20)]
  checkEq "hand: t1 → N junction point inside the segment" (junctions a ⟨base⟩) #[kv 100 (-20)]
  checkEq "hand: t3 → N bends" (bends a ⟨base + 1⟩) #[kv 150 (-20), kv 100 (-20)]
  checkEq "hand: t3 → N junction already created" (junctions a ⟨base + 1⟩) #[]
  checkEq "hand: eA gets [t1 position] ++ origin bends" (bends a eA) #[kv 50 20, kv 50 (-20), kv 100 (-20)]
  checkEq "hand: eA targets N" ((a.edge eA).target) (some pN)
  checkEq "hand: N final (95, -20)" (pos a nN) (kv 95 (-20))
  checkEq "hand: offset/size after one northern slot" ((a.graph g).offset, (a.graph g).size) (kv 0 20, kv 200 70)
  checkEq "hand: layers after removal" (layers.map fun l => (a.layer l).nodes.size) #[1, 0, 1]

/-! ## FIXED_ORDER -/

def fixedOrderTests : Suite := suite "layered.intermediate.hierarchicalPortRouting.fixedOrder" do
  -- `L0 = [tM (50, 0)]`, `L1 = [tN (80, 0)]`; N ratio 1 (margin right 2), M ratio 2 (margin left 3)
  let ((g, nN, nM, base), a) ← LayeredM.run (do
    let g ← mkGraph .fixedOrder (kv 100 50)
    let l0 ← addLayer g
    let l1 ← addLayer g
    let (nN, _) ← addOriginal g .north 1.0 { right := 2 }
    let (nM, _) ← addOriginal g .north 2.0 { left := 3 }
    let _ ← addTemp g l0 nM .north 50 0
    let _ ← addTemp g l1 nN .north 80 0
    setReplaced g #[nN, nM]
    let base := (← get).edges.size
    HierarchicalPortOrthogonalEdgeRouter.processor.process g ProgressMonitor.null
    return (g, nN, nM, base))
  -- hand: N.x 75, M.x 45 violates the ratio order; next = 75 + 10 + 2 + 10 = 97, M = 97 + 3 = 100
  checkEq "hand: N keeps x 75" (pos a nN) (kv 75 (-20))
  checkEq "hand: M moved behind N's margin and the port spacing" (pos a nM) (kv 100 (-20))
  checkEq "hand: graph widened to M's right border" (a.graph g).size (kv 110 70)
  checkEq "hand: tM → M bends (edge created first, layer 0)" (bends a ⟨base⟩) #[kv 50 (-20), kv 105 (-20)]
  checkEq "hand: tN → N straight" (bends a ⟨base + 1⟩) #[]

/-! ## FIXED_RATIO / FIXED_POS and east/west dummies -/

def fixedRatioTests : Suite := suite "layered.intermediate.hierarchicalPortRouting.fixedRatio" do
  -- size (100, 50), padding (top 5, left 4, right 6, bottom 5), offset (1, 2).
  -- `L0 = [tN (30, 0) → N, W (west, ratio 1, anchor y 2, ext size y 4)]`,
  -- `L1 = [x (60, 10), E (east, ratio 0.5, anchor y 3, ext size y 6)]`, N ratio 0.5;
  -- `eW: W → x` with bends [(20, 40), (20, 15)], `eE: x → E` with bends [(80, 15), (80, 30)]
  let ((g, nN, nW, nE, eW, eE, base), a) ← LayeredM.run (do
    let g ← mkGraph .fixedRatio (kv 100 50) { top := 5, left := 4, right := 6, bottom := 5 } (kv 1 2)
    let l0 ← addLayer g
    let l1 ← addLayer g
    let (nN, _) ← addOriginal g .north 0.5
    let _ ← addTemp g l0 nN .north 30 0
    let nW ← LayeredM.createNode g { type := .externalPort }
    LayeredM.modifyNode nW fun x => { x with
      props := x.props.set LayeredOptions.PORT_ANCHOR (kv 0 2)
      internal := { x.internal with extPortSide := .west, portRatioOrPosition := 1.0, extPortSize := kv 0 4 } }
    LayeredM.setNodeLayer nW (some l0)
    let pW ← addPort nW .east 0.0 0.0
    let nx ← addNode g l1 60 10
    let px ← addPort nx .west 0.0 5.0
    let pxe ← addPort nx .east 30.0 5.0
    let nE ← LayeredM.createNode g { type := .externalPort }
    LayeredM.modifyNode nE fun x => { x with
      props := x.props.set LayeredOptions.PORT_ANCHOR (kv 0 3)
      internal := { x.internal with extPortSide := .east, portRatioOrPosition := 0.5, extPortSize := kv 0 6 } }
    LayeredM.setNodeLayer nE (some l1)
    let pE ← addPort nE .west 0.0 0.0
    let eW ← connect pW px #[kv 20 40, kv 20 15]
    let eE ← connect pxe pE #[kv 80 15, kv 80 30]
    setReplaced g #[nN]
    let base := (← get).edges.size
    HierarchicalPortOrthogonalEdgeRouter.processor.process g ProgressMonitor.null
    return (g, nN, nW, nE, eW, eE, base))
  -- hand: N.x = 110 · 0.5 - 5 - (4 + 1) = 45 (anchor x 50); start -20 - 2
  checkEq "hand: tN → N routed at y -22" (bends a ⟨base⟩) #[kv 30 (-22), kv 50 (-22)]
  -- hand: W: x = -1 - 4; y = 80 · 1 - 2 = 78 (needs 82, graph grows by 2), 78 - (5 + 22) = 51
  checkEq "hand: W at (-5, 51)" (pos a nW) (kv (-5) 51)
  -- hand: E: x = 100 + 6 - 1; y = 82 · 0.5 - 3 = 38, 38 - 27 = 11
  checkEq "hand: E at (105, 11)" (pos a nE) (kv 105 11)
  checkEq "hand: N at (45, -27)" (pos a nN) (kv 45 (-27))
  checkEq "hand: size (100, 50 + 20 + 2)" (a.graph g).size (kv 100 72)
  checkEq "hand: offset (1, 22)" (a.graph g).offset (kv 1 22)
  checkEq "hand: eW first bend aligned with W's anchor" (bends a eW) #[kv 20 51, kv 20 15]
  checkEq "hand: eE last bend aligned with E's anchor" (bends a eE) #[kv 80 15, kv 80 11]

def fixedPosTests : Suite := suite "layered.intermediate.hierarchicalPortRouting.fixedPos" do
  -- one layer `L0 = [E (east, position 70, anchor y 4, ext size y 8)]`; unconnected N at position 120
  let ((g, nN, nE, layer), a) ← LayeredM.run (do
    let g ← mkGraph .fixedPos (kv 100 50)
    let l0 ← addLayer g
    let (nN, _) ← addOriginal g .north 120.0
    let nE ← LayeredM.createNode g { type := .externalPort }
    LayeredM.modifyNode nE fun x => { x with
      props := x.props.set LayeredOptions.PORT_ANCHOR (kv 0 4)
      internal := { x.internal with extPortSide := .east, portRatioOrPosition := 70.0, extPortSize := kv 0 8 } }
    LayeredM.setNodeLayer nE (some l0)
    setReplaced g #[nN]
    HierarchicalPortOrthogonalEdgeRouter.processor.process g ProgressMonitor.null
    return (g, nN, nE, l0))
  -- hand: N.x = 120 - 5 = 115, graph width max(100, 115 + 5) = 120
  checkEq "hand: N at (115, 0)" (pos a nN) (kv 115 0)
  -- hand: E.x = 120 + 0 - 0; y = 70 - 4 = 66, required 74 → height 74
  checkEq "hand: E at (120, 66)" (pos a nE) (kv 120 66)
  checkEq "hand: graph size (120, 74)" (a.graph g).size (kv 120 74)
  checkEq "hand: single layer = last layer holds N" (a.layer layer).nodes #[nE, nN]
  checkEq "hand: no origin edge for an unconnected dummy" (a.port (a.node nN).ports[0]!).incomingEdges #[]

def freeTests : Suite := suite "layered.intermediate.hierarchicalPortRouting.free" do
  let ((g, nN, nM), a) ← LayeredM.run (do
    let g ← mkGraph .free (kv 20 50)
    let l0 ← addLayer g
    let _ ← addNode g l0 0 0
    let (nN, _) ← addOriginal g .north
    let (nM, _) ← addOriginal g .north
    setReplaced g #[nN, nM]
    HierarchicalPortOrthogonalEdgeRouter.processor.process g ProgressMonitor.null
    return (g, nN, nM))
  checkEq "hand: unconnected dummy gets x 0" (pos a nN) (kv 0 0)
  checkEq "hand: second unconnected dummy moved to 0 + 10 + 10" (pos a nM) (kv 20 0)
  checkFloat "hand: graph widened to 30" (a.graph g).size.x 30.0
  let (n, a2) ← LayeredM.run (do
    let g ← mkGraph .fixedSide (kv 20 50)
    let _ ← addLayer g
    HierarchicalPortOrthogonalEdgeRouter.processor.process g ProgressMonitor.null
    return g)
  checkEq "hand: nothing to restore leaves the graph unchanged" ((a2.graph n).size, (a2.graph n).offset) (kv 20 50, kv 0 0)

/-! ## Port labels of restored dummies -/

/-- A `20 × 10` north dummy with its port at `(8, 0)` and labels of size `6 × 4` and `10 × 5`. -/
def labelGraph (placement : EnumSet PortLabelPlacement) : LayeredM (LNodeId × Array LLabelId) := do
  let g ← mkGraph .fixedSide (kv 100 50)
  LayeredM.setGraphProp g LayeredOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.portLabels])
  LayeredM.setGraphProp g CoreOptions.PORT_LABELS_PLACEMENT placement
  let _ ← addLayer g
  let n ← LayeredM.createNode g { size := ⟨20, 10⟩, type := .externalPort }
  LayeredM.setNodeProp n LayeredOptions.SPACING_LABEL_PORT_HORIZONTAL 3.0
  LayeredM.setNodeProp n LayeredOptions.SPACING_LABEL_PORT_VERTICAL 2.0
  LayeredM.setNodeProp n LayeredOptions.SPACING_LABEL_LABEL 1.0
  LayeredM.modifyNode n fun x => { x with internal := { x.internal with extPortSide := .north } }
  let p ← addPort n .north 8.0 0.0
  let l1 ← LayeredM.createLabel "a" { size := ⟨6, 4⟩, position := ⟨0, 7⟩ }
  let l2 ← LayeredM.createLabel "b" { size := ⟨10, 5⟩, position := ⟨0, 9⟩ }
  LayeredM.modifyPort p fun pt => { pt with labels := #[l1, l2] }
  restoreDummy n g
  return (n, #[l1, l2])

def labelTests : Suite := suite "layered.intermediate.hierarchicalPortRouting.labels" do
  let ((n, ls), a) ← LayeredM.run (labelGraph PortLabelPlacement.insideSet)
  -- hand: centre x = 20 / 2 - 8 = 2; y from 2, then 2 + 4 + 1
  checkEq "hand: INSIDE first label" (a.label ls[0]!).position (kv (-1) 2)
  checkEq "hand: INSIDE second label" (a.label ls[1]!).position (kv (-3) 7)
  checkEq "hand: restored port side" (a.port (a.node n).ports[0]!).side PortSide.south
  -- elk-rs: the dummy is not in a layer, so the adapter search finds nothing and no margins are set
  checkEq "elk-rs: no margins for the (layerless) restored dummy" (a.node n).margin.right 0.0
  let ((_, ls2), a2) ← LayeredM.run (labelGraph PortLabelPlacement.outsideSet)
  -- hand: x = 3 + 20 - 8 = 15, y unchanged
  checkEq "hand: OUTSIDE labels right of the dummy"
    (ls2.map fun l => (a2.label l).position) #[kv 15 7, kv 15 9]

def suites : Array Suite :=
  #[stepTests, fullTests, junctionTests, fixedOrderTests, fixedRatioTests, fixedPosTests, freeTests, labelTests]

end Tests.Layered.IntermediateHierarchicalPortRouting
