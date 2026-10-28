import Tests.Framework
import Elk.Alg.Common
/-! Tests of `nodespacing.internal.algorithm` cell/label/node-size parts (task N2a):
PortContextCreator, NodeLabelCellCreator, InsidePortLabelCellCreator, CellSystemConfigurator,
LabelPlacer, NodeSizeCalculator.

elk-rs has no unit tests for these files, so every expected number is derived by hand from the
elk-rs formulas; the check names say which formula ("hand:" prefix). -/
namespace Tests.AlgCommon.NodeSpacing.AlgorithmCells

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal
open Elk.Alg.Common.NodeSpacing.Internal.Algorithm

private abbrev Ctx := NodeContext NodeId PortId LabelId

private def close (a b : Float) : Bool := (a - b).abs <= 1e-9

private def checkRect (name : String) (r : ElkRectangle) (x y w h : Float) : TestM Unit :=
  report name (close r.x x && close r.y y && close r.width w && close r.height h)
    s!"expected ({x}, {y}, {w}, {h}), got {repr r}"

private def checkVec (name : String) (v : KVector) (x y : Float) : TestM Unit :=
  report name (close v.x x && close v.y y) s!"expected ({x}, {y}), got {repr v}"

private def checkPadding (name : String) (p : ElkPadding) (top right bottom left : Float) : TestM Unit :=
  report name (close p.top top && close p.right right && close p.bottom bottom && close p.left left)
    s!"expected [t={top}, r={right}, b={bottom}, l={left}], got {repr p}"

/-- Size contribution flags `(width, height)` of an optional cell (`(false, false)` for none). -/
private def flags (ctx : Ctx) (c : Option CellId) : Bool × Bool :=
  match c with
  | some id => (ctx.cells.isContributingToMinimumWidth id, ctx.cells.isContributingToMinimumHeight id)
  | none => (false, false)

/-- The labels held by an optional label cell. -/
private def labelsOf (ctx : Ctx) (c : Option CellId) : Array LabelId :=
  match c with
  | some id => (ctx.cells.labels id).map (·.1)
  | none => #[]

/-- Runs `f` with a fresh adapter family on the node context of `n`. -/
private def withContext {α : Type} (g : ElkGraph) (n : NodeId) (f : ElkAdapters → Ctx → ElkM α) :
    IO (α × ElkGraph) := do
  let a ← ElkGraphAdapters.new
  ElkM.run (do f a (← NodeContext.new a n)) g

/-- Phase 1 of the calculator: port contexts, node label cells, inside port label cells. -/
private def phase1 (a : ElkAdapters) (ctx : Ctx) (horizontalLayoutMode : Bool := true) : ElkM Ctx := do
  let ctx ← PortContextCreator.createPortContexts a ctx false
  let ctx ← NodeLabelCellCreator.createNodeLabelCells a ctx false horizontalLayoutMode
  return InsidePortLabelCellCreator.createInsidePortLabelCells ctx

/-! ### PortContextCreator -/

/-- Root (SPACING_LABEL_LABEL 2, SPACING_PORTS_SURROUNDING t10 r4 b12 l6) ⊃ node `n` (60×40) with
seven 4×4 ports on N, S, E, S, W, N, W; p0 has a 10×5 label, p2 labels 8×3 and 6×4, p6 has
PORT_BORDER_OFFSET -2. -/
private def portGraph (placement : EnumSet PortLabelPlacement) : ElkGraph × NodeId × Array PortId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root CoreOptions.SPACING_LABEL_LABEL 2.0
  let g := g.setNodeProp root CoreOptions.SPACING_PORTS_SURROUNDING
    ({ top := 10.0, right := 4.0, bottom := 12.0, left := 6.0 } : ElkMargin)
  let (g, n) := g.createNode (some root)
  let g := g.modifyNode n fun nd => { nd with width := 60.0, height := 40.0 }
  let g := g.setNodeProp n CoreOptions.PORT_LABELS_PLACEMENT placement
  let mut g := g
  let mut ports : Array PortId := #[]
  for side in #[PortSide.north, .south, .east, .south, .west, .north, .west] do
    let (g', p) := g.createPort (some n)
    g := (g'.setPortProp p CoreOptions.PORT_SIDE side).modifyPort p fun pt => { pt with width := 4.0, height := 4.0 }
    ports := ports.push p
  let addLabel (g : ElkGraph) (p : PortId) (w h : Float) : ElkGraph :=
    let (g, l) := g.createLabel (some (.port p)) "l"
    g.modifyLabel l fun lb => { lb with width := w, height := h, x := 1.0, y := 2.0 }
  g := addLabel g ports[0]! 10.0 5.0
  g := addLabel g ports[2]! 8.0 3.0
  g := addLabel g ports[2]! 6.0 4.0
  g := g.setPortProp ports[6]! CoreOptions.PORT_BORDER_OFFSET (-2.0)
  return (g, n, ports)

def portContextCreatorTests : Suite := suite "alg.common.nodespacing.internal.algorithm.PortContextCreator" do
  let (g, n, ports) := portGraph (EnumSet.of #[PortLabelPlacement.inside])
  let ((ctx, vids), _) ← withContext g n fun a ctx => do
    let ctx ← PortContextCreator.createPortContexts a ctx false
    let vids ← ports.mapM a.port.getVolatileId
    return (ctx, vids)
  let idx (pc : PortContext PortId LabelId) : Nat := (ports.findIdx? (· == pc.port)).getD 99
  checkEq "volatile ids = port indices" vids #[0, 1, 2, 3, 4, 5, 6]
  checkEq "NORTH contexts in port order" ((ctx.portContextsOf .north).map idx) #[0, 5]
  checkEq "EAST contexts" ((ctx.portContextsOf .east).map idx) #[2]
  checkEq "SOUTH contexts reversed" ((ctx.portContextsOf .south).map idx) #[3, 1]
  checkEq "WEST contexts reversed" ((ctx.portContextsOf .west).map idx) #[6, 4]
  checkEq "SOUTH volatile ids descending" ((ctx.portContextsOf .south).map (·.volatileId)) #[3, 1]
  checkEq "values() order N, E, S, W" (ctx.allPortContexts.map idx) #[0, 5, 2, 3, 1, 6, 4]
  checkEq "UNDEFINED side has no contexts" (ctx.portContextsOf .undefined).size 0
  let p0 := (ctx.portContextsOf .north)[0]!
  let p2 := (ctx.portContextsOf .east)[0]!
  let p6 := (ctx.portContextsOf .west)[0]!
  let p4 := (ctx.portContextsOf .west)[1]!
  checkVec "port size extracted" p0.portSize 4.0 4.0
  checkEq "p2 label sizes extracted" (p2.labelSizes.map (·.x)) #[8.0, 6.0]
  checkVec "p2 label position extracted" p2.labelPositions[1]! 1.0 2.0
  check "INSIDE labels of a non-compound node are next to the port" (ctx.allPortContexts.all (·.labelsNextToPort))
  check "p6 has an explicit border offset -2" (p6.hasPortBorderOffset && close p6.portBorderOffset (-2.0))
  check "p4 has no border offset (0.0)" (!p4.hasPortBorderOffset && close p4.portBorderOffset 0.0)
  check "portRatioOrPosition stays 0" (ctx.allPortContexts.all fun pc => close pc.portRatioOrPosition 0.0)
  -- Java/elk-rs give every port a label cell; an empty one acts like none, so ports without labels
  -- get none here (`PortContextCreator.createPortContextOnSide`)
  check "ports with labels get a label cell, ports without labels none"
    (ctx.allPortContexts.all fun pc => pc.portLabelCell.isSome == !pc.labels.isEmpty)
  checkEq "p2 label cell holds both labels" (labelsOf ctx p2.portLabelCell).size 2
  checkEq "p4 label cell is empty" (labelsOf ctx p4.portLabelCell).size 0
  checkFloat "hand: p2 label cell width = max(8, 6)" (ctx.cells.minimumWidthOpt p2.portLabelCell) 8.0
  checkFloat "hand: p2 label cell height = 3 + 4 + gap labelLabelSpacing 2" (ctx.cells.minimumHeightOpt p2.portLabelCell) 9.0
  checkFloat "hand: p0 label cell width 10" (ctx.cells.minimumWidthOpt p0.portLabelCell) 10.0
  -- ignoreInsidePortLabels with INSIDE labels: no label cells
  let ((ctxI, _), _) ← withContext g n fun a ctx => do
    return (← PortContextCreator.createPortContexts a ctx true, ())
  check "ignoreInsidePortLabels + INSIDE: no label cells" (ctxI.allPortContexts.all (·.portLabelCell.isNone))
  -- fixed port labels: no label cells either
  let (gF, nF, _) := portGraph PortLabelPlacement.fixed
  let ((ctxF, _), _) ← withContext gF nF fun a ctx => do
    return (← PortContextCreator.createPortContexts a ctx false, ())
  check "fixed port labels: no label cells" (ctxF.allPortContexts.all (·.portLabelCell.isNone))
  check "fixed port labels: never next to the port" (ctxF.allPortContexts.all (!·.labelsNextToPort))
  -- OUTSIDE + NEXT_TO_PORT_IF_POSSIBLE: only ports without incident edges
  let (gO, nO, portsO) := portGraph (EnumSet.of #[PortLabelPlacement.outside, .nextToPortIfPossible])
  let (gO, other) := gO.createNode (gO.node nO).parent
  let (gO, _) := ElkGraphUtil.createSimpleEdge gO (.port portsO[0]!) (.node other)
  let ((ctxO, _), _) ← withContext gO nO fun a ctx => do
    return (← PortContextCreator.createPortContexts a ctx false, ())
  check "OUTSIDE next-to-port: port with an edge is not next to its labels"
    (!(ctxO.portContextsOf .north)[0]!.labelsNextToPort)
  check "OUTSIDE next-to-port: port without edges is" (ctxO.portContextsOf .north)[1]!.labelsNextToPort
  -- a port without side
  let gU := gO.setPortProp portsO[3]! CoreOptions.PORT_SIDE PortSide.undefined
  checkThrows "port without side throws IllegalArgumentException" do
    let _ ← withContext gU nO fun a ctx => PortContextCreator.createPortContexts a ctx false
    pure ()

/-! ### NodeLabelCellCreator -/

/-- Node `n` (50×30, default placement IN_T_C) with labels l0 20×10 and l1 12×6 (default), l2 8×4
OUT_T_L, l3 6×6 OUT_R_C, l4 5×5 fixed, l5 9×3 IN_B_R; root SPACING_LABEL_LABEL 2. -/
private def labelGraph : ElkGraph × NodeId × Array LabelId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root CoreOptions.SPACING_LABEL_LABEL 2.0
  let (g, n) := g.createNode (some root)
  let g := g.modifyNode n fun nd => { nd with width := 50.0, height := 30.0 }
  let g := g.setNodeProp n CoreOptions.NODE_LABELS_PLACEMENT (EnumSet.of #[NodeLabelPlacement.inside, .vTop, .hCenter])
  let specs : Array (Float × Float × Option (EnumSet NodeLabelPlacement)) := #[
    (20.0, 10.0, none), (12.0, 6.0, none),
    (8.0, 4.0, some (EnumSet.of #[.outside, .vTop, .hLeft])),
    (6.0, 6.0, some (EnumSet.of #[.outside, .hRight, .vCenter])),
    (5.0, 5.0, some NodeLabelPlacement.fixed),
    (9.0, 3.0, some (EnumSet.of #[.inside, .vBottom, .hRight]))]
  let mut g := g
  let mut labels : Array LabelId := #[]
  for (w, h, placement) in specs do
    let (g', l) := g.createLabel (some (.node n)) "label"
    g := g'.modifyLabel l fun lb => { lb with width := w, height := h }
    if let some p := placement then
      g := g.setLabelProp l CoreOptions.NODE_LABELS_PLACEMENT p
    labels := labels.push l
  return (g, n, labels)

def nodeLabelCellCreatorTests : Suite := suite "alg.common.nodespacing.internal.algorithm.NodeLabelCellCreator" do
  let (g, n, labels) := labelGraph
  let ((ctx, _), _) ← withContext g n fun a ctx => do
    return (← NodeLabelCellCreator.createNodeLabelCells a ctx false true, ())
  let some grid := ctx.insideNodeLabelContainer
    | report "inside node label container exists in the middle row's center" false
  check "inside node label container is a grid" (ctx.cells.isGrid grid)
  checkPadding "inside container padding = NODE_LABELS_PADDING (default 5)" (ctx.cells.padding grid) 5.0 5.0 5.0 5.0
  checkFloat "inside container gap = labelCellSpacing = 2 * 2" (ctx.cells.gap grid) 4.0
  let definedCells := NodeLabelLocation.allDefined.filter fun l => (ctx.nodeLabelCell l).isSome
  checkEq "label cells for IN_T_C, OUT_T_L, OUT_R_C, IN_B_R only (fixed label ignored)"
    (definedCells.map ElkEnum.javaName) #["OUT_T_L", "OUT_R_C", "IN_T_C", "IN_B_R"]
  let inTC := ctx.nodeLabelCell .inTC
  checkEqR "two labels of the same location share one cell" (labelsOf ctx inTC) #[labels[0]!, labels[1]!]
  checkEqR "IN_T_C cell sits in the grid at (BEGIN, CENTER)" (ctx.cells.getGridCell grid .begin .center) inTC
  checkEqR "IN_B_R cell sits in the grid at (END, END)" (ctx.cells.getGridCell grid .«end» .«end») (ctx.nodeLabelCell .inBR)
  checkFloat "hand: IN_T_C cell width = max(20, 12)" (ctx.cells.minimumWidthOpt inTC) 20.0
  checkFloat "hand: IN_T_C cell height = 10 + 6 + gap 2" (ctx.cells.minimumHeightOpt inTC) 18.0
  check "IN_T_C alignment (CENTER, TOP)"
    (match inTC with
      | some c => ctx.cells.horizontalAlignment c == .center && ctx.cells.verticalAlignment c == .top
      | none => false)
  let north := ctx.outsideNodeLabelContainer .north
  let east := ctx.outsideNodeLabelContainer .east
  checkEqR "OUT_T_L cell is the NORTH container's BEGIN cell"
    (north.bind fun c => ctx.cells.getCell c .begin) (ctx.nodeLabelCell .outTL)
  checkEqR "OUT_R_C cell is the EAST container's CENTER cell"
    (east.bind fun c => ctx.cells.getCell c .center) (ctx.nodeLabelCell .outRC)
  checkEq "OUT_T_L contributes height only" (flags ctx (ctx.nodeLabelCell .outTL)) (false, true)
  checkEq "OUT_R_C contributes width only" (flags ctx (ctx.nodeLabelCell .outRC)) (true, false)
  checkEq "inside label cells contribute nothing yet" (flags ctx inTC) (false, false)
  checkEq "NORTH container is a horizontal strip" (north.map (ctx.cells.containerMode ·)) (some Strip.horizontal)
  checkEq "WEST container is a vertical strip"
    ((ctx.outsideNodeLabelContainer .west).map (ctx.cells.containerMode ·)) (some Strip.vertical)
  checkPadding "NORTH container: bottom padding = SPACING_LABEL_NODE 5"
    (ctx.cells.paddingOpt north) 0.0 0.0 5.0 0.0
  checkPadding "SOUTH container: top padding 5" (ctx.cells.paddingOpt (ctx.outsideNodeLabelContainer .south)) 5.0 0.0 0.0 0.0
  checkPadding "WEST container: right padding 5" (ctx.cells.paddingOpt (ctx.outsideNodeLabelContainer .west)) 0.0 5.0 0.0 0.0
  checkPadding "EAST container: left padding 5" (ctx.cells.paddingOpt east) 0.0 0.0 0.0 5.0
  -- only inside labels
  let ((ctxI, _), _) ← withContext g n fun a ctx => do
    return (← NodeLabelCellCreator.createNodeLabelCells a ctx true true, ())
  check "onlyInside: no outside containers"
    (#[PortSide.north, .south, .east, .west].all fun s => (ctxI.outsideNodeLabelContainer s).isNone)
  checkEq "onlyInside: only the inside label cells"
    ((NodeLabelLocation.allDefined.filter fun l => (ctxI.nodeLabelCell l).isSome).map ElkEnum.javaName) #["IN_T_C", "IN_B_R"]
  -- vertical layout mode: labels side by side
  let ((ctxV, _), _) ← withContext g n fun a ctx => do
    return (← NodeLabelCellCreator.createNodeLabelCells a ctx false false, ())
  checkFloat "hand: vertical layout mode IN_T_C width = 20 + 12 + gap 2" (ctxV.cells.minimumWidthOpt (ctxV.nodeLabelCell .inTC)) 34.0
  checkFloat "hand: vertical layout mode IN_T_C height = max(10, 6)" (ctxV.cells.minimumHeightOpt (ctxV.nodeLabelCell .inTC)) 10.0

/-! ### InsidePortLabelCellCreator -/

def insidePortLabelCellCreatorTests : Suite :=
    suite "alg.common.nodespacing.internal.algorithm.InsidePortLabelCellCreator" do
  let (g, n, _) := portGraph (EnumSet.of #[PortLabelPlacement.inside])
  let ((ctx, _), _) ← withContext g n fun a ctx => do return (← phase1 a ctx, ())
  let cellN := ctx.insidePortLabelCell .north
  let cellS := ctx.insidePortLabelCell .south
  let cellE := ctx.insidePortLabelCell .east
  let cellW := ctx.insidePortLabelCell .west
  check "a cell for every side" (cellN.isSome && cellS.isSome && cellE.isSome && cellW.isSome)
  check "inside port label cells are atomic"
    (#[cellN, cellS, cellE, cellW].all fun c => match c with | some id => ctx.cells.isAtomic id | none => false)
  checkEqR "NORTH = node container BEGIN" (ctx.cells.getCell ctx.nodeContainer .begin) cellN
  checkEqR "SOUTH = node container END" (ctx.cells.getCell ctx.nodeContainer .«end») cellS
  checkEqR "WEST = middle row BEGIN" (ctx.cells.getCell ctx.nodeContainerMiddleRow .begin) cellW
  checkEqR "EAST = middle row END" (ctx.cells.getCell ctx.nodeContainerMiddleRow .«end») cellE
  checkPadding "hand: NORTH padding top = SPACING_LABEL_PORT_VERTICAL 1, left/right = margins 6/4"
    (ctx.cells.paddingOpt cellN) 1.0 4.0 0.0 6.0
  checkPadding "hand: SOUTH padding bottom = 1, left/right = 6/4" (ctx.cells.paddingOpt cellS) 0.0 4.0 1.0 6.0
  checkPadding "hand: EAST padding top/bottom = margins 10/12, right = SPACING_LABEL_PORT_HORIZONTAL 1"
    (ctx.cells.paddingOpt cellE) 10.0 1.0 12.0 0.0
  checkPadding "hand: WEST has empty label cells only: no left padding" (ctx.cells.paddingOpt cellW) 10.0 0.0 12.0 0.0
  checkFloat "hand: EAST content width = widest port label cell 8"
    (cellE.map (ctx.cells.minimumContentAreaSize · |>.x) |>.getD 0.0) 8.0
  checkFloat "hand: EAST minimum width = 8 + right padding 1" (ctx.cells.minimumWidthOpt cellE) 9.0
  -- OUTSIDE labels: no label width on the east cell
  let (gO, nO, _) := portGraph (EnumSet.of #[PortLabelPlacement.outside])
  let ((ctxO, _), _) ← withContext gO nO fun a ctx => do return (← phase1 a ctx, ())
  checkFloat "OUTSIDE port labels: EAST cell has no content width" (ctxO.cells.minimumWidthOpt (ctxO.insidePortLabelCell .east)) 0.0
  -- negative vertical port label spacing is not used as padding (inherited from the parent graph)
  let gN := gO.setNodeProp ((gO.node nO).parent.getD nO) CoreOptions.SPACING_LABEL_PORT_VERTICAL (-3.0)
  let ((ctxN, _), _) ← withContext gN nO fun a ctx => do return (← phase1 a ctx, ())
  checkPadding "negative SPACING_LABEL_PORT_VERTICAL keeps the NORTH top padding 0"
    (ctxN.cells.paddingOpt (ctxN.insidePortLabelCell .north)) 0.0 4.0 0.0 6.0

/-! ### CellSystemConfigurator -/

/-- Node `n` (60×40) with one NORTH port and one EAST port (label 8×3), inside node label IN_C_C
(20×10) and outside node label OUT_T_C (12×4); root SPACING_PORTS_SURROUNDING t2 r3 b4 l1. -/
private def configGraph (constraints : EnumSet SizeConstraint) (options : EnumSet SizeOptions)
    (portConstraints : PortConstraints) : ElkGraph × NodeId × LabelId × LabelId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root CoreOptions.SPACING_PORTS_SURROUNDING
    ({ top := 2.0, right := 3.0, bottom := 4.0, left := 1.0 } : ElkMargin)
  let (g, n) := g.createNode (some root)
  let g := g.modifyNode n fun nd => { nd with width := 60.0, height := 40.0 }
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_CONSTRAINTS constraints
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_OPTIONS options
  let g := g.setNodeProp n CoreOptions.PORT_CONSTRAINTS portConstraints
  let g := g.setNodeProp n CoreOptions.PORT_LABELS_PLACEMENT (EnumSet.of #[PortLabelPlacement.inside])
  let (g, pn) := g.createPort (some n)
  let g := g.setPortProp pn CoreOptions.PORT_SIDE PortSide.north
  let (g, pe) := g.createPort (some n)
  let g := g.setPortProp pe CoreOptions.PORT_SIDE PortSide.east
  let (g, pl) := g.createLabel (some (.port pe)) "pl"
  let g := g.modifyLabel pl fun lb => { lb with width := 8.0, height := 3.0 }
  let (g, inside) := g.createLabel (some (.node n)) "inside"
  let g := g.modifyLabel inside fun lb => { lb with width := 20.0, height := 10.0 }
  let g := g.setLabelProp inside CoreOptions.NODE_LABELS_PLACEMENT (EnumSet.of #[NodeLabelPlacement.inside, .vCenter, .hCenter])
  let (g, outside) := g.createLabel (some (.node n)) "outside"
  let g := g.modifyLabel outside fun lb => { lb with width := 12.0, height := 4.0 }
  let g := g.setLabelProp outside CoreOptions.NODE_LABELS_PLACEMENT (EnumSet.of #[NodeLabelPlacement.outside, .vTop, .hCenter])
  return (g, n, inside, outside)

/-- Phase 1 followed by `configureCellSystemSizeContributions` on `configGraph`. -/
private def configured (constraints : EnumSet SizeConstraint) (options : EnumSet SizeOptions := EnumSet.empty)
    (portConstraints : PortConstraints := .free) : IO Ctx := do
  let (g, n, _, _) := configGraph constraints options portConstraints
  let ((ctx, _), _) ← withContext g n fun a ctx => do
    return (CellSystemConfigurator.configureCellSystemSizeContributions (← phase1 a ctx), ())
  return ctx

def cellSystemConfiguratorTests : Suite := suite "alg.common.nodespacing.internal.algorithm.CellSystemConfigurator" do
  let ipl (ctx : Ctx) (s : PortSide) := flags ctx (ctx.insidePortLabelCell s)
  let row (ctx : Ctx) := flags ctx (some ctx.nodeContainerMiddleRow)
  -- fixed size: nothing changes
  let c ← configured EnumSet.empty
  checkEq "fixed size: NORTH cell contributes nothing" (ipl c .north) (false, false)
  checkEq "fixed size: middle row contributes nothing" (row c) (false, false)
  checkEq "fixed size: OUT_T_C keeps the creator's height flag" (flags c (c.nodeLabelCell .outTC)) (false, true)
  -- PORTS with free port placement
  let c ← configured (EnumSet.of #[SizeConstraint.ports])
  checkEq "PORTS: NORTH/SOUTH contribute width" (ipl c .north, ipl c .south) ((true, false), (true, false))
  checkEq "PORTS free: EAST/WEST contribute height" (ipl c .east, ipl c .west) ((false, true), (false, true))
  checkEq "PORTS free: middle row contributes height" (row c) (false, true)
  checkEq "PORTS: inside node label container untouched" (flags c c.insideNodeLabelContainer) (false, false)
  -- PORTS with FIXED_POS
  let c ← configured (EnumSet.of #[SizeConstraint.ports]) (portConstraints := .fixedPos)
  checkEq "PORTS FIXED_POS: EAST does not contribute height" (ipl c .east) (false, false)
  checkEq "PORTS FIXED_POS: middle row does not contribute height" (row c) (false, false)
  -- PORTS + PORT_LABELS
  let c ← configured (EnumSet.of #[SizeConstraint.ports, .portLabels])
  checkEq "PORT_LABELS: NORTH contributes both" (ipl c .north) (true, true)
  checkEq "PORT_LABELS: WEST contributes both" (ipl c .west) (true, true)
  checkEq "PORT_LABELS: middle row contributes both" (row c) (true, true)
  -- PORT_LABELS without PORTS does nothing
  let c ← configured (EnumSet.of #[SizeConstraint.portLabels])
  checkEq "PORT_LABELS alone: NORTH contributes nothing" (ipl c .north) (false, false)
  -- NODE_LABELS
  let c ← configured (EnumSet.of #[SizeConstraint.nodeLabels])
  checkEq "NODE_LABELS: inside container contributes both" (flags c c.insideNodeLabelContainer) (true, true)
  checkEq "NODE_LABELS: middle row contributes both" (row c) (true, true)
  checkEq "NODE_LABELS: inside label cell contributes both" (flags c (c.nodeLabelCell .inCC)) (true, true)
  checkEq "NODE_LABELS: outside label cell contributes both" (flags c (c.nodeLabelCell .outTC)) (true, true)
  checkEq "NODE_LABELS: inside port label cells untouched" (ipl c .east) (false, false)
  let c ← configured (EnumSet.of #[SizeConstraint.nodeLabels]) (EnumSet.of #[SizeOptions.outsideNodeLabelsOverhang])
  checkEq "NODE_LABELS + overhang: outside label cell contributes nothing" (flags c (c.nodeLabelCell .outTC)) (false, false)
  checkEq "NODE_LABELS + overhang: inside label cell still contributes" (flags c (c.nodeLabelCell .inCC)) (true, true)
  -- MINIMUM_SIZE accounting for padding
  let onlyCenter (ctx : Ctx) : Bool :=
    match ctx.insideNodeLabelContainer.bind (ctx.cells.gridData? ·) with
    | some d => d.onlyCenterCellContributes
    | none => false
  let c ← configured (EnumSet.of #[SizeConstraint.minimumSize]) (EnumSet.of #[SizeOptions.minimumSizeAccountsForPadding])
  checkEq "Java: MINIMUM_SIZE + MSAFP: middle row contributes its height only (elk-rs: both)" (row c) (false, true)
  checkEq "MINIMUM_SIZE + MSAFP: inside container contributes both" (flags c c.insideNodeLabelContainer) (true, true)
  check "MINIMUM_SIZE + MSAFP: only the center cell contributes" (onlyCenter c)
  checkEq "MINIMUM_SIZE + MSAFP: node label cells are not regarded" (flags c (c.nodeLabelCell .inCC)) (false, false)
  let c ← configured (EnumSet.of #[SizeConstraint.minimumSize, .nodeLabels])
    (EnumSet.of #[SizeOptions.minimumSizeAccountsForPadding])
  check "MINIMUM_SIZE + NODE_LABELS: the whole container contributes" (!onlyCenter c)
  let c ← configured (EnumSet.of #[SizeConstraint.minimumSize])
  checkEq "MINIMUM_SIZE without MSAFP: middle row contributes nothing" (row c) (false, false)
  -- updateVerticalInsidePortLabelCellPadding (portGraph: margins t10 b12, labelCellSpacing 4)
  let (g, n, _) := portGraph (EnumSet.of #[PortLabelPlacement.inside])
  let ((ctx, _), _) ← withContext g n fun a ctx => do
    return (CellSystemConfigurator.updateVerticalInsidePortLabelCellPadding (← phase1 a ctx), ())
  checkPadding "hand: EAST top = max(0, 10 - (0 + 1 + 4)), bottom = max(0, 12 - (0 + 1 + 4))"
    (ctx.cells.paddingOpt (ctx.insidePortLabelCell .east)) 5.0 1.0 7.0 0.0
  checkPadding "hand: WEST gets the same top/bottom padding" (ctx.cells.paddingOpt (ctx.insidePortLabelCell .west)) 5.0 0.0 7.0 0.0
  let gF := g.setNodeProp n CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedRatio
  let ((ctxF, _), _) ← withContext gF n fun a ctx => do
    return (CellSystemConfigurator.updateVerticalInsidePortLabelCellPadding (← phase1 a ctx), ())
  checkPadding "FIXED_RATIO: EAST padding unchanged" (ctxF.cells.paddingOpt (ctxF.insidePortLabelCell .east)) 10.0 1.0 12.0 0.0

/-! ### NodeSizeCalculator -/

/-- Phase 1, configuration, width, vertical padding update, height (the calculator without the
port placement phases). -/
private def sizeNode (a : ElkAdapters) (ctx : Ctx) : ElkM Ctx := do
  let ctx ← phase1 a ctx
  let ctx := CellSystemConfigurator.configureCellSystemSizeContributions ctx
  let ctx := NodeSizeCalculator.setNodeWidth ctx
  let ctx := CellSystemConfigurator.updateVerticalInsidePortLabelCellPadding ctx
  return NodeSizeCalculator.setNodeHeight ctx

/-- Node `n` (60×40) with PORT_LABELS_PLACEMENT INSIDE and one EAST port with an 8×3 label; root
SPACING_PORTS_SURROUNDING t2 r3 b4 l1. -/
private def eastPortGraph (constraints : EnumSet SizeConstraint) (portConstraints : PortConstraints) :
    ElkGraph × NodeId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root CoreOptions.SPACING_PORTS_SURROUNDING
    ({ top := 2.0, right := 3.0, bottom := 4.0, left := 1.0 } : ElkMargin)
  let (g, n) := g.createNode (some root)
  let g := g.modifyNode n fun nd => { nd with width := 60.0, height := 40.0 }
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_CONSTRAINTS constraints
  let g := g.setNodeProp n CoreOptions.PORT_CONSTRAINTS portConstraints
  let g := g.setNodeProp n CoreOptions.PORT_LABELS_PLACEMENT (EnumSet.of #[PortLabelPlacement.inside])
  let (g, pe) := g.createPort (some n)
  let g := g.setPortProp pe CoreOptions.PORT_SIDE PortSide.east
  let (g, pl) := g.createLabel (some (.port pe)) "pl"
  return (g.modifyLabel pl fun lb => { lb with width := 8.0, height := 3.0 }, n)

/-- Node `n` (10×10) with one IN_C_C label 20×10; constraints/minimum size as given. -/
private def insideLabelGraph (constraints : EnumSet SizeConstraint) (minimum : KVector) :
    ElkGraph × NodeId × LabelId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n) := g.createNode (some root)
  let g := g.modifyNode n fun nd => { nd with width := 10.0, height := 10.0 }
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_CONSTRAINTS constraints
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_MINIMUM minimum
  let g := g.setNodeProp n CoreOptions.NODE_LABELS_PLACEMENT (EnumSet.of #[NodeLabelPlacement.inside, .vCenter, .hCenter])
  let (g, l) := g.createLabel (some (.node n)) "label"
  return (g.modifyLabel l fun lb => { lb with width := 20.0, height := 10.0 }, n, l)

def nodeSizeCalculatorTests : Suite := suite "alg.common.nodespacing.internal.algorithm.NodeSizeCalculator" do
  -- fixed size
  let (g, n) := eastPortGraph EnumSet.empty .free
  let ((ctx, _), _) ← withContext g n fun a ctx => do return (← sizeNode a ctx, ())
  checkVec "fixed size: node keeps 60x40" ctx.nodeSize 60.0 40.0
  checkRect "fixed size: node container gets (0, 0, 60, 40)" (ctx.cells.cellRectangle ctx.nodeContainer) 0.0 0.0 60.0 40.0
  let (g, n) := eastPortGraph (EnumSet.of #[SizeConstraint.portLabels]) .free
  let ((ctx, _), _) ← withContext g n fun a ctx => do return (← sizeNode a ctx, ())
  checkVec "{PORT_LABELS} is effectively fixed" ctx.nodeSize 60.0 40.0
  -- PORTS + PORT_LABELS, free ports
  let (g, n) := eastPortGraph (EnumSet.of #[SizeConstraint.ports, .portLabels]) .free
  let ((ctx, _), _) ← withContext g n fun a ctx => do return (← sizeNode a ctx, ())
  checkFloat "hand: width = middle row, symmetric EAST/WEST (8 + 1) * 2 = 18" ctx.nodeSize.x 18.0
  checkFloat "hand: height = EAST/WEST cells 0 + top 1 + bottom 3 (after the padding update)" ctx.nodeSize.y 4.0
  checkRect "hand: EAST cell (9, 0, 9, 4)" (ctx.cells.cellRectangleOpt (ctx.insidePortLabelCell .east)) 9.0 0.0 9.0 4.0
  checkRect "hand: WEST cell gets the symmetric width (0, 0, 9, 4)"
    (ctx.cells.cellRectangleOpt (ctx.insidePortLabelCell .west)) 0.0 0.0 9.0 4.0
  -- PORTS with FIXED_POS: east/west heights are added by hand
  let (g, n) := eastPortGraph (EnumSet.of #[SizeConstraint.ports]) .fixedPos
  let ((ctx, _), _) ← withContext g n fun a ctx => do return (← sizeNode a ctx, ())
  checkFloat "hand: FIXED_POS width = NORTH cell margins 1 + 3" ctx.nodeSize.x 4.0
  checkFloat "hand: FIXED_POS height = EAST cell 0 + 2 + 4" ctx.nodeSize.y 6.0
  -- NODE_SIZE_FIXED_GRAPH_SIZE on the parent: never shrink the node
  let gG := g.setNodeProp ((g.node n).parent.getD n) CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE true
  let ((ctx, _), _) ← withContext gG n fun a ctx => do return (← sizeNode a ctx, ())
  checkVec "fixed graph size: node keeps 60x40" ctx.nodeSize 60.0 40.0
  checkRect "fixed graph size: the cell system still gets the computed 4x6"
    (ctx.cells.cellRectangle ctx.nodeContainer) 0.0 0.0 4.0 6.0
  -- top-down layout: at least the current size
  let gT := g.setNodeProp n CoreOptions.TOPDOWN_LAYOUT true
  let ((ctx, _), _) ← withContext gT n fun a ctx => do return (← sizeNode a ctx, ())
  checkVec "top-down layout: max(current, computed)" ctx.nodeSize 60.0 40.0
  -- NODE_LABELS with one IN_C_C label 20x10 (NODE_LABELS_PADDING 5)
  let (g, n, _) := insideLabelGraph (EnumSet.of #[SizeConstraint.nodeLabels]) KVector.zero
  let ((ctx, _), _) ← withContext g n fun a ctx => do return (← sizeNode a ctx, ())
  checkFloat "hand: NODE_LABELS width = 20 + padding 5 + 5" ctx.nodeSize.x 30.0
  checkFloat "hand: NODE_LABELS height = 10 + padding 5 + 5" ctx.nodeSize.y 20.0
  -- with a minimum size
  let (g, n, _) := insideLabelGraph (EnumSet.of #[SizeConstraint.nodeLabels, .minimumSize]) ⟨50.0, 40.0⟩
  let ((ctx, _), _) ← withContext g n fun a ctx => do return (← sizeNode a ctx, ())
  checkVec "hand: MINIMUM_SIZE 50x40 wins over 30x20" ctx.nodeSize 50.0 40.0
  checkRect "hand: IN_C_C cell = grid content area (5, 5, 40, 30)" (ctx.cells.cellRectangleOpt (ctx.nodeLabelCell .inCC))
    5.0 5.0 40.0 30.0

/-! ### LabelPlacer -/

def labelPlacerTests : Suite := suite "alg.common.nodespacing.internal.algorithm.LabelPlacer" do
  -- inside centered label in a 50x40 node
  let (g, n, l) := insideLabelGraph (EnumSet.of #[SizeConstraint.nodeLabels, .minimumSize]) ⟨50.0, 40.0⟩
  let ((ctx, positions), g') ← withContext g n fun a ctx => do
    let ctx ← sizeNode a ctx
    let (_, positions) := LabelPlacer.placeLabelsPure ctx
    let ctx ← LabelPlacer.placeLabels a ctx
    return (ctx, positions)
  checkEqR "placeLabelsPure: one label" (positions.map (·.1)) #[l]
  checkVec "hand: centered label at ((50 - 20) / 2, (40 - 10) / 2)" positions[0]!.2 15.0 15.0
  let lb := g'.label l
  checkVec "placeLabels writes the position through the adapter" ⟨lb.x, lb.y⟩ 15.0 15.0
  checkEq "label cells to place: the IN_C_C cell" (LabelPlacer.labelCellsToPlace ctx).size 1
  -- outside label above a fixed-size node (60x40): OUT_T_C 12x4 of configGraph
  let (g, n, _, outside) := configGraph EnumSet.empty EnumSet.empty .free
  let ((ctx, _), g') ← withContext g n fun a ctx => do
    let ctx ← sizeNode a ctx
    return (← LabelPlacer.placeLabels a ctx, ())
  checkRect "hand: NORTH container = (-(60 - 60) / 2, -(4 + 5), 60, 4 + 5)"
    (ctx.cells.cellRectangleOpt (ctx.outsideNodeLabelContainer .north)) 0.0 (-9.0) 60.0 9.0
  let lb := g'.label outside
  checkVec "hand: OUT_T_C label centered above the node, 5 away: ((60 - 12) / 2, -9)" ⟨lb.x, lb.y⟩ 24.0 (-9.0)
  -- a label wider than a fixed-size node: the label cell does not contribute its width (size
  -- contributions are not configured for fixed sizes), so the container keeps the node width and
  -- the strip's center cell grows symmetrically around it
  let gW := g.modifyLabel outside fun lb => { lb with width := 80.0 }
  let ((ctxW, _), gW') ← withContext gW n fun a ctx => do
    let ctx ← sizeNode a ctx
    return (← LabelPlacer.placeLabels a ctx, ())
  checkRect "hand: NORTH container keeps the node width (0, -9, 60, 9)"
    (ctxW.cells.cellRectangleOpt (ctxW.outsideNodeLabelContainer .north)) 0.0 (-9.0) 60.0 9.0
  checkVec "hand: wide label centered on the node: x = -(80 - 60) / 2" ⟨(gW'.label outside).x, (gW'.label outside).y⟩
    (-10.0) (-9.0)
  -- container placement with a contributing outside label (NODE_LABELS) on a node made narrower
  -- than the label afterwards: clipped to the node width unless labels may overhang
  let (gN, nN, _, _) := configGraph (EnumSet.of #[SizeConstraint.nodeLabels]) EnumSet.empty .free
  let ((ctxN, _), _) ← withContext gN nN fun a ctx => do return (← sizeNode a ctx, ())
  checkFloat "hand: NODE_LABELS width = inside label 20 + padding 10" ctxN.nodeSize.x 30.0
  let narrow : Ctx := { ctxN with nodeSize := ⟨10.0, 40.0⟩ }
  let clipped := LabelPlacer.placeOuterNodeLabelContainers narrow
  checkRect "hand: NORTH container min width 12 clipped to the node width 10"
    (clipped.cells.cellRectangleOpt (clipped.outsideNodeLabelContainer .north)) 0.0 (-9.0) 10.0 9.0
  checkRect "hand: empty EAST container right of the node with the node height"
    (clipped.cells.cellRectangleOpt (clipped.outsideNodeLabelContainer .east)) 10.0 0.0 0.0 40.0
  let overhanging := LabelPlacer.placeOuterNodeLabelContainers
    { narrow with sizeOptions := EnumSet.of #[SizeOptions.outsideNodeLabelsOverhang] }
  checkRect "hand: overhanging NORTH container keeps 12, centered: x = -(12 - 10) / 2"
    (overhanging.cells.cellRectangleOpt (overhanging.outsideNodeLabelContainer .north)) (-1.0) (-9.0) 12.0 9.0

def suites : Array Tests.Suite := #[
  portContextCreatorTests, nodeLabelCellCreatorTests, insidePortLabelCellCreatorTests,
  cellSystemConfiguratorTests, nodeSizeCalculatorTests, labelPlacerTests]

end Tests.AlgCommon.NodeSpacing.AlgorithmCells
