import Tests.Framework
import Elk.Alg.Common
/-! Tests of `nodespacing.cellsystem`, `nodespacing.internal` (NodeLabelLocation, PortContext,
NodeContext) and `internal.algorithm.NodeLabelAndSizeUtilities` (task N1).

elk-rs has no unit test for these files (`cellsystem_process_test.rs` needs the layered
algorithm), so every expected number is derived by hand from the Java/elk-rs formulas; the check
names say which formula ("hand:" prefix). -/
namespace Tests.AlgCommon.NodeSpacing.CellSystem

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal
open Elk.Alg.Common.NodeSpacing.Internal.Algorithm

private def close (a b : Float) : Bool := (a - b).abs <= 1e-9

private def checkRect (name : String) (r : ElkRectangle) (x y w h : Float) : TestM Unit :=
  report name (close r.x x && close r.y y && close r.width w && close r.height h)
    s!"expected ({x}, {y}, {w}, {h}), got {r}"

private def checkVec (name : String) (v : KVector) (x y : Float) : TestM Unit :=
  report name (close v.x x && close v.y y) s!"expected ({x}, {y}), got {v}"

private def checkPadding (name : String) (p : ElkPadding) (top right bottom left : Float) : TestM Unit :=
  report name (close p.top top && close p.right right && close p.bottom bottom && close p.left left)
    s!"expected [t={top}, r={right}, b={bottom}, l={left}], got {p}"

/-- An atomic cell with the given content size and contribution flags. -/
private def atomic (a : CellArena Nat) (cx cy : Float) (cw ch : Bool := true) : CellArena Nat × CellId :=
  let (a, c) := a.createAtomic
  let a := a.setMinimumContentAreaSize c ⟨cx, cy⟩ false
  let a := a.setContributesToMinimumWidth c cw
  (a.setContributesToMinimumHeight c ch, c)

def atomicCellTests : Suite := suite "alg.common.nodespacing.cellsystem.AtomicCell" do
  let (a, c) := (CellArena.empty : CellArena Nat).createAtomic
  let a := a.setPadding c (ElkPadding.ofValues 1.0 2.0 3.0 4.0)
  let a := a.setMinimumContentAreaSize c ⟨10.0, 20.0⟩ false
  checkFloat "hand: minimumWidth = content.x + left + right" (a.minimumWidth c) 16.0
  checkFloat "hand: minimumHeight = content.y + top + bottom" (a.minimumHeight c) 24.0
  let a := a.setMinimumContentAreaSize c ⟨30.0, 40.0⟩ true
  checkVec "hand: setMinimumContentAreaSize(includesPadding) subtracts padding" (a.minimumContentAreaSize c) 24.0 36.0
  checkFloat "hand: minimumWidth after padding-inclusive size" (a.minimumWidth c) 30.0
  check "defaults: no size contributions" (!a.isContributingToMinimumWidth c && !a.isContributingToMinimumHeight c)
  check "layoutChildren* is a no-op on atomic cells"
    (close (a.layoutChildrenHorizontally c |>.cellRectangle c).width 0.0)

def stripContainerTests : Suite := suite "alg.common.nodespacing.cellsystem.StripContainerCell" do
  -- Horizontal strip, gap 5, padding t3 r2 b4 l1; begin (10,6) contributes both, center (4,2)
  -- contributes nothing, end (20,8) contributes width only.
  let (a, s) := (CellArena.empty : CellArena Nat).createStrip .horizontal false 5.0
  let a := a.setPadding s (ElkPadding.ofValues 3.0 2.0 4.0 1.0)
  let (a, b) := atomic a 10.0 6.0
  let (a, m) := atomic a 4.0 2.0 false false
  let (a, e) := atomic a 20.0 8.0 true false
  let a := a.setCell s .begin (some b)
  let a := a.setCell s .center (some m)
  let a := a.setCell s .«end» (some e)
  checkEqR "getCell(END)" (a.getCell s .«end») (some e)
  checkFloat "hand: horizontal minimumWidth = 10 + 20 + gap 5 + padding 3" (a.minimumWidth s) 38.0
  checkFloat "hand: horizontal minimumHeight = max contributing height 6 + padding 7" (a.minimumHeight s) 13.0
  -- Layout in the rectangle (100, 50, 100, 30)
  let a := a.setCellRectangle s { x := 100.0, y := 50.0, width := 100.0, height := 30.0 }
  let a := a.layoutChildrenHorizontally s
  let a := a.layoutChildrenVertically s
  checkRect "hand: begin cell left-aligned (101, 53, 10, 23)" (a.cellRectangle b) 101.0 53.0 10.0 23.0
  checkRect "hand: end cell right-aligned (178, 53, 20, 23)" (a.cellRectangle e) 178.0 53.0 20.0 23.0
  checkRect "hand: center cell fills free space (116, 53, 57, 23)" (a.cellRectangle m) 116.0 53.0 57.0 23.0
  -- Symmetrical variant: outer widths become max(10, 20) = 20
  let (a2, s2) := (CellArena.empty : CellArena Nat).createStrip .horizontal true 5.0
  let a2 := a2.setPadding s2 (ElkPadding.ofValues 3.0 2.0 4.0 1.0)
  let (a2, b2) := atomic a2 10.0 6.0
  let (a2, e2) := atomic a2 20.0 8.0 true false
  let a2 := (a2.setCell s2 .begin (some b2)).setCell s2 .«end» (some e2)
  checkFloat "hand: symmetrical minimumWidth = 20 + 20 + 5 + 3" (a2.minimumWidth s2) 48.0
  let a2 := a2.setContributesToMinimumWidth b2 false
  checkFloat "hand: symmetry only uses contributing widths: 20 + 20 + 5 + 3" (a2.minimumWidth s2) 48.0
  let a2' := (a2.setCell s2 .«end» none)
  checkFloat "hand: no contributing cell -> minimumWidth 0 (no padding)" (a2'.minimumWidth s2) 0.0
  -- Vertical strip, gap 2, symmetrical, padding 1: rows (5,10), (8,30), (5,4)
  let (v, vs) := (CellArena.empty : CellArena Nat).createStrip .vertical true 2.0
  let v := v.setPadding vs (ElkPadding.ofAny 1.0)
  let (v, r0) := atomic v 5.0 10.0 false true
  let (v, r1) := atomic v 8.0 30.0 true true
  let (v, r2) := atomic v 5.0 4.0 false true
  let v := ((v.setCell vs .begin (some r0)).setCell vs .center (some r1)).setCell vs .«end» (some r2)
  checkFloat "hand: vertical minimumHeight = 10 + 30 + 10 (symmetry) + 2*2 + 2" (v.minimumHeight vs) 56.0
  checkFloat "hand: vertical minimumWidth = max contributing width 8 + 2" (v.minimumWidth vs) 10.0
  let v1 := v.setCellRectangle vs { width := 50.0, height := 100.0 }
  let v1 := (v1.layoutChildrenHorizontally vs).layoutChildrenVertically vs
  checkRect "hand: vertical strip top row (1, 1, 48, 10)" (v1.cellRectangle r0) 1.0 1.0 48.0 10.0
  checkRect "hand: vertical strip bottom row (1, 89, 48, 10)" (v1.cellRectangle r2) 1.0 89.0 48.0 10.0
  checkRect "hand: vertical strip center row (1, 13, 48, 74)" (v1.cellRectangle r1) 1.0 13.0 48.0 74.0
  let v2 := (v.setCellRectangle vs { width := 50.0, height := 40.0 }).layoutChildrenVertically vs
  checkRect "hand: too small strip centers the overflowing middle row (y = 13 - (30 - 14) / 2)"
    (v2.cellRectangle r1) 0.0 5.0 0.0 30.0
  -- Atomic cells without content width do not count in a horizontal strip, but do count by their
  -- padding in a vertical strip (minWidthOfCell vs. getMinimumWidth)
  let (z, zs) := (CellArena.empty : CellArena Nat).createStrip .horizontal false 0.0
  let (z, zc) := atomic z 0.0 3.0
  let z := (z.setPadding zc (ElkPadding.ofValues 0.0 0.0 0.0 7.0)).setCell zs .begin (some zc)
  checkFloat "hand: minWidthOfCell ignores zero-width atomic cells" (z.minimumWidth zs) 0.0
  let (z, zv) := z.createStrip .vertical false 0.0
  let z := z.setCell zv .begin (some zc)
  checkFloat "hand: vertical strip takes the child's getMinimumWidth (padding 7)" (z.minimumWidth zv) 7.0
  -- Nested strips: the outer layout recurses into the middle row
  let (n, outer) := (CellArena.empty : CellArena Nat).createStrip .vertical false 0.0
  let (n, inner) := n.createStrip .horizontal false 0.0
  let (n, ib) := atomic n 6.0 3.0 true false
  let (n, ie) := atomic n 4.0 3.0 true false
  let n := ((n.setCell outer .center (some inner)).setCell inner .begin (some ib)).setCell inner .«end» (some ie)
  let n := n.setCellRectangle outer { width := 40.0, height := 20.0 }
  let n := (n.layoutChildrenHorizontally outer).layoutChildrenVertically outer
  checkRect "hand: nested strip layout reaches grandchildren (end cell at x = 36)" (n.cellRectangle ie) 36.0 0.0 4.0 20.0
  checkRect "hand: nested strip begin cell (0, 0, 6, 20)" (n.cellRectangle ib) 0.0 0.0 6.0 20.0

/-- A grid with (BEGIN,BEGIN) (10,5), (BEGIN,END) (6,5), (CENTER,CENTER) (20,8), (END,CENTER) (12,4),
all contributing, gap 3, padding 2. -/
private def sampleGrid (tabular symmetrical : Bool) : CellArena Nat × CellId × Array CellId :=
  let (a, g) := (CellArena.empty : CellArena Nat).createGrid tabular symmetrical 3.0
  let a := a.setPadding g (ElkPadding.ofAny 2.0)
  let (a, bb) := atomic a 10.0 5.0
  let (a, be) := atomic a 6.0 5.0
  let (a, cc) := atomic a 20.0 8.0
  let (a, ec) := atomic a 12.0 4.0
  let a := a.setGridCell g .begin .begin (some bb)
  let a := a.setGridCell g .begin .«end» (some be)
  let a := a.setGridCell g .center .center (some cc)
  let a := a.setGridCell g .«end» .center (some ec)
  (a, g, #[bb, be, cc, ec])

def gridContainerTests : Suite := suite "alg.common.nodespacing.cellsystem.GridContainerCell" do
  let (a, g, ids) := sampleGrid false false
  checkEqR "getGridCell(CENTER, CENTER)" (a.getGridCell g .center .center) (some ids[2]!)
  checkFloat "hand: non-tabular minimumWidth = max row (20) + padding 4" (a.minimumWidth g) 24.0
  checkFloat "hand: minimumHeight = 5 + 8 + 4 + 2 gaps + padding 4" (a.minimumHeight g) 27.0
  let (t, tg, tids) := sampleGrid true false
  checkFloat "hand: tabular minimumWidth = 10 + 20 + 6 + 2 gaps + 4" (t.minimumWidth tg) 46.0
  let (s, sg, _) := sampleGrid true true
  checkFloat "hand: symmetrical tabular minimumWidth = 10 + 20 + 10 + 6 + 4" (s.minimumWidth sg) 50.0
  checkFloat "hand: symmetrical minimumHeight = 5 + 8 + 5 + 6 + 4" (s.minimumHeight sg) 28.0
  let m := a.setCenterCellMinimumSize g ⟨30.0, 10.0⟩
  checkFloat "hand: center minimum size widens the center column (10 + 30 + 6 + 6 + 4)" (m.minimumWidth g) 56.0
  checkFloat "hand: center minimum size heightens the center row (5 + 10 + 4 + 6 + 4)" (m.minimumHeight g) 29.0
  let o := m.setOnlyCenterCellContributesToMinimumSize g true
  checkFloat "hand: only-center with minimum size: 30 + 4" (o.minimumWidth g) 34.0
  checkFloat "hand: only-center with minimum size: 10 + 4" (o.minimumHeight g) 14.0
  let o2 := a.setOnlyCenterCellContributesToMinimumSize g true
  checkFloat "hand: only-center without minimum size uses the center cell: 20 + 4" (o2.minimumWidth g) 24.0
  -- Tabular layout in (0, 0, 100, 60)
  let t := t.setCellRectangle tg { width := 100.0, height := 60.0 }
  let t := (t.layoutChildrenHorizontally tg).layoutChildrenVertically tg
  -- Java hands one `colWidths` array ([10, 20, 6]) to the three rows and `applyWidthsToRow` updates
  -- it in place: row BEGIN leaves [13, 74, 9], row CENTER [16, 74, 12] (free width 68), row END
  -- applies widths 16 / 12 to the outer columns (elk-rs copies the array: 10 / 6, free width 74)
  checkRect "Java: tabular (BEGIN,BEGIN) = (2, 2, 16, 5) (accumulated gaps)" (t.cellRectangle tids[0]!) 2.0 2.0 16.0 5.0
  checkRect "Java: tabular (BEGIN,END) = (86, 2, 12, 5) (accumulated gaps)" (t.cellRectangle tids[1]!) 86.0 2.0 12.0 5.0
  checkRect "hand: tabular (CENTER,CENTER) = (15, 10, 74, 41)" (t.cellRectangle tids[2]!) 15.0 10.0 74.0 41.0
  checkRect "hand: tabular (END,CENTER) = (15, 54, 74, 4)" (t.cellRectangle tids[3]!) 15.0 54.0 74.0 4.0
  checkRect "Java: center cell rectangle from the CENTER row's free width (2, 2, 68, 41)"
    (t.centerCellRectangle tg) 2.0 2.0 68.0 41.0
  -- Non-tabular: the END row's column widths are applied last to every row (Java/elk-rs quirk)
  let a := a.setCellRectangle g { width := 100.0, height := 60.0 }
  let a := a.layoutChildrenHorizontally g
  checkRect "hand: non-tabular (BEGIN,BEGIN) gets the END row's empty column (2, 0, 0, 0)"
    (a.cellRectangle ids[0]!) 2.0 0.0 0.0 0.0
  checkRect "hand: non-tabular (CENTER,CENTER) spans the content width (2, 0, 96, 0)"
    (a.cellRectangle ids[2]!) 2.0 0.0 96.0 0.0

def labelCellTests : Suite := suite "alg.common.nodespacing.cellsystem.LabelCell" do
  let (a, l) := (CellArena.empty : CellArena Nat).createLabel 2.0
  let a := (a.addLabel l 1 ⟨10.0, 4.0⟩).addLabel l 2 ⟨6.0, 3.0⟩
  let a := a.setPadding l (ElkPadding.ofAny 1.0)
  check "hasLabels" (a.hasLabels l)
  checkFloat "hand: horizontal mode minimumWidth = max width 10 + 2" (a.minimumWidth l) 12.0
  checkFloat "hand: horizontal mode minimumHeight = 4 + 3 + gap 2 + 2" (a.minimumHeight l) 11.0
  let a := a.setCellRectangle l { x := 100.0, y := 200.0, width := 30.0, height := 20.0 }
  let pos := a.applyLabelLayout l
  checkEq "applyLabelLayout keeps label order" (pos.map (·.1)) #[1, 2]
  checkVec "hand: centered first label (111, 205.5)" pos[0]!.2 111.0 205.5
  checkVec "hand: centered second label (113, 211.5)" pos[1]!.2 113.0 211.5
  let lt := (a.setHorizontalAlignment l .left).setVerticalAlignment l .top
  let pos := lt.applyLabelLayout l
  checkVec "hand: left/top first label (101, 200)" pos[0]!.2 101.0 200.0
  checkVec "hand: left/top second label (101, 206)" pos[1]!.2 101.0 206.0
  let rb := (a.setHorizontalAlignment l .right).setVerticalAlignment l .bottom
  let pos := rb.applyLabelLayout l
  checkVec "hand: right/bottom first label (119, 211)" pos[0]!.2 119.0 211.0
  checkVec "hand: right/bottom second label (123, 217)" pos[1]!.2 123.0 217.0
  -- Vertical layout mode
  let (v, vl) := (CellArena.empty : CellArena Nat).createLabel 2.0 false
  let v := (v.addLabel vl 7 ⟨10.0, 4.0⟩).addLabel vl 8 ⟨6.0, 3.0⟩
  checkFloat "hand: vertical mode minimumWidth = 10 + 6 + gap 2" (v.minimumWidth vl) 18.0
  checkFloat "hand: vertical mode minimumHeight = max height 4" (v.minimumHeight vl) 4.0
  let v := v.setCellRectangle vl { width := 40.0, height := 10.0 }
  let pos := v.applyLabelLayout vl
  checkVec "hand: vertical mode centered first label (11, 3)" pos[0]!.2 11.0 3.0
  checkVec "hand: vertical mode centered second label (23, 3.5)" pos[1]!.2 23.0 3.5
  let vr := (v.setHorizontalAlignment vl .right).setVerticalAlignment vl .top
  let pos := vr.applyLabelLayout vl
  checkVec "hand: vertical mode right/top second label (34, 0)" pos[1]!.2 34.0 0.0
  let posM := Id.run (v.applyLabelLayoutM vl fun n => pure (if n == 7 then KVector.mk' 10.0 4.0 else ⟨6.0, 3.0⟩))
  check "applyLabelLayoutM with unchanged sizes = applyLabelLayout"
    ((posM.map (·.2.x)) == ((v.applyLabelLayout vl).map (·.2.x)))
  checkEq "applyLabelLayout on a non-label cell is empty" (v.applyLabelLayout ⟨99⟩).size 0

def nodeLabelLocationTests : Suite := suite "alg.common.nodespacing.internal.NodeLabelLocation" do
  checkEq "22 constants" (ElkEnum.count (α := NodeLabelLocation)) 22
  checkEq "allDefined excludes UNDEFINED" NodeLabelLocation.allDefined.size 21
  checkEq "Java name OUT_T_L" (ElkEnum.javaName NodeLabelLocation.outTL) "OUT_T_L"
  checkEq "inside top left" (NodeLabelLocation.fromNodeLabelPlacement (EnumSet.of #[.inside, .vTop, .hLeft])) .inTL
  checkEq "inside center with H_PRIORITY"
    (NodeLabelLocation.fromNodeLabelPlacement (EnumSet.of #[.inside, .vCenter, .hCenter, .hPriority])) .inCC
  checkEq "outside top center" (NodeLabelLocation.fromNodeLabelPlacement (EnumSet.of #[.outside, .vTop, .hCenter])) .outTC
  checkEq "outside H_LEFT V_TOP without priority = OUT_T_L"
    (NodeLabelLocation.fromNodeLabelPlacement (EnumSet.of #[.outside, .hLeft, .vTop])) .outTL
  checkEq "outside H_LEFT V_TOP with priority = OUT_L_T"
    (NodeLabelLocation.fromNodeLabelPlacement (EnumSet.of #[.outside, .hLeft, .vTop, .hPriority])) .outLT
  checkEq "outside bottom right" (NodeLabelLocation.fromNodeLabelPlacement (EnumSet.of #[.outside, .hRight, .vBottom])) .outBR
  checkEq "fixed placement = UNDEFINED" (NodeLabelLocation.fromNodeLabelPlacement NodeLabelPlacement.fixed) .undefined
  checkEq "incomplete placement = UNDEFINED" (NodeLabelLocation.fromNodeLabelPlacement (EnumSet.of #[.inside, .vTop])) .undefined
  checkEqR "OUT_L_T data" (NodeLabelLocation.outLT.horizontalAlignment, NodeLabelLocation.outLT.verticalAlignment,
      NodeLabelLocation.outLT.containerRow, NodeLabelLocation.outLT.containerColumn)
    (some HorizontalLabelAlignment.right, some VerticalLabelAlignment.top, some ContainerArea.begin, some ContainerArea.begin)
  checkEq "OUT_L_T outside side" NodeLabelLocation.outLT.outsideSide .west
  checkEq "OUT_B_C outside side" NodeLabelLocation.outBC.outsideSide .south
  check "IN_B_R is inside, OUT_R_C is not" (NodeLabelLocation.inBR.isInsideLocation && !NodeLabelLocation.outRC.isInsideLocation)
  checkEq "IN_B_R has no outside side" NodeLabelLocation.inBR.outsideSide .undefined
  checkEqR "UNDEFINED has no alignment" NodeLabelLocation.undefined.horizontalAlignment none
  check "every defined location maps back to itself"
    (NodeLabelLocation.allDefined.all fun l => l.assignedPlacements.all (NodeLabelLocation.fromNodeLabelPlacement · == l))

/-- Graph for the context tests: root (SPACING_LABEL_LABEL 3, SPACING_PORT_PORT 7,
NODE_SIZE_FIXED_GRAPH_SIZE) ⊃ node `n` (40×30, options below, one child `c`, seven ports). -/
private def contextGraph : ElkGraph × NodeId × NodeId × Array PortId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root CoreOptions.SPACING_LABEL_LABEL 3.0
  let g := g.setNodeProp root CoreOptions.SPACING_PORT_PORT 7.0
  let g := g.setNodeProp root CoreOptions.NODE_SIZE_FIXED_GRAPH_SIZE true
  let (g, n) := g.createNode (some root)
  let g := g.modifyNode n fun nd => { nd with width := 40.0, height := 30.0 }
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.ports, .nodeLabels])
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_OPTIONS (EnumSet.of #[SizeOptions.asymmetrical])
  let g := g.setNodeProp n CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedOrder
  let g := g.setNodeProp n CoreOptions.PORT_ALIGNMENT_NORTH PortAlignment.center
  let g := g.setNodeProp n CoreOptions.PORT_ALIGNMENT_DEFAULT PortAlignment.begin
  let g := g.setNodeProp n CoreOptions.PORT_LABELS_PLACEMENT (EnumSet.of #[PortLabelPlacement.inside])
  let individual : IndividualSpacings := { props := ({} : PropertyMap).set CoreOptions.SPACING_PORT_PORT 12.0 }
  let g := g.setNodeProp n CoreOptions.SPACING_INDIVIDUAL individual
  let (g, c) := g.createNode (some n)
  let mut g := g
  let mut ports : Array PortId := #[]
  for side in #[PortSide.north, .south, .east, .south, .west, .north, .west] do
    let (g', p) := g.createPort (some n)
    g := g'.setPortProp p CoreOptions.PORT_SIDE side
    ports := ports.push p
  return (g, n, c, ports)

/-- Port context of `p` from the adapters (volatile id set to `vid`). -/
private def portContextOf (a : ElkAdapters) (p : PortId) (vid : Int) : ElkM (PortContext PortId LabelId) := do
  a.port.setVolatileId p vid
  let labels ← a.portLabels p
  let mut sizes := #[]
  let mut positions := #[]
  for l in labels do
    sizes := sizes.push (← a.label.getSize l)
    positions := positions.push (← a.label.getPosition l)
  let pc : PortContext PortId LabelId := PortContext.new p (← a.port.getSize p) (← a.portSide p) (← a.port.getVolatileId p) (← a.port.getPosition p)
    (← a.port.getPropertyD p CoreOptions.PORT_BORDER_OFFSET 0.0) (← a.port.hasProp p CoreOptions.PORT_BORDER_OFFSET)
    (← a.hasCompoundConnections p)
  return { pc with labels := labels, labelSizes := sizes, labelPositions := positions }

def nodeContextTests : Suite := suite "alg.common.nodespacing.internal.NodeContext" do
  let (g, n, c, ports) := contextGraph
  let a ← ElkGraphAdapters.new
  let ((ctx, cctx, pcs), _) ← ElkM.run (do
      let ctx ← NodeContext.new a n
      let cctx ← NodeContext.new a c
      let mut pcs := #[]
      let mut vid : Int := 0
      for p in (← a.nodePorts n) do
        pcs := pcs.push (← portContextOf a p vid)
        vid := vid + 1
      return (ctx, cctx, pcs)) g
  checkVec "nodeSize copied" ctx.nodeSize 40.0 30.0
  check "compound node (has a child)" ctx.treatAsCompoundNode
  check "size constraints {PORTS, NODE_LABELS}"
    (ctx.sizeConstraints == EnumSet.of #[SizeConstraint.ports, .nodeLabels])
  check "size options {ASYMMETRICAL}" (ctx.sizeOptions.contains .asymmetrical)
  checkEq "port constraints" ctx.portConstraints .fixedOrder
  checkFloat "SPACING_LABEL_LABEL inherited from the parent graph" ctx.labelLabelSpacing 3.0
  checkFloat "labelCellSpacing = 2 * labelLabelSpacing" ctx.labelCellSpacing 6.0
  checkFloat "SPACING_PORT_PORT from SPACING_INDIVIDUAL beats the parent" ctx.portPortSpacing 12.0
  checkFloat "SPACING_LABEL_NODE default" ctx.nodeLabelSpacing 5.0
  checkFloat "SPACING_LABEL_PORT_HORIZONTAL default" ctx.portLabelSpacingHorizontal 1.0
  checkPadding "NODE_LABELS_PADDING default" ctx.nodeLabelsPadding 5.0 5.0 5.0 5.0
  check "NODE_SIZE_FIXED_GRAPH_SIZE read from the parent graph" ctx.nodeSizeFixedGraphSize
  checkEq "PORT_ALIGNMENT_NORTH explicitly set" (ctx.getPortAlignment .north) .center
  checkEq "SOUTH falls back to PORT_ALIGNMENT_DEFAULT" (ctx.getPortAlignment .south) .begin
  checkEqR "PORT_ALIGNMENT_EAST not set" ctx.portAlignmentEast none
  checkEq "node container is a vertical strip" (ctx.cells.containerMode ctx.nodeContainer) .vertical
  checkEqR "middle row is the container's center cell" (ctx.cells.getCell ctx.nodeContainer .center)
    (some ctx.nodeContainerMiddleRow)
  checkEq "middle row is a horizontal strip" (ctx.cells.containerMode ctx.nodeContainerMiddleRow) .horizontal
  check "ASYMMETRICAL -> non-symmetrical containers"
    (match ctx.cells.stripData? ctx.nodeContainer with | some d => !d.symmetrical | none => false)
  checkEqR "no inside node label container yet" ctx.insideNodeLabelContainer none
  -- the child: inherited spacings come from its own parent `n` only
  check "leaf child is not compound" (!cctx.treatAsCompoundNode)
  checkFloat "child: SPACING_LABEL_LABEL not set on its parent -> default 0" cctx.labelLabelSpacing 0.0
  check "child: parent has no NODE_SIZE_FIXED_GRAPH_SIZE" (!cctx.nodeSizeFixedGraphSize)
  checkEq "child: PORT_ALIGNMENT_DEFAULT property default" cctx.portAlignmentDefault .distributed
  check "child: PORT_LABELS_PLACEMENT default {OUTSIDE}" (cctx.portLabelsPlacement == PortLabelPlacement.outsideSet)
  check "child: default NODE_SIZE_OPTIONS {DEFAULT_MINIMUM_SIZE}"
    (cctx.sizeOptions == EnumSet.of #[SizeOptions.defaultMinimumSize])
  check "child: symmetrical containers"
    (match cctx.cells.stripData? cctx.nodeContainer with | some d => d.symmetrical | none => false)
  -- Port context order (TreeMultimap): insert in reverse order
  let ctxT := pcs.reverse.foldl (fun c pc => c.insertPortContext pc) ctx
  let order (cx : NodeContext NodeId PortId LabelId) : Array Nat :=
    cx.allPortContexts.map fun pc => (ports.findIdx? (· == pc.port)).getD 99
  checkEq "TreeMultimap order: N asc, E, S desc, W desc" (order ctxT) #[0, 5, 2, 3, 1, 6, 4]
  checkEq "portContextsOf(SOUTH) descending volatile ids" ((ctxT.portContextsOf .south).map (·.volatileId)) #[3, 1]
  -- elk-rs PortContextCreator: append in port order, then reverse SOUTH and WEST
  let ctxR := pcs.foldl (fun c pc => c.addPortContext pc) ctx
  let ctxR := (ctxR.modifyPortContextsOf .south (·.reverse)).modifyPortContextsOf .west (·.reverse)
  checkEq "append + reverse S/W gives the same order" (order ctxR) #[0, 5, 2, 3, 1, 6, 4]
  check "first south port label placed differently (2 ports, not next to port)"
    (NodeLabelAndSizeUtilities.isFirstOutsidePortLabelPlacedDifferently ctxT .south)
  check "a single east port is never placed differently"
    (!NodeLabelAndSizeUtilities.isFirstOutsidePortLabelPlacedDifferently ctxT .east)
  let ctxA := { ctxT with portLabelsPlacement := EnumSet.of #[.inside, .alwaysSameSide] }
  check "ALWAYS_SAME_SIDE prevents a different first label"
    (!NodeLabelAndSizeUtilities.isFirstOutsidePortLabelPlacedDifferently ctxA .south)
  -- shared cells: registering the same CellId in two places sees one cell
  let (cells, w) := ctxT.cells.createAtomic
  let ctxW : NodeContext NodeId PortId LabelId := { ctxT with cells }
  let ctxW := (ctxW.setInsidePortLabelCell .west (some w)).modifyCells
    (·.setCell ctxT.nodeContainerMiddleRow .begin (some w))
  let ctxW := ctxW.modifyCells (·.setCellRectangle w { x := 3.0, width := 4.0 })
  checkRect "insidePortLabelCells and the middle row share the cell"
    ((ctxW.cells.cellRectangleOpt (ctxW.insidePortLabelCell .west))) 3.0 0.0 4.0 0.0

/-- Graph for the utility tests: node `u` (100×50) with fixed port labels and
`{COMPUTE_PADDING, MINIMUM_SIZE_ACCOUNTS_FOR_PADDING}`, minimum size (30, 40); ports: north
(10×10, label at (0,5) sized 8×12), west (6×6, border offset -3), south (4×4 at (7,0)). -/
private def utilityGraph : ElkGraph × NodeId × PortId × PortId × PortId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let (g, u) := g.createNode (some root)
  let g := g.modifyNode u fun nd => { nd with width := 100.0, height := 50.0 }
  let g := g.setNodeProp u CoreOptions.PORT_LABELS_PLACEMENT PortLabelPlacement.fixed
  let g := g.setNodeProp u CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.minimumSize])
  let g := g.setNodeProp u CoreOptions.NODE_SIZE_OPTIONS
    (EnumSet.of #[SizeOptions.computePadding, .minimumSizeAccountsForPadding])
  let g := g.setNodeProp u CoreOptions.NODE_SIZE_MINIMUM ⟨30.0, 40.0⟩
  let (g, pn) := g.createPort (some u)
  let g := (g.setPortProp pn CoreOptions.PORT_SIDE PortSide.north).modifyPort pn fun p => { p with width := 10.0, height := 10.0 }
  let (g, l) := g.createLabel (some (.port pn)) "l"
  let g := g.modifyLabel l fun lb => { lb with x := 0.0, y := 5.0, width := 8.0, height := 12.0 }
  let (g, pw) := g.createPort (some u)
  let g := (g.setPortProp pw CoreOptions.PORT_SIDE PortSide.west).modifyPort pw fun p => { p with width := 6.0, height := 6.0 }
  let g := g.setPortProp pw CoreOptions.PORT_BORDER_OFFSET (-3.0)
  let (g, ps) := g.createPort (some u)
  let g := (g.setPortProp ps CoreOptions.PORT_SIDE PortSide.south).modifyPort ps fun p =>
    { p with width := 4.0, height := 4.0, x := 7.0 }
  return (g, u, pn, pw, ps)

def utilitiesTests : Suite := suite "alg.common.nodespacing.internal.algorithm.NodeLabelAndSizeUtilities" do
  let (g, u, _, _, ps) := utilityGraph
  let a ← ElkGraphAdapters.new
  let (ctx, g) ← ElkM.run (do
      let mut ctx ← NodeContext.new a u
      let mut vid : Int := 0
      for p in (← a.nodePorts u) do
        ctx := ctx.insertPortContext (← portContextOf a p vid)
        vid := vid + 1
      return ctx) g
  checkVec "hand: getMinimumNodeOrClientAreaSize = NODE_SIZE_MINIMUM"
    (NodeLabelAndSizeUtilities.getMinimumNodeOrClientAreaSize ctx) 30.0 40.0
  check "minimum size accounts for padding -> client area minimum, no node minimum"
    ((NodeLabelAndSizeUtilities.getMinimumClientAreaSize ctx).isSome &&
      (NodeLabelAndSizeUtilities.getMinimumNodeSize ctx).isNone)
  let ctxD := { ctx with sizeOptions := EnumSet.of #[.defaultMinimumSize], nodeSizeMinimum := ⟨0.0, 35.0⟩ }
  checkVec "hand: DEFAULT_MINIMUM_SIZE replaces a non-positive width by 20"
    ((NodeLabelAndSizeUtilities.getMinimumNodeSize ctxD).getD {}) 20.0 35.0
  check "{PORT_LABELS} counts as fixed size constraints"
    (NodeLabelAndSizeUtilities.areSizeConstraintsFixed { ctx with sizeConstraints := EnumSet.of #[.portLabels] })
  check "{PORTS} is not fixed"
    (!NodeLabelAndSizeUtilities.areSizeConstraintsFixed { ctx with sizeConstraints := EnumSet.of #[.ports] })
  -- Node padding for ports with offset / fixed labels
  let ctx := NodeLabelAndSizeUtilities.setupNodePaddingForPortsWithOffset ctx
  checkPadding "hand: north label inside part 12 + 5 - 10 = 7, mirrored south; west offset -3"
    (ctx.cells.padding ctx.nodeContainer) 7.0 0.0 7.0 3.0
  -- Inside node label container (normally created by NodeLabelCellCreator)
  let (cells, grid) := ctx.cells.createGrid false true 0.0
  let cells := (cells.setPadding grid (ElkPadding.ofAny 5.0)).setCell ctx.nodeContainerMiddleRow .center (some grid)
  let ctx := { ctx with cells }
  checkEqR "insideNodeLabelContainer finds the grid" ctx.insideNodeLabelContainer (some grid)
  let ctx := NodeLabelAndSizeUtilities.setupMinimumClientAreaSize ctx
  checkFloat "hand: client area minimum widens the grid: 30 + 10" (ctx.cells.minimumWidth grid) 40.0
  checkFloat "hand: client area minimum heightens the grid: 40 + 10" (ctx.cells.minimumHeight grid) 50.0
  -- Lay out the whole cell system in (0, 0, 100, 50)
  let ctx := ctx.modifyCells fun cs =>
    let cs := cs.setCellRectangle ctx.nodeContainer { width := 100.0, height := 50.0 }
    (cs.layoutChildrenHorizontally ctx.nodeContainer).layoutChildrenVertically ctx.nodeContainer
  checkRect "hand: middle row inside the node padding (3, 7, 97, 36)"
    (ctx.cells.cellRectangle ctx.nodeContainerMiddleRow) 3.0 7.0 97.0 36.0
  checkRect "hand: client area (8, 12, 87, 26)" (ctx.cells.centerCellRectangle grid) 8.0 12.0 87.0 26.0
  match NodeLabelAndSizeUtilities.computeNodePadding ctx with
  | some p => checkPadding "hand: computed node padding" p 12.0 5.0 12.0 8.0
  | none => report "computed node padding" false "expected some"
  check "no COMPUTE_PADDING -> no padding"
    (NodeLabelAndSizeUtilities.computeNodePadding { ctx with sizeOptions := EnumSet.empty }).isNone
  -- Southern ports and application
  let ctx := NodeLabelAndSizeUtilities.offsetSouthernPortsByNodeSize ctx
  checkVec "hand: southern port moved by the node height" (ctx.portContextsOf .south)[0]!.portPosition 7.0 50.0
  let ctx := { ctx with nodeSize := ⟨120.0, 50.0⟩ }
  let ((padding, width, southPos), _) ← ElkM.run (do
      NodeLabelAndSizeUtilities.setNodePadding a ctx
      NodeLabelAndSizeUtilities.applyStuff a ctx
      return (← ElkM.getNodeProp u CoreOptions.PADDING, (← ElkM.getNode u).width, (← ElkM.getPort ps).position)) g
  checkPadding "setNodePadding writes PADDING" (padding.getD {}) 12.0 5.0 12.0 8.0
  checkFloat "applyStuff applies the node size" width 120.0
  checkVec "applyStuff applies port positions" southPos 7.0 50.0

def suites : Array Tests.Suite :=
  #[atomicCellTests, stripContainerTests, gridContainerTests, labelCellTests, nodeLabelLocationTests,
    nodeContextTests, utilitiesTests]

end Tests.AlgCommon.NodeSpacing.CellSystem
