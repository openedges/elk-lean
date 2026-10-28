import Tests.Framework
import Elk.Alg.Common
/-! Tests of the port parts of `nodespacing.internal.algorithm` (task N2b):
`PortPlacementCalculator`, `Horizontal/VerticalPortPlacementSizeCalculator` and
`PortLabelPlacementCalculator`.

elk-rs has no unit tests for these files (the end-to-end `nodespacing_test.rs` needs the whole
calculator), so every expected number is derived by hand from the elk-rs formulas; the check names
say which formula ("hand:" prefix).

The node contexts are built from small `ElkGraph`s through `ElkGraphAdapters`. Port contexts and
inside port label cells are created by test stand-ins for N2a's `PortContextCreator` and
`InsidePortLabelCellCreator` (same rules as elk-rs, but without the creator's padding setup).

Shared spacings (set on the root): port-port 5, surrounding port margins (top 2, right 4,
bottom 6, left 3), label-port 2 (horizontal) / 3 (vertical), label-label 1, label-node 5. -/
namespace Tests.AlgCommon.NodeSpacing.AlgorithmPorts

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.Common.NodeSpacing.CellSystem Elk.Alg.Common.NodeSpacing.Internal
open Elk.Alg.Common.NodeSpacing.Internal.Algorithm

private abbrev Ctx := NodeContext NodeId PortId LabelId

private def close (a b : Float) : Bool := (a - b).abs <= 1e-9

private def checkFloats (name : String) (actual expected : Array Float) : TestM Unit :=
  report name (actual.size == expected.size && (actual.zip expected).all fun (a, e) => close a e)
    s!"expected {expected}, got {actual}"

private def checkRect (name : String) (r : ElkRectangle) (x y w h : Float) : TestM Unit :=
  report name (close r.x x && close r.y y && close r.width w && close r.height h)
    s!"expected ({x}, {y}, {w}, {h}), got {r}"

private def checkPadding (name : String) (p : ElkPadding) (top right bottom left : Float) : TestM Unit :=
  report name (close p.top top && close p.right right && close p.bottom bottom && close p.left left)
    s!"expected [t={top}, r={right}, b={bottom}, l={left}], got {p}"

/-- Checks `(left, right)` (horizontal) or `(top, bottom)` (vertical) of each margin. -/
private def checkMargins (name : String) (actual : Array (Float × Float)) (expected : Array (Float × Float)) :
    TestM Unit :=
  report name (actual.size == expected.size &&
      (actual.zip expected).all fun ((a1, a2), (e1, e2)) => close a1 e1 && close a2 e2)
    s!"expected {expected}, got {actual}"

/-! ### Fixtures -/

/-- A port of the test node: side, size, position, optional border offset, labels as
`(size, position)` and whether an edge connects the port to the node's child. -/
private structure PortSpec where
  side : PortSide
  width : Float := 10.0
  height : Float := 8.0
  x : Float := 0.0
  y : Float := 0.0
  borderOffset : Option Float := none
  labels : Array (KVector × KVector) := #[]
  toChild : Bool := false

/-- A label of the given size at (0, 0). -/
private def lbl (w h : Float) : KVector × KVector := (⟨w, h⟩, ⟨0.0, 0.0⟩)

/-- Root (with the shared spacings) ⊃ node `n` (`width × height`, options set by `nodeOpts`) with
the given ports; a child node is created if `withChild` or a port connects to it. -/
private def buildGraph (width height : Float) (nodeOpts : ElkGraph → NodeId → ElkGraph) (ports : Array PortSpec)
    (withChild : Bool := false) : ElkGraph × NodeId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root CoreOptions.SPACING_PORT_PORT 5.0
  let g := g.setNodeProp root CoreOptions.SPACING_PORTS_SURROUNDING
    ({ top := 2.0, right := 4.0, bottom := 6.0, left := 3.0 } : ElkMargin)
  let g := g.setNodeProp root CoreOptions.SPACING_LABEL_PORT_HORIZONTAL 2.0
  let g := g.setNodeProp root CoreOptions.SPACING_LABEL_PORT_VERTICAL 3.0
  let g := g.setNodeProp root CoreOptions.SPACING_LABEL_LABEL 1.0
  let g := g.setNodeProp root CoreOptions.SPACING_LABEL_NODE 5.0
  let (g, n) := g.createNode (some root)
  let g := g.modifyNode n fun nd => { nd with width := width, height := height }
  let mut g := nodeOpts g n
  let mut child : Option NodeId := none
  if withChild || ports.any (·.toChild) then
    let (g', c) := g.createNode (some n)
    g := g'
    child := some c
  for spec in ports do
    let (g', p) := g.createPort (some n)
    g := g'.setPortProp p CoreOptions.PORT_SIDE spec.side
    g := g.modifyPort p fun pt => { pt with width := spec.width, height := spec.height, x := spec.x, y := spec.y }
    if let some bo := spec.borderOffset then
      g := g.setPortProp p CoreOptions.PORT_BORDER_OFFSET bo
    for (size, pos) in spec.labels do
      let (g', l) := g.createLabel (some (.port p)) "l"
      g := g'.modifyLabel l fun lb => { lb with x := pos.x, y := pos.y, width := size.x, height := size.y }
    if spec.toChild then
      if let some c := child then
        g := (ElkGraphUtil.createSimpleEdge g (.port p) (.node c)).1
  return (g, n)

/-- Node options: port constraints, size constraints, port label placement, default alignment. -/
private def nodeOptions (constraints : PortConstraints) (sizeConstraints : EnumSet SizeConstraint)
    (labelPlacement : EnumSet PortLabelPlacement) (alignment : PortAlignment) (g : ElkGraph) (n : NodeId) :
    ElkGraph :=
  let g := g.setNodeProp n CoreOptions.PORT_CONSTRAINTS constraints
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_CONSTRAINTS sizeConstraints
  let g := g.setNodeProp n CoreOptions.PORT_LABELS_PLACEMENT labelPlacement
  g.setNodeProp n CoreOptions.PORT_ALIGNMENT_DEFAULT alignment

/-- Test stand-in for N2a's `PortContextCreator.createPortContext` (elk-rs rules): extracts the
port data, decides `labelsNextToPort`, creates the port label cell (unless port labels are
fixed) and inserts the context in `TreeMultimap` order. -/
private def addPortContext (a : ElkAdapters) (ctx : Ctx) (p : PortId) (vid : Int) : ElkM Ctx := do
  a.port.setVolatileId p vid
  let labels ← a.portLabels p
  let mut sizes : Array KVector := #[]
  let mut positions : Array KVector := #[]
  for l in labels do
    sizes := sizes.push (← a.label.getSize l)
    positions := positions.push (← a.label.getPosition l)
  let hasCompound ← a.hasCompoundConnections p
  let hasIncidentEdges := !(← a.portIncomingEdges p).isEmpty || !(← a.portOutgoingEdges p).isEmpty
  let nextToPortIfPossible := ctx.portLabelsPlacement.contains .nextToPortIfPossible
  let labelsNextToPort :=
    if ctx.portLabelsPlacement.contains .inside then
      if ctx.treatAsCompoundNode then nextToPortIfPossible && !hasCompound else true
    else if ctx.portLabelsPlacement.contains .outside then
      nextToPortIfPossible && !hasIncidentEdges
    else false
  let pc : PortContext PortId LabelId := PortContext.new p (← a.port.getSize p) (← a.portSide p) vid
    (← a.port.getPosition p) (← a.port.getPropertyD p CoreOptions.PORT_BORDER_OFFSET 0.0)
    (← a.port.hasProp p CoreOptions.PORT_BORDER_OFFSET) hasCompound
  let mut pc := { pc with labelsNextToPort, labels, labelSizes := sizes, labelPositions := positions }
  let mut ctx := ctx
  if !PortLabelPlacement.isFixed ctx.portLabelsPlacement then
    let (cells, lc) := ctx.cells.createLabel ctx.labelLabelSpacing
    let cells := (labels.zip sizes).foldl (fun cs (l, s) => cs.addLabel lc l s) cells
    ctx := { ctx with cells }
    pc := { pc with portLabelCell := some lc }
  return ctx.insertPortContext pc

/-- Test stand-in for N2a's `InsidePortLabelCellCreator.createInsidePortLabelCells`: one atomic
cell per side, registered in `insidePortLabelCells` and put into the node container (NORTH →
`BEGIN`, SOUTH → `END`) or its middle row (WEST → `BEGIN`, EAST → `END`). -/
private def createInsidePortLabelCells (ctx : Ctx) : Ctx := Id.run do
  let mut ctx := ctx
  for (side, container, area) in #[(PortSide.north, ctx.nodeContainer, ContainerArea.begin),
      (.south, ctx.nodeContainer, .«end»), (.west, ctx.nodeContainerMiddleRow, .begin),
      (.east, ctx.nodeContainerMiddleRow, .«end»)] do
    let (cells, c) := ctx.cells.createAtomic
    ctx := { ctx with cells := cells.setCell container area (some c) }
    ctx := ctx.setInsidePortLabelCell side (some c)
  return ctx

/-- The node context of `n` with its port contexts (volatile ids in port order) and inside port
label cells. -/
private def mkContext (g : ElkGraph) (n : NodeId) : IO Ctx := do
  let a ← ElkGraphAdapters.new
  let (ctx, _) ← ElkM.run (do
      let mut ctx ← NodeContext.new a n
      let mut vid : Int := 0
      for p in (← a.nodePorts n) do
        ctx ← addPortContext a ctx p vid
        vid := vid + 1
      return ctx) g
  return createInsidePortLabelCells ctx

private def inside (ctx : Ctx) (side : PortSide) : CellId := (ctx.insidePortLabelCell side).getD default

private def setInsideRect (ctx : Ctx) (side : PortSide) (r : ElkRectangle) : Ctx :=
  ctx.modifyCells (·.setCellRectangle (inside ctx side) r)

private def content (ctx : Ctx) (side : PortSide) : KVector := ctx.cells.minimumContentAreaSize (inside ctx side)

private def xs (ctx : Ctx) (side : PortSide) : Array Float := (ctx.portContextsOf side).map (·.portPosition.x)

private def ys (ctx : Ctx) (side : PortSide) : Array Float := (ctx.portContextsOf side).map (·.portPosition.y)

private def hMargins (ctx : Ctx) (side : PortSide) : Array (Float × Float) :=
  (ctx.portContextsOf side).map fun pc => (pc.portMargin.left, pc.portMargin.right)

private def vMargins (ctx : Ctx) (side : PortSide) : Array (Float × Float) :=
  (ctx.portContextsOf side).map fun pc => (pc.portMargin.top, pc.portMargin.bottom)

/-- The cell rectangle of the `i`-th port label cell of a side. -/
private def labelRect (ctx : Ctx) (side : PortSide) (i : Nat) : ElkRectangle :=
  match (ctx.portContextsOf side)[i]? with
  | some pc => ctx.cells.cellRectangleOpt pc.portLabelCell
  | none => {}

/-- `(horizontal, vertical)` alignment of the `i`-th port label cell of a side, as Java names. -/
private def labelAlign (ctx : Ctx) (side : PortSide) (i : Nat) : String :=
  match (ctx.portContextsOf side)[i]?.bind (·.portLabelCell) with
  | some c => s!"{ctx.cells.horizontalAlignment c}/{ctx.cells.verticalAlignment c}"
  | none => "none"

private def calcH (ctx : Ctx) : Ctx := HorizontalPortPlacementSizeCalculator.calculateHorizontalPortPlacementSize ctx

private def calcV (ctx : Ctx) : Ctx := VerticalPortPlacementSizeCalculator.calculateVerticalPortPlacementSize ctx

/-! ### Port placement size -/

/-- Three northern 10×8 ports, two eastern and one western 6×8 port, no labels. -/
private def freeGraph : ElkGraph × NodeId :=
  buildGraph 100.0 60.0 (nodeOptions .fixedSide (EnumSet.of #[.ports]) PortLabelPlacement.outsideSet .justified)
    #[{ side := .north }, { side := .north }, { side := .north },
      { side := .east, width := 6.0 }, { side := .east, width := 6.0 }, { side := .west, width := 6.0 }]

def placementSizeTests : Suite := suite "alg.common.nodespacing.internal.algorithm.PortPlacementSizeCalculators" do
  let (g, n) := freeGraph
  let ctx ← mkContext g n
  -- A padding on the empty south side, to see it cleared
  let ctx := ctx.modifyCells (·.setPadding (inside ctx .south) { top := 1.0, right := 9.0, left := 9.0 })
  let c := calcH ctx
  checkFloat "hand: FIXED_SIDE/JUSTIFIED north content width 10+5+10+5+10" (content c .north).x 40.0
  checkPadding "free north padding = surrounding port margins (l 3, r 4)"
    (c.cells.padding (inside c .north)) 0.0 4.0 0.0 3.0
  checkFloat "hand: node container BEGIN is the same cell: minimum width 40 + 3 + 4"
    (c.cells.minimumWidthOpt (c.cells.getCell c.nodeContainer .begin)) 47.0
  checkPadding "empty south side: left/right padding cleared, top kept"
    (c.cells.padding (inside c .south)) 1.0 0.0 0.0 0.0
  checkFloat "hand: DISTRIBUTED adds 2 * port-port spacing: 40 + 10"
    (content (calcH { ctx with portAlignmentNorth := some .distributed }) .north).x 50.0
  -- elk-rs keeps two copies of the cell and updates both: use two different arena cells
  let (cells, other) := ctx.cells.createAtomic
  let ctx2 := ({ ctx with cells } : Ctx).setInsidePortLabelCell .north (some other)
  let c2 := calcH ctx2
  check "hand: distinct inside/container cells both get width 40 (elk-rs updates both copies)"
    (close (c2.cells.minimumContentAreaSize other).x 40.0 &&
      close (c2.cells.minimumContentAreaSize (inside ctx .north)).x 40.0)
  -- Vertical
  let v := calcV ctx
  checkFloat "hand: east content height 8+5+8" (content v .east).y 21.0
  checkPadding "free east padding = surrounding port margins (t 2, b 6)"
    (v.cells.padding (inside v .east)) 2.0 0.0 6.0 0.0
  checkFloat "hand: middle row END is the same cell: minimum height 21 + 2 + 6"
    (v.cells.minimumHeightOpt (v.cells.getCell v.nodeContainerMiddleRow .«end»)) 29.0
  checkFloat "hand: single west port, DISTRIBUTED: 8 + 2 * 5"
    (content (calcV { ctx with portAlignmentWest := some .distributed }) .west).y 18.0

def freePlacementTests : Suite := suite "alg.common.nodespacing.internal.algorithm.PortPlacementCalculator (free)" do
  let (g, n) := freeGraph
  let ctx ← mkContext g n
  let place (align : PortAlignment) (width : Float) (opts : EnumSet SizeOptions) : Array Float :=
    let c := calcH { ctx with portAlignmentNorth := some align, sizeOptions := opts }
    let c := setInsideRect c .north { width := width, height := 20.0 }
    xs (PortPlacementCalculator.placeHorizontalPorts c) .north
  let none' : EnumSet SizeOptions := EnumSet.empty
  let overhang : EnumSet SizeOptions := EnumSet.of #[.portsOverhang]
  checkFloats "hand: JUSTIFIED: spacing 5 + (93 - 40) / 2, start 3" (place .justified 100.0 none') #[3.0, 44.5, 86.0]
  checkFloats "hand: CENTER: start 3 + (93 - 40) / 2" (place .center 100.0 none') #[29.5, 44.5, 59.5]
  checkFloats "hand: BEGIN: start 3, spacing 5" (place .begin 100.0 none') #[3.0, 18.0, 33.0]
  checkFloats "hand: END: start 3 + 53" (place .«end» 100.0 none') #[56.0, 71.0, 86.0]
  checkFloats "hand: DISTRIBUTED: spacing 5 + (93 - 50) / 4, start 3 + 15.75" (place .distributed 100.0 none')
    #[18.75, 44.5, 70.25]
  checkFloats "hand: cram (no PORTS_OVERHANG): spacing 5 + (23 - 40) / 2" (place .justified 30.0 none')
    #[3.0, 9.5, 16.0]
  checkFloats "hand: cram DISTRIBUTED: spacing 5 + (23 - 50) / 4, start 3 - 1.75" (place .distributed 30.0 none')
    #[1.25, 9.5, 17.75]
  checkFloats "hand: PORTS_OVERHANG: CENTER fallback, start 3 + (23 - 40) / 2" (place .justified 30.0 overhang)
    #[-5.5, 9.5, 24.5]
  checkFloats "hand: PORTS_OVERHANG + DISTRIBUTED: size 50 - 10, centered" (place .distributed 30.0 overhang)
    #[-5.5, 9.5, 24.5]
  let c := setInsideRect (calcH ctx) .north { width := 100.0, height := 20.0 }
  checkFloats "northern ports end at y = 0: y = -8" (ys (PortPlacementCalculator.placeHorizontalPorts c) .north)
    #[-8.0, -8.0, -8.0]
  -- Vertical: cells (0, 0, 20, 60), padding t 2 / b 6 → available 52
  let v := calcV { ctx with portAlignmentWest := some .distributed }
  let v := setInsideRect (setInsideRect v .east { width := 20.0, height := 60.0 }) .west { width := 20.0, height := 60.0 }
  let v := PortPlacementCalculator.placeVerticalPorts v
  checkFloats "hand: east JUSTIFIED: spacing 5 + (52 - 21), start 2" (ys v .east) #[2.0, 46.0]
  checkFloats "eastern ports start at the node width" (xs v .east) #[100.0, 100.0]
  checkFloats "hand: single west port DISTRIBUTED → CENTER: 2 + (52 - (18 - 10)) / 2" (ys v .west) #[24.0]
  checkFloats "western ports end at x = 0: x = -6" (xs v .west) #[-6.0]

/-! ### Fixed positions and ratios -/

def fixedPlacementTests : Suite := suite "alg.common.nodespacing.internal.algorithm.PortPlacementCalculator (fixed)" do
  -- FIXED_POS: node 80×50
  let (g, n) := buildGraph 80.0 50.0 (nodeOptions .fixedPos (EnumSet.of #[.ports]) PortLabelPlacement.outsideSet .justified)
    #[{ side := .north, x := 5.0 }, { side := .north, x := 30.0, borderOffset := some 2.0 },
      { side := .south, width := 12.0, height := 4.0, x := 60.0 },
      { side := .east, width := 6.0, y := 10.0, borderOffset := some (-1.0) },
      { side := .west, width := 6.0, y := 20.0 }]
  let ctx ← mkContext g n
  let ctx := ctx.modifyCells (·.setPadding (inside ctx .north) { left := 3.0, right := 4.0 })
  let c := calcV (calcH ctx)
  checkFloat "hand: FIXED_POS north: rightmost port border max(5 + 10, 30 + 10)" (content c .north).x 40.0
  checkPadding "FIXED_POS removes the left padding only" (c.cells.padding (inside c .north)) 0.0 4.0 0.0 0.0
  checkFloat "hand: FIXED_POS south: 60 + 12" (content c .south).x 72.0
  checkFloats "hand: FIXED_POS east/west: bottommost border 10 + 8, 20 + 8"
    #[(content c .east).y, (content c .west).y] #[18.0, 28.0]
  let c := PortPlacementCalculator.placeVerticalPorts (PortPlacementCalculator.placeHorizontalPorts c)
  checkFloats "FIXED_POS keeps x of northern ports" (xs c .north) #[5.0, 30.0]
  checkFloats "hand: north y = -8, with border offset 2: -8 - 2" (ys c .north) #[-8.0, -10.0]
  checkFloats "south y = 0" (ys c .south) #[0.0]
  checkFloats "hand: east x = 80 + border offset -1, west x = -6" (xs c .east ++ xs c .west) #[79.0, -6.0]
  checkFloats "FIXED_POS keeps y of eastern/western ports" (ys c .east ++ ys c .west) #[10.0, 20.0]
  -- FIXED_RATIO: node 200×100, two northern 10×8 and two eastern 6×8 ports
  let (g, n) := buildGraph 200.0 100.0 (nodeOptions .fixedRatio (EnumSet.of #[.ports]) PortLabelPlacement.outsideSet .justified)
    #[{ side := .north }, { side := .north }, { side := .east, width := 6.0 }, { side := .east, width := 6.0 }]
  let ctx ← mkContext g n
  let c := calcH ctx
  checkFloat "hand: FIXED_RATIO with the ratios elk-rs uses (all 0): only the right margin, 14 / (1 - 0)"
    (content c .north).x 14.0
  checkFloats "elk-rs ratio 0: x = 200 * 0" (xs (PortPlacementCalculator.placeHorizontalPorts c) .north) #[0.0, 0.0]
  let withRatios (side : PortSide) (r : Array Float) (cx : Ctx) : Ctx :=
    cx.modifyPortContextsOf side fun pcs =>
      (pcs.zip r).map fun (pc, ratio) => { pc with portRatioOrPosition := ratio }
  let cr := withRatios .east #[0.25, 0.75] (withRatios .north #[0.25, 0.5] ctx)
  let c := calcV (calcH cr)
  checkFloat "hand: north ratios 0.25/0.5: max(3 / 0.25, 15 / 0.25, 14 / 0.5)" (content c .north).x 60.0
  checkPadding "FIXED_RATIO removes the left padding" (c.cells.padding (inside c .north)) 0.0 0.0 0.0 0.0
  checkFloat "hand: east ratios 0.25/0.75: max(2 / 0.25, 13 / 0.5, 14 / 0.25)" (content c .east).y 56.0
  checkPadding "empty south side: left/right padding cleared" (c.cells.padding (inside c .south)) 0.0 0.0 0.0 0.0
  let c := PortPlacementCalculator.placeVerticalPorts (PortPlacementCalculator.placeHorizontalPorts c)
  checkFloats "hand: north x = 200 * ratio" (xs c .north) #[50.0, 100.0]
  checkFloats "hand: east y = 100 * ratio" (ys c .east) #[25.0, 75.0]
  checkFloats "east x = node width" (xs c .east) #[200.0, 200.0]

def minSizeTests : Suite := suite "alg.common.nodespacing.internal.algorithm.minSizeRequiredToRespectSpacing" do
  let f := HorizontalPortPlacementSizeCalculator.minSizeRequiredToRespectSpacing
  checkFloat "hand: 10 / (0.75 - 0.25)" (f 10.0 0.25 0.75) 20.0
  checkFloat "ratios closer than 0.01 count as equal" (f 10.0 0.3 0.305) 0.0
  checkFloat "equal ratios" (f 10.0 0.0 0.0) 0.0
  checkFloat "Java: DoubleMath.fuzzyEquals accepts |0 - 0.01| <= 0.01 → equal (elk-rs: 10 / 0.01)" (f 10.0 0.0 0.01) 0.0
  checkFloat "hand: ratios 0.02 apart differ → 10 / 0.02" (f 10.0 0.0 0.02) 500.0 1e-6

/-! ### Port margins (`SizeConstraint.PORT_LABELS`) -/

def portMarginTests : Suite := suite "alg.common.nodespacing.internal.algorithm.PortPlacementSizeCalculators (margins)" do
  let sc := EnumSet.of #[SizeConstraint.ports, .portLabels]
  -- Outside labels, not next to the port: three northern ports with labels 20, 8 and 20 wide
  let (g, n) := buildGraph 100.0 60.0 (nodeOptions .fixedSide sc PortLabelPlacement.outsideSet .justified)
    #[{ side := .north, labels := #[lbl 20.0 6.0] }, { side := .north, labels := #[lbl 8.0 6.0] },
      { side := .north, labels := #[lbl 20.0 6.0] }]
  let ctx ← mkContext g n
  let c := calcH ctx
  checkMargins "hand: right margin 2 + label width; last port none" (hMargins c .north)
    #[(0.0, 22.0), (0.0, 10.0), (0.0, 0.0)]
  checkFloat "hand: width (10 + 22) + 5 + (10 + 10) + 5 + 10" (content c .north).x 72.0
  let cu := calcH { ctx with sizeOptions := EnumSet.of #[.uniformPortSpacing] }
  checkMargins "hand: UNIFORM_PORT_SPACING: max right margin 22, outer margins cleared again" (hMargins cu .north)
    #[(0.0, 22.0), (0.0, 22.0), (0.0, 0.0)]
  checkFloat "hand: uniform width 32 + 5 + 32 + 5 + 10" (content cu .north).x 84.0
  -- Two ports: space-efficient by count, the first label goes left of its port
  let (g, n) := buildGraph 100.0 60.0 (nodeOptions .fixedSide sc PortLabelPlacement.outsideSet .justified)
    #[{ side := .north, labels := #[lbl 20.0 6.0] }, { side := .north, labels := #[lbl 20.0 6.0] }]
  let c2 := calcH (← mkContext g n)
  checkMargins "two ports: first port loses its right margin too" (hMargins c2 .north) #[(0.0, 0.0), (0.0, 0.0)]
  let ctxA ← mkContext g n
  let c2a := calcH { ctxA with portLabelsPlacement := EnumSet.of #[.outside, .alwaysSameSide] }
  checkMargins "ALWAYS_SAME_SIDE keeps the first port's right margin" (hMargins c2a .north) #[(0.0, 22.0), (0.0, 0.0)]
  -- Inside labels next to the port (non-compound node): overhang (20 - 10) / 2 on both sides
  let (g, n) := buildGraph 100.0 60.0 (nodeOptions .fixedSide sc PortLabelPlacement.insideSet .justified)
    #[{ side := .north, labels := #[lbl 20.0 6.0] }, { side := .north, labels := #[lbl 20.0 6.0] }]
  let ci := calcH (← mkContext g n)
  checkMargins "hand: next-to-port labels overhang 5 on both sides" (hMargins ci .north) #[(5.0, 5.0), (5.0, 5.0)]
  checkFloat "hand: width 20 + 5 + 20" (content ci .north).x 45.0
  -- Compound node, NEXT_TO_PORT_IF_POSSIBLE: the port with a compound connection is not next to its label
  let (g, n) := buildGraph 100.0 60.0
    (nodeOptions .fixedSide sc (EnumSet.of #[.inside, .nextToPortIfPossible]) .justified)
    #[{ side := .north, labels := #[lbl 20.0 6.0], toChild := true }, { side := .north, labels := #[lbl 20.0 6.0] }]
  let cc := calcH (← mkContext g n)
  check "compound connection → label not next to the port"
    ((cc.portContextsOf .north).map (·.labelsNextToPort) == #[false, true])
  checkMargins "hand: compound connection: right margin 2 + 20; other port overhang 5" (hMargins cc .north)
    #[(0.0, 22.0), (5.0, 5.0)]
  checkFloat "hand: width 32 + 5 + 20" (content cc .north).x 57.0
  -- Vertical, inside next to the port: labels 12 and 6 high, gap 1 → label cell height 19
  let (g, n) := buildGraph 100.0 60.0 (nodeOptions .fixedSide sc PortLabelPlacement.insideSet .justified)
    #[{ side := .east, width := 6.0, labels := #[lbl 10.0 12.0, lbl 10.0 6.0] },
      { side := .east, width := 6.0, labels := #[lbl 10.0 12.0, lbl 10.0 6.0] }]
  let ctxV ← mkContext g n
  let cv := calcV ctxV
  checkMargins "hand: grouped labels centered: (19 - 8) / 2" (vMargins cv .east) #[(5.5, 5.5), (5.5, 5.5)]
  checkFloat "hand: height 19 + 5 + 19" (content cv .east).y 43.0
  let cvs := calcV { ctxV with portLabelsTreatAsGroup := false }
  checkMargins "hand: first label centered: top (12 - 8) / 2, bottom 19 - 2 - 8" (vMargins cvs .east)
    #[(2.0, 9.0), (2.0, 9.0)]
  -- Vertical, outside not next to the port: bottom margin 3 + 19, first/last cleared, space-efficient first
  let (g, n) := buildGraph 100.0 60.0 (nodeOptions .fixedSide sc PortLabelPlacement.outsideSet .justified)
    #[{ side := .east, width := 6.0, labels := #[lbl 10.0 12.0, lbl 10.0 6.0] },
      { side := .east, width := 6.0, labels := #[lbl 10.0 12.0, lbl 10.0 6.0] },
      { side := .east, width := 6.0, labels := #[lbl 10.0 12.0, lbl 10.0 6.0] }]
  let co := calcV (← mkContext g n)
  checkMargins "hand: outside: bottom 3 + 19, last port none" (vMargins co .east)
    #[(0.0, 22.0), (0.0, 22.0), (0.0, 0.0)]
  -- Fixed labels: no label cell, margins from the label bounds
  let (g, n) := buildGraph 100.0 60.0 (nodeOptions .fixedSide sc PortLabelPlacement.fixed .justified)
    #[{ side := .north, labels := #[(⟨20.0, 5.0⟩, ⟨-4.0, 9.0⟩)] },
      { side := .east, width := 6.0, labels := #[(⟨5.0, 4.0⟩, ⟨7.0, -3.0⟩)] }]
  let cf := calcV (calcH (← mkContext g n))
  checkMargins "hand: fixed label bounds x -4..16 on a 10 wide port: left 4, right 6" (hMargins cf .north) #[(4.0, 6.0)]
  checkMargins "hand: fixed label bounds y -3..1 on an 8 high port: top 3" (vMargins cf .east) #[(3.0, 0.0)]
  checkFloat "hand: fixed labels: width 4 + 10 + 6" (content cf .north).x 20.0

/-! ### Port label placement -/

def outsideLabelTests : Suite := suite "alg.common.nodespacing.internal.algorithm.PortLabelPlacementCalculator (outside)" do
  let sc := EnumSet.of #[SizeConstraint.ports, .portLabels]
  let (g, n) := buildGraph 100.0 60.0 (nodeOptions .fixedSide sc PortLabelPlacement.outsideSet .justified)
    #[{ side := .north, labels := #[lbl 20.0 6.0] }, { side := .north, labels := #[lbl 20.0 6.0] },
      { side := .south, labels := #[lbl 20.0 6.0] },
      { side := .east, width := 6.0, labels := #[lbl 10.0 12.0, lbl 10.0 6.0] },
      { side := .east, width := 6.0, labels := #[lbl 10.0 4.0] },
      { side := .west, width := 6.0, labels := #[lbl 20.0 6.0] },
      { side := .west, width := 6.0 }]
  let ctx ← mkContext g n
  let c := PortLabelPlacementCalculator.placeVerticalPortLabels (PortLabelPlacementCalculator.placeHorizontalPortLabels ctx)
  checkRect "hand: first of two northern ports placed differently: (-20 - 2, -6 - 3)" (labelRect c .north 0)
    (-22.0) (-9.0) 20.0 6.0
  checkEq "first northern label RIGHT/BOTTOM" (labelAlign c .north 0) "RIGHT/BOTTOM"
  checkRect "hand: second northern port: (10 + 2, -9)" (labelRect c .north 1) 12.0 (-9.0) 20.0 6.0
  checkEq "second northern label LEFT/BOTTOM" (labelAlign c .north 1) "LEFT/BOTTOM"
  checkRect "hand: single southern port: (10 + 2, 8 + 3)" (labelRect c .south 0) 12.0 11.0 20.0 6.0
  checkEq "southern label LEFT/TOP" (labelAlign c .south 0) "LEFT/TOP"
  checkRect "hand: first eastern port placed differently: (6 + 2, -19 - 3)" (labelRect c .east 0) 8.0 (-22.0) 10.0 19.0
  checkRect "hand: second eastern port below: (8, 8 + 3)" (labelRect c .east 1) 8.0 11.0 10.0 4.0
  checkEq "eastern labels LEFT/BOTTOM then LEFT/TOP" #[labelAlign c .east 0, labelAlign c .east 1]
    #["LEFT/BOTTOM", "LEFT/TOP"]
  -- West: descending volatile ids, the label-less port comes first; skipping it keeps the "first" flag
  checkRect "hand: western label of the second port placed differently: (-20 - 2, -6 - 3)" (labelRect c .west 1)
    (-22.0) (-9.0) 20.0 6.0
  checkEq "western label RIGHT/BOTTOM" (labelAlign c .west 1) "RIGHT/BOTTOM"
  let ca := PortLabelPlacementCalculator.placeHorizontalPortLabels
    { ctx with portLabelsPlacement := EnumSet.of #[.outside, .alwaysOtherSameSide] }
  checkFloats "hand: ALWAYS_OTHER_SAME_SIDE: every northern label left of its port" #[(labelRect ca .north 0).x,
    (labelRect ca .north 1).x, (labelRect ca .south 0).x] #[-22.0, -22.0, -22.0]
  -- Next to the port (outside + NEXT_TO_PORT_IF_POSSIBLE, ports without edges)
  let (g, n) := buildGraph 100.0 60.0
    (nodeOptions .fixedSide sc (EnumSet.of #[.outside, .nextToPortIfPossible]) .justified)
    #[{ side := .north, labels := #[lbl 20.0 6.0] }, { side := .north, labels := #[lbl 20.0 6.0] },
      { side := .east, width := 6.0, labels := #[lbl 10.0 12.0, lbl 10.0 6.0] }]
  let ctxN ← mkContext g n
  let cn := PortLabelPlacementCalculator.placeVerticalPortLabels (PortLabelPlacementCalculator.placeHorizontalPortLabels ctxN)
  checkRect "hand: next-to-port northern label centered: ((10 - 20) / 2, -9)" (labelRect cn .north 0) (-5.0) (-9.0) 20.0 6.0
  checkEq "next-to-port northern label CENTER/BOTTOM" (labelAlign cn .north 0) "CENTER/BOTTOM"
  checkRect "hand: next-to-port grouped eastern labels: (8, (8 - 19) / 2)" (labelRect cn .east 0) 8.0 (-5.5) 10.0 19.0
  let cng := PortLabelPlacementCalculator.placeVerticalPortLabels { ctxN with portLabelsTreatAsGroup := false }
  checkRect "hand: next-to-port, first label centered: (8, (8 - 12) / 2)" (labelRect cng .east 0) 8.0 (-2.0) 10.0 19.0
  checkEq "next-to-port eastern label LEFT/CENTER" (labelAlign cng .east 0) "LEFT/CENTER"

def insideLabelTests : Suite := suite "alg.common.nodespacing.internal.algorithm.PortLabelPlacementCalculator (inside)" do
  let sc := EnumSet.of #[SizeConstraint.ports, .portLabels]
  let ports : Array PortSpec := #[{ side := .north, labels := #[lbl 20.0 6.0] },
      { side := .north, borderOffset := some 2.0, labels := #[lbl 10.0 12.0, lbl 10.0 6.0] },
      { side := .south, labels := #[lbl 20.0 6.0] },
      { side := .east, width := 6.0, labels := #[lbl 10.0 12.0, lbl 10.0 6.0] },
      { side := .west, width := 6.0, labels := #[lbl 20.0 6.0] }]
  let (g, n) := buildGraph 100.0 60.0 (nodeOptions .fixedSide sc PortLabelPlacement.insideSet .justified) ports
  let ctx ← mkContext g n
  -- Node container padding t 1, r 2, b 3, l 4 → label border offsets N 1 + 3, S 3 + 3, E 2 + 2, W 4 + 2
  let ctx := ctx.modifyCells (·.setPadding ctx.nodeContainer { top := 1.0, right := 2.0, bottom := 3.0, left := 4.0 })
  let c := PortLabelPlacementCalculator.placeVerticalPortLabels (PortLabelPlacementCalculator.placeHorizontalPortLabels ctx)
  checkRect "hand: northern label next to the port: ((10 - 20) / 2, 8 + 0 + 4)" (labelRect c .north 0) (-5.0) 12.0 20.0 6.0
  checkRect "hand: with border offset 2: (0, 8 + 2 + 4)" (labelRect c .north 1) 0.0 14.0 10.0 19.0
  checkEq "northern inside label CENTER/TOP" (labelAlign c .north 0) "CENTER/TOP"
  checkFloat "hand: north inside cell content height max(6, 19)" (content c .north).y 19.0
  checkFloat "node container BEGIN (same cell) sees the height"
    (c.cells.minimumContentAreaSize ((c.cells.getCell c.nodeContainer .begin).getD default)).y 19.0
  checkRect "hand: southern label: (-5, -0 - 6 - 6)" (labelRect c .south 0) (-5.0) (-12.0) 20.0 6.0
  checkEq "southern inside label CENTER/BOTTOM" (labelAlign c .south 0) "CENTER/BOTTOM"
  checkFloat "hand: south inside cell content height 6" (content c .south).y 6.0
  checkRect "hand: eastern grouped labels: (-0 - 4 - 10, (8 - 19) / 2)" (labelRect c .east 0) (-14.0) (-5.5) 10.0 19.0
  checkEq "eastern inside label RIGHT/CENTER" (labelAlign c .east 0) "RIGHT/CENTER"
  checkRect "hand: western label: (6 + 0 + 6, (8 - 6) / 2)" (labelRect c .west 0) 12.0 1.0 20.0 6.0
  checkEq "western inside label LEFT/CENTER" (labelAlign c .west 0) "LEFT/CENTER"
  let cs := PortLabelPlacementCalculator.placeVerticalPortLabels { ctx with portLabelsTreatAsGroup := false }
  checkRect "hand: first eastern label centered: (-14, (8 - 12) / 2)" (labelRect cs .east 0) (-14.0) (-2.0) 10.0 19.0
  -- Compound node with NEXT_TO_PORT_IF_POSSIBLE: ports with compound connections place labels beside them
  let ports := (ports.modify 0 fun p => { p with toChild := true }).modify 3 fun p => { p with toChild := true }
  let (g, n) := buildGraph 100.0 60.0
    (nodeOptions .fixedSide sc (EnumSet.of #[.inside, .nextToPortIfPossible]) .justified) ports
  let ctxC ← mkContext g n
  let ctxC := ctxC.modifyCells (·.setPadding ctxC.nodeContainer { top := 1.0, right := 2.0, bottom := 3.0, left := 4.0 })
  let cc := PortLabelPlacementCalculator.placeVerticalPortLabels (PortLabelPlacementCalculator.placeHorizontalPortLabels ctxC)
  check "compound connections: labels of ports 0 and 3 not next to the port"
    ((cc.portContextsOf .north)[0]?.map (·.labelsNextToPort) == some false &&
      (cc.portContextsOf .east)[0]?.map (·.labelsNextToPort) == some false)
  checkRect "hand: compound northern label beside the port: (10 + 2, 12)" (labelRect cc .north 0) 12.0 12.0 20.0 6.0
  checkRect "hand: second northern port (no compound edge) still next to it: (0, 14)" (labelRect cc .north 1)
    0.0 14.0 10.0 19.0
  checkRect "hand: compound eastern label below the port: (-14, 8 + 3)" (labelRect cc .east 0) (-14.0) 11.0 10.0 19.0

def constrainedLabelTests : Suite :=
    suite "alg.common.nodespacing.internal.algorithm.PortLabelPlacementCalculator (constrained)" do
  -- Inside, PORT_LABELS not in the size constraints: northern ports at (10, -10) and (20, -10)
  let (g, n) := buildGraph 100.0 60.0 (nodeOptions .fixedSide (EnumSet.of #[.ports]) PortLabelPlacement.insideSet .justified)
    #[{ side := .north, width := 10.0, height := 10.0, x := 10.0, y := -10.0, labels := #[lbl 30.0 10.0] },
      { side := .north, width := 10.0, height := 10.0, x := 20.0, y := -10.0, labels := #[lbl 30.0 10.0] },
      { side := .south, width := 10.0, height := 10.0, x := 10.0, y := 60.0, labels := #[lbl 30.0 10.0] },
      { side := .east, width := 6.0, x := 100.0, y := 20.0, labels := #[lbl 10.0 4.0] }]
  let ctx ← mkContext g n
  let ctx := setInsideRect (setInsideRect ctx .north { width := 100.0, height := 20.0 }) .south
    { y := 40.0, width := 100.0, height := 20.0 }
  let c := PortLabelPlacementCalculator.placeVerticalPortLabels (PortLabelPlacementCalculator.placeHorizontalPortLabels ctx)
  -- borders 0 + max(0, 3, 5) = 5 and 100 - max(0, 4, 5) = 95; start 0 + 3; DOWN removal with gap 3
  checkRect "hand: first label clamped to x 5, y 0 + 3, relative to (10, -10)" (labelRect c .north 0)
    (-5.0) 13.0 30.0 10.0
  checkRect "hand: second label pushed down to 13 + 3, relative to (20, -10)" (labelRect c .north 1)
    (-10.0) 26.0 30.0 10.0
  checkEq "constrained inside label RIGHT/TOP" (labelAlign c .north 0) "RIGHT/TOP"
  checkFloat "hand: strip height max(10, 13 + 10) becomes the north content height" (content c .north).y 23.0
  checkRect "hand: southern label: x 5, UP removal y 57 - 10 - 0, relative to (10, 60)" (labelRect c .south 0)
    (-5.0) (-13.0) 30.0 10.0
  checkFloat "hand: south strip height 10" (content c .south).y 10.0
  checkRect "east reverts to the simple placement: (-0 - (0 + 2) - 10, (8 - 4) / 2)" (labelRect c .east 0)
    (-12.0) 2.0 10.0 4.0
  let cf := PortLabelPlacementCalculator.placeHorizontalPortLabels
    { ctx with portConstraints := .fixedPos, sizeConstraints := EnumSet.of #[.ports, .portLabels] }
  checkRect "FIXED_POS with PORT_LABELS is constrained as well" (labelRect cf .north 1) (-10.0) 26.0 30.0 10.0
  -- Outside, constrained: three northern ports at x 0, 20, 40 (y -10), labels 30×10
  let (g, n) := buildGraph 100.0 60.0 (nodeOptions .fixedSide (EnumSet.of #[.ports]) PortLabelPlacement.outsideSet .justified)
    #[{ side := .north, width := 10.0, height := 10.0, x := 0.0, y := -10.0, labels := #[lbl 30.0 10.0] },
      { side := .north, width := 10.0, height := 10.0, x := 20.0, y := -10.0, labels := #[lbl 30.0 10.0] },
      { side := .north, width := 10.0, height := 10.0, x := 40.0, y := -10.0, labels := #[lbl 30.0 10.0] },
      { side := .south, width := 10.0, height := 10.0, x := 0.0, y := 60.0, labels := #[lbl 30.0 10.0] },
      { side := .south, width := 10.0, height := 10.0, x := 30.0, y := 60.0, labels := #[lbl 30.0 10.0] }]
  let ctxO ← mkContext g n
  let co := PortLabelPlacementCalculator.placeHorizontalPortLabels ctxO
  -- right of the ports at 12, 32, 52; start -10 - 3; UP removal with vertical gap 2 (= horizontal spacing)
  checkFloats "hand: labels right of their ports: x + 10 + 2, relative" ((#[0, 1, 2] : Array Nat).map fun i =>
    (labelRect co .north i).x) #[12.0, 12.0, 12.0]
  checkFloats "hand: UP removal: -13 - 10 - (0, 12, 0), relative to y -10" ((#[0, 1, 2] : Array Nat).map fun i =>
    (labelRect co .north i).y) #[-13.0, -25.0, -13.0]
  checkEq "constrained outside label RIGHT/BOTTOM" (labelAlign co .north 0) "RIGHT/BOTTOM"
  let cse := PortLabelPlacementCalculator.placeHorizontalPortLabels
    { ctxO with portLabelsPlacement := EnumSet.of #[.outside, .spaceEfficient] }
  checkFloats "hand: SPACE_EFFICIENT: first label left of its port: 0 - 30 - 2" ((#[0, 1, 2] : Array Nat).map fun i =>
    (labelRect cse .north i).x) #[-32.0, 12.0, 12.0]
  checkFloats "hand: SPACE_EFFICIENT: only the last two labels overlap" ((#[0, 1, 2] : Array Nat).map fun i =>
    (labelRect cse .north i).y) #[-13.0, -13.0, -25.0]
  -- Two southern ports (descending volatile ids: x 30 first) revert to the simple placement
  checkRect "hand: two ports → simple: first (x 30) placed differently (-30 - 2, 10 + 3)" (labelRect co .south 0)
    (-32.0) 13.0 30.0 10.0
  checkRect "hand: second southern label (10 + 2, 13)" (labelRect co .south 1) 12.0 13.0 30.0 10.0

def suites : Array Tests.Suite :=
  #[placementSizeTests, freePlacementTests, fixedPlacementTests, minSizeTests, portMarginTests,
    outsideLabelTests, insideLabelTests, constrainedLabelTests]

end Tests.AlgCommon.NodeSpacing.AlgorithmPorts
