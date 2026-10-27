import Tests.Framework
import Elk.Alg.Common
/-! Tests of the nodespacing calculators (task N3a): `NodeLabelAndSizeCalculator` (the Java
cell-system pipeline `process`/`processWithOptions`, the elk-rs simplified `processNode`, the inside
node label padding / container minimum size) and `NodeMarginCalculator`.

Expected numbers prefixed "rust:" are the assertions of elk-rs `tests/all/nodespacing_test.rs`
(same graphs); all others are derived by hand from the elk-rs formulas ("hand:" prefix, the
derivation is sketched in the check name or the comment above it). -/
namespace Tests.AlgCommon.NodeSpacing.Calculators

open Tests Elk Elk.Graph Elk.Core.Math Elk.Core.Util Elk.Core.Options Elk.Core.Util.Adapters
open Elk.Alg.Common.NodeSpacing Elk.Alg.Common.NodeSpacing.CellSystem

private def close (a b : Float) : Bool := (a - b).abs <= 1e-9

private def checkVec (name : String) (v : KVector) (x y : Float) : TestM Unit :=
  report name (close v.x x && close v.y y) s!"expected ({x}, {y}), got {repr v}"

private def checkPadding (name : String) (p : ElkPadding) (top right bottom left : Float) : TestM Unit :=
  report name (close p.top top && close p.right right && close p.bottom bottom && close p.left left)
    s!"expected [t={top}, r={right}, b={bottom}, l={left}], got {repr p}"

private def checkFloats (name : String) (actual expected : Array Float) : TestM Unit :=
  report name (actual.size == expected.size && (actual.zip expected).all fun (a, b) => close a b)
    s!"expected {expected}, got {actual}"

/-- Runs `f` with a fresh adapter family on graph `g`. -/
private def runWith {α : Type} (g : ElkGraph) (f : ElkAdapters → ElkM α) : IO (α × ElkGraph) := do
  let a ← ElkGraphAdapters.new
  ElkM.run (f a) g

/-! ### Graph construction helpers -/

private def nodeSize (g : ElkGraph) (n : NodeId) : KVector := ⟨(g.node n).width, (g.node n).height⟩
private def portPos (g : ElkGraph) (p : PortId) : KVector := ⟨(g.port p).x, (g.port p).y⟩
private def labelPos (g : ElkGraph) (l : LabelId) : KVector := ⟨(g.label l).x, (g.label l).y⟩
private def nodeMargin (g : ElkGraph) (n : NodeId) : ElkMargin := (g.node n).props.getD CoreOptions.MARGINS {}

private def setGeometry (g : ElkGraph) (n : NodeId) (x y w h : Float) : ElkGraph :=
  g.modifyNode n fun nd => { nd with x, y, width := w, height := h }

/-- A node label of the given size at (0, 0), with its own placement if given. -/
private def addNodeLabel (g : ElkGraph) (n : NodeId) (w h : Float)
    (placement : Option (EnumSet NodeLabelPlacement) := none) : ElkGraph × LabelId :=
  let (g, l) := g.createLabel (some (.node n)) "l"
  let g := g.modifyLabel l fun lb => { lb with width := w, height := h }
  match placement with
  | some pl => (g.setLabelProp l CoreOptions.NODE_LABELS_PLACEMENT pl, l)
  | none => (g, l)

/-- A port on the given side (no side if `none`). -/
private def addPort (g : ElkGraph) (n : NodeId) (side : Option PortSide) (x y w h : Float) : ElkGraph × PortId :=
  let (g, p) := g.createPort (some n)
  let g := g.modifyPort p fun pt => { pt with x, y, width := w, height := h }
  match side with
  | some s => (g.setPortProp p CoreOptions.PORT_SIDE s, p)
  | none => (g, p)

/-- A label of the given geometry attached to an element. -/
private def addLabelTo (g : ElkGraph) (parent : ElementId) (x y w h : Float) : ElkGraph × LabelId :=
  let (g, l) := g.createLabel (some parent) "l"
  (g.modifyLabel l fun lb => { lb with x, y, width := w, height := h }, l)

private def insideTC : EnumSet NodeLabelPlacement := EnumSet.of #[.inside, .vTop, .hCenter]
private def outsideBC : EnumSet NodeLabelPlacement := EnumSet.of #[.outside, .vBottom, .hCenter]

/-! ### Helpers of `NodeLabelAndSizeCalculator` -/

open NodeLabelAndSizeCalculator in
def helperTests : Suite := suite "alg.common.nodespacing.NodeLabelAndSizeCalculator helpers" do
  checkFloat "hand: sumWithGaps [3, 0, 4] gap 2 = 3 + 4 + one gap" (sumWithGapsWithGap #[3.0, 0.0, 4.0] 2.0) 9.0
  checkFloat "hand: sumWithGaps [3, 5, 4] gap 2 = 12 + two gaps" (sumWithGapsWithGap #[3.0, 5.0, 4.0] 2.0) 16.0
  checkFloat "hand: sumWithGaps of zeros is 0" (sumWithGapsWithGap #[0.0, 0.0, 0.0] 2.0) 0.0
  let ax := layoutAxisThree 0.0 30.0 5.0 5.0 #[10.0, 0.0, 10.0] 0.0
  checkFloats "hand: layoutAxisThree(0, 30, pad 5/5, [10, 0, 10]) starts [5, 5+10, 30-5-10]" ax.starts #[5.0, 15.0, 15.0]
  checkFloats "hand: layoutAxisThree spans [10, max(0, free 0), 10]" ax.spans #[10.0, 0.0, 10.0]
  -- free = 10 - 2 - 2 - (4 + 1) - (4 + 1) = -4; center = max(3, -4) = 3 centered on the free span
  let ax2 := layoutAxisThree 0.0 10.0 2.0 2.0 #[4.0, 3.0, 4.0] 1.0
  checkFloats "hand: overfull axis: center start 2 + 5 - (3 + 4) / 2, end start 10 - 2 - 4" ax2.starts #[2.0, 3.5, 4.0]
  checkFloat "hand: overfull axis: free area start 2 + (0 + 4) / 2" ax2.centerAreaStart 4.0
  checkFloat "hand: overfull axis: free area span clamped at 0" ax2.centerAreaSpan 0.0
  checkEqR "outside V_TOP H_LEFT H_PRIORITY goes to the WEST strip"
    (nodeLabelLocationInfoForPlacement (EnumSet.of #[.outside, .vTop, .hLeft, .hPriority]))
    (some { inside := false, row := .begin, col := .begin, outsideSide := some .west })
  checkEqR "outside V_TOP H_LEFT without H_PRIORITY goes to the NORTH strip"
    (nodeLabelLocationInfoForPlacement (EnumSet.of #[.outside, .vTop, .hLeft]))
    (some { inside := false, row := .begin, col := .begin, outsideSide := some .north })
  checkEqR "outside V_CENTER H_CENTER has no location"
    (nodeLabelLocationInfoForPlacement (EnumSet.of #[.outside, .vCenter, .hCenter])) none
  checkEqR "INSIDE and OUTSIDE together have no location"
    (nodeLabelLocationInfoForPlacement (EnumSet.of #[.inside, .outside, .vTop, .hLeft])) none
  checkEqR "inside V_BOTTOM H_RIGHT is the (END, END) cell"
    (nodeLabelLocationInfoForPlacement (EnumSet.of #[.inside, .vBottom, .hRight]))
    (some { inside := true, row := .«end», col := .«end», outsideSide := none })
  check "insideCellForPlacement needs a horizontal flag"
    (insideCellForPlacement (EnumSet.of #[.inside, .vTop])).isNone
  check "insideCellForPlacement: V_TOP wins over V_BOTTOM, H_LEFT"
    (insideCellForPlacement (EnumSet.of #[.inside, .vTop, .vBottom, .hLeft]) == some (.begin, .begin))
  check "fixed size constraints: {} and {PORT_LABELS}"
    (hasEffectivelyFixedSizeConstraints EnumSet.empty
      && hasEffectivelyFixedSizeConstraints (EnumSet.of #[SizeConstraint.portLabels])
      && !hasEffectivelyFixedSizeConstraints (EnumSet.of #[SizeConstraint.ports]))
  let s := ((({} : CellMinSize).addLabel ⟨6.0, 5.0⟩ 1.0 false).addLabel ⟨4.0, 3.0⟩ 1.0 false)
  checkVec "hand: CellMinSize side by side (6 + 1 + 4, max(5, 3))" ⟨s.width, s.height⟩ 11.0 5.0

/-! ### `process` (Java cell-system pipeline) -/

/-- Root ⊃ node `n` (10×10, `NODE_LABELS`) with an inside top-center label 30×10 and an outside
bottom-center label 20×5 (all spacings default: label-label 0, label-node 5, node labels
padding 5). -/
private def nodeLabelsGraph (options : EnumSet SizeOptions := EnumSet.of #[.defaultMinimumSize]) :
    ElkGraph × NodeId × LabelId × LabelId :=
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n) := g.createNode (some root)
  let g := setGeometry g n 0.0 0.0 10.0 10.0
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.nodeLabels])
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_OPTIONS options
  let (g, inside) := addNodeLabel g n 30.0 10.0 (some insideTC)
  let (g, outside) := addNodeLabel g n 20.0 5.0 (some outsideBC)
  (g, n, inside, outside)

/-- Root ⊃ node `n` (10×10, `{PORTS, PORT_LABELS}`, `FIXED_SIDE`, outside port labels) with EAST
ports p0 (4×4, label 8×3), p1 (4×4) and a NORTH port p2 (6×2). -/
private def portsGraph : ElkGraph × NodeId × Array PortId × LabelId :=
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n) := g.createNode (some root)
  let g := setGeometry g n 0.0 0.0 10.0 10.0
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.ports, .portLabels])
  let g := g.setNodeProp n CoreOptions.PORT_CONSTRAINTS PortConstraints.fixedSide
  let (g, p0) := addPort g n (some .east) 0.0 0.0 4.0 4.0
  let (g, p1) := addPort g n (some .east) 0.0 0.0 4.0 4.0
  let (g, p2) := addPort g n (some .north) 0.0 0.0 6.0 2.0
  let (g, l0) := addLabelTo g (.port p0) 0.0 0.0 8.0 3.0
  (g, n, #[p0, p1, p2], l0)

/-- Root ⊃ node `n` (10×10, `{PORTS, MINIMUM_SIZE}`) with the given port constraints and ports. -/
private def fixedPortsGraph (constraints : PortConstraints) (minimum : KVector)
    (ports : Array (PortSide × Float × Float)) : ElkGraph × NodeId × Array PortId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n) := g.createNode (some root)
  let g := setGeometry g n 0.0 0.0 10.0 10.0
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.ports, .minimumSize])
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_MINIMUM minimum
  let mut g := g.setNodeProp n CoreOptions.PORT_CONSTRAINTS constraints
  let mut ids : Array PortId := #[]
  for (side, x, y) in ports do
    let (g', p) := addPort g n (some side) x y 4.0 4.0
    g := g'
    ids := ids.push p
  return (g, n, ids)

/-- Root ⊃ node `n` (10×10, `{PORTS, PORT_LABELS}`, INSIDE port labels) with a WEST port 4×4
carrying a label 10×2. -/
private def insidePortLabelGraph : ElkGraph × NodeId × PortId × LabelId :=
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n) := g.createNode (some root)
  let g := setGeometry g n 0.0 0.0 10.0 10.0
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.ports, .portLabels])
  let g := g.setNodeProp n CoreOptions.PORT_LABELS_PLACEMENT (EnumSet.of #[PortLabelPlacement.inside])
  let (g, p) := addPort g n (some .west) 0.0 0.0 4.0 4.0
  let (g, l) := addLabelTo g (.port p) 0.0 0.0 10.0 2.0
  (g, n, p, l)

def processTests : Suite := suite "alg.common.nodespacing.NodeLabelAndSizeCalculator.process" do
  -- Node labels. Width: grid row TOP (0, 30, 0) + padding 5 + 5 = 40 (south strip needs only 20).
  -- Height: rows (10, 0, 10) (symmetric) + padding 10 = 30. Inside cell (5, 5, 30, 10). South
  -- strip (0, 30, 40, 10): label cell (0, 35, 40, 5), label centered: x = (40 - 20) / 2.
  let (g, n, inside, outside) := nodeLabelsGraph (EnumSet.of #[.defaultMinimumSize, .computePadding])
  let (size, g1) ← runWith g fun a => NodeLabelAndSizeCalculator.process a n .right
  checkVec "hand: node labels: size (30 + 2·5, (10 + 10) + 2·5)" size 40.0 30.0
  checkVec "hand: node labels: size applied" (nodeSize g1 n) 40.0 30.0
  checkVec "hand: inside top-center label at the padded top-left of its 30-wide cell" (labelPos g1 inside) 5.0 5.0
  checkVec "hand: outside bottom-center label below the node + label-node spacing, centered"
    (labelPos g1 outside) 10.0 35.0
  check "oracle: COMPUTE_PADDING is discarded by process (no PADDING set)"
    (!(g1.node n).props.has CoreOptions.PADDING)
  -- applyStuff = false: same size, nothing applied
  let (size0, g0) ← runWith g fun a => NodeLabelAndSizeCalculator.processWithOptions a n .right false false
  checkVec "hand: applyStuff = false returns the same size" size0 40.0 30.0
  checkVec "applyStuff = false leaves the node size" (nodeSize g0 n) 10.0 10.0
  checkVec "applyStuff = false leaves the labels" (labelPos g0 outside) 0.0 0.0
  -- Free ports with outside labels. EAST: two 4-high ports, labels 3 + 1 below p0, but the
  -- outermost margins are dropped and the first bottom margin too (2 ports = space efficient):
  -- 4 + 10 + 4 + 2·10 (DISTRIBUTED) = 38. NORTH: 6 + 2·10 = 26.
  let (g, n, ports, l0) := portsGraph
  let ((size, vids), g1) ← runWith g fun a => do
    let s ← NodeLabelAndSizeCalculator.process a n .right
    return (s, ← ports.mapM a.port.getVolatileId)
  checkVec "hand: free ports: size (6 + 2·10, 4 + 10 + 4 + 2·10)" size 26.0 38.0
  checkEq "volatile ids are the port indices" vids #[0, 1, 2]
  checkVec "hand: p0 at the node width, first distributed slot y = 10" (portPos g1 ports[0]!) 26.0 10.0
  checkVec "hand: p1 below p0: y = 10 + 4 + 10" (portPos g1 ports[1]!) 26.0 24.0
  checkVec "hand: single NORTH port centered: x = (26 - 6) / 2, y = -height" (portPos g1 ports[2]!) 10.0 (-2.0)
  checkVec "hand: first EAST port label above the port (2 ports): (4 + 1, -3 - 1)" (labelPos g1 l0) 5.0 (-4.0)
  -- FIXED_POS: width = max(SOUTH border 7 + 4, minimum 50); height = max(minimum 30, EAST border 16)
  let (g, n, ports) := fixedPortsGraph .fixedPos ⟨50.0, 30.0⟩ #[(.south, 7.0, 99.0), (.east, 77.0, 12.0)]
  let (size, g1) ← runWith g fun a => NodeLabelAndSizeCalculator.process a n .right
  checkVec "hand: FIXED_POS: minimum size wins" size 50.0 30.0
  checkVec "hand: FIXED_POS: SOUTH port keeps x, y = node height" (portPos g1 ports[0]!) 7.0 30.0
  checkVec "hand: FIXED_POS: EAST port keeps y, x = node width" (portPos g1 ports[1]!) 50.0 12.0
  -- FIXED_RATIO: elk-rs never sets portRatioOrPosition, so every port sits at ratio 0
  let (g, n, ports) := fixedPortsGraph .fixedRatio ⟨40.0, 20.0⟩ #[(.north, 13.0, 0.0), (.west, 0.0, 9.0)]
  let (size, g1) ← runWith g fun a => NodeLabelAndSizeCalculator.process a n .right
  checkVec "hand: FIXED_RATIO: minimum size" size 40.0 20.0
  checkVec "oracle: FIXED_RATIO NORTH port at x = 40 · 0, y = -4" (portPos g1 ports[0]!) 0.0 (-4.0)
  checkVec "oracle: FIXED_RATIO WEST port at x = -4, y = 20 · 0" (portPos g1 ports[1]!) (-4.0) 0.0
  -- INSIDE port label next to a WEST port: the WEST cell is 10 + spacing 1 wide, mirrored on the
  -- EAST side (symmetric strip): 22; height 4 + 2·10 = 24; port centered at y = (24 - 4) / 2.
  let (g, n, p, l) := insidePortLabelGraph
  let (size, g1) ← runWith g fun a => NodeLabelAndSizeCalculator.process a n .right
  checkVec "hand: inside port labels: size (2·(10 + 1), 4 + 2·10)" size 22.0 24.0
  checkVec "hand: WEST port at (-4, 10)" (portPos g1 p) (-4.0) 10.0
  checkVec "hand: inside label right of the port: (4 + 0 + 1, (4 - 2) / 2)" (labelPos g1 l) 5.0 1.0
  -- Importer path: ignoring inside port labels removes the label width
  let (sizeI, gI) ← runWith g fun a => NodeLabelAndSizeCalculator.processWithOptions a n .right false true
  checkVec "hand: ignoreInsidePortLabels: (0, 24)" sizeI 0.0 24.0
  checkVec "ignoreInsidePortLabels + applyStuff = false: node untouched" (nodeSize gI n) 10.0 10.0
  -- A port without side
  let (g, n, _) := fixedPortsGraph .fixedSide ⟨0.0, 0.0⟩ #[]
  let (g, _) := addPort g n none 0.0 0.0 4.0 4.0
  checkThrows "a port without side throws IllegalArgumentException" do
    let _ ← runWith g fun a => NodeLabelAndSizeCalculator.process a n .right
    pure ()

/-! ### `processNode` (elk-rs simplified path) -/

/-- Root ⊃ node `n` with the given geometry and size constraints. -/
private def plainNode (w h : Float) (constraints : EnumSet SizeConstraint) : ElkGraph × NodeId :=
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n) := g.createNode (some root)
  let g := setGeometry g n 0.0 0.0 w h
  (g.setNodeProp n CoreOptions.NODE_SIZE_CONSTRAINTS constraints, n)

def processNodeTests : Suite := suite "alg.common.nodespacing.NodeLabelAndSizeCalculator.processNode" do
  -- Same graph as the first process test: the simplified path agrees here
  let (g, n, inside, outside) := nodeLabelsGraph
  let (_, g1) ← runWith g fun a => NodeLabelAndSizeCalculator.processNode a n .right
  checkVec "hand: node labels: size (30 + 2·5, 20 + 2·5)" (nodeSize g1 n) 40.0 30.0
  checkVec "hand: inside top-center label" (labelPos g1 inside) 5.0 5.0
  checkVec "hand: outside bottom-center label" (labelPos g1 outside) 10.0 35.0
  -- MINIMUM_SIZE 60×40, COMPUTE_PADDING; WEST outside label 12×6 (V_CENTER, H_LEFT) and inside
  -- bottom-right label 8×4. Rows (4, 0, 4): vertical axis starts [5, 9, 31], free 22 from y = 5.
  -- Row END columns (8, 0, 8): END start 60 - 5 - 8 = 47. WEST strip: 12 + 5 wide, at x = -17.
  let (g, n) := plainNode 10.0 10.0 (EnumSet.of #[SizeConstraint.minimumSize])
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_MINIMUM (⟨60.0, 40.0⟩ : KVector)
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_OPTIONS (EnumSet.of #[SizeOptions.computePadding])
  let (g, west) := addNodeLabel g n 12.0 6.0 (some (EnumSet.of #[.outside, .hLeft, .vCenter]))
  let (g, br) := addNodeLabel g n 8.0 4.0 (some (EnumSet.of #[.inside, .vBottom, .hRight]))
  let (_, g1) ← runWith g fun a => NodeLabelAndSizeCalculator.processNode a n .right
  checkVec "hand: minimum size 60×40" (nodeSize g1 n) 60.0 40.0
  checkVec "hand: inside bottom-right label at (47, 31)" (labelPos g1 br) 47.0 31.0
  checkVec "hand: WEST label right-aligned at x = -17, centered y = (40 - 6) / 2" (labelPos g1 west) (-17.0) 17.0
  checkPadding "hand: computed padding = distance to the free center area (5, 5, 50, 22)"
    ((g1.node n).props.getD CoreOptions.PADDING {}) 5.0 5.0 13.0 5.0
  -- EAST ports with outside labels below p1: 6 + 10 + (6 + 1 + 3) + 10 + 6 + 2·10 = 62; the inside
  -- grid is empty, so the width stays 0
  let (g, n) := plainNode 10.0 10.0 (EnumSet.of #[SizeConstraint.ports, .portLabels, .nodeLabels])
  let (g, _) := addPort g n (some .east) 0.0 0.0 4.0 6.0
  let (g, p1) := addPort g n (some .east) 0.0 0.0 4.0 6.0
  let (g, _) := addPort g n (some .east) 0.0 0.0 4.0 6.0
  let (g, _) := addLabelTo g (.port p1) 0.0 0.0 5.0 3.0
  let (_, g1) ← runWith g fun a => NodeLabelAndSizeCalculator.processNode a n .right
  checkVec "hand: free EAST port height (0, 62)" (nodeSize g1 n) 0.0 62.0
  checkVec "processNode does not move ports" (portPos g1 p1) 0.0 0.0
  -- Fixed size: labels are placed on the current size; centered label in (5, 5, 20, 10)
  let (g, n) := plainNode 30.0 20.0 EnumSet.empty
  let (g, cc) := addNodeLabel g n 10.0 4.0 (some (EnumSet.of #[.inside, .vCenter, .hCenter]))
  let (_, g1) ← runWith g fun a => NodeLabelAndSizeCalculator.processNode a n .right
  checkVec "fixed size constraints keep the size" (nodeSize g1 n) 30.0 20.0
  checkVec "hand: centered label at (5 + (20 - 10) / 2, 5 + (10 - 4) / 2)" (labelPos g1 cc) 10.0 8.0
  -- Compound node with fixed port labels grows to the inside grid: columns (20, 0, 20) + 10,
  -- rows (4, 0, 4) + 10
  let (g, n) := plainNode 10.0 10.0 EnumSet.empty
  let (g, _) := g.createNode (some n)
  let g := g.setNodeProp n CoreOptions.PORT_LABELS_PLACEMENT PortLabelPlacement.fixed
  let (g, tl) := addNodeLabel g n 20.0 4.0 (some (EnumSet.of #[.inside, .vTop, .hLeft]))
  let (_, g1) ← runWith g fun a => NodeLabelAndSizeCalculator.processNode a n .right
  checkVec "hand: compound + fixed port labels: (2·20 + 10, 2·4 + 10)" (nodeSize g1 n) 50.0 18.0
  checkVec "hand: top-left label at the padding (5, 5)" (labelPos g1 tl) 5.0 5.0
  -- Negative border offset and fixed port labels reserve node padding: WEST extension 3, fixed
  -- label inside part 10 + 6 - (4 - 3) = 15 → left 15, mirrored right 15 - 3 = 12
  let (g, n) := plainNode 40.0 30.0 (EnumSet.of #[SizeConstraint.nodeLabels])
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_OPTIONS (EnumSet.empty : EnumSet SizeOptions)
  let g := g.setNodeProp n CoreOptions.PORT_LABELS_PLACEMENT PortLabelPlacement.fixed
  let (g, p) := addPort g n (some .west) 0.0 0.0 4.0 4.0
  let g := g.setPortProp p CoreOptions.PORT_BORDER_OFFSET (-3.0)
  let (g, _) := addLabelTo g (.port p) 6.0 0.0 10.0 4.0
  let (g, cc) := addNodeLabel g n 10.0 4.0 (some (EnumSet.of #[.inside, .vCenter, .hCenter]))
  let (_, g1) ← runWith g fun a => NodeLabelAndSizeCalculator.processNode a n .right
  checkVec "hand: port padding: (10 + 15 + 12 + 10, 4 + 10)" (nodeSize g1 n) 47.0 14.0
  checkVec "hand: center label shifted by the left port padding: (15 + 5, 5)" (labelPos g1 cc) 20.0 5.0
  -- INSIDE port labels widen the inside cell next to the EAST side (mirrored by symmetry)
  let insideLabelNode (constraints : EnumSet SizeConstraint) : ElkGraph × NodeId := Id.run do
    let (g, n) := plainNode 10.0 10.0 constraints
    let g := g.setNodeProp n CoreOptions.PORT_LABELS_PLACEMENT (EnumSet.of #[PortLabelPlacement.inside])
    let g := g.setNodeProp n CoreOptions.NODE_SIZE_MINIMUM (⟨0.0, 30.0⟩ : KVector)
    let (g, p) := addPort g n (some .east) 0.0 0.0 4.0 4.0
    let (g, _) := addLabelTo g (.port p) 0.0 0.0 8.0 2.0
    return (g, n)
  let (g, n) := insideLabelNode (EnumSet.of #[SizeConstraint.nodeLabels, .minimumSize])
  let (_, g1) ← runWith g fun a => NodeLabelAndSizeCalculator.processNode a n .right
  checkVec "hand: MINIMUM_SIZE (default min width 20): no compensation, 2·(8 + 1) + 10, height 30"
    (nodeSize g1 n) 28.0 30.0
  let (g, n) := insideLabelNode (EnumSet.of #[SizeConstraint.nodeLabels])
  let (_, g1) ← runWith g fun a => NodeLabelAndSizeCalculator.processNode a n .right
  checkVec "hand: compensation 8 + 10 + 5 + 0 + 2 (+1 spacing) mirrored: 2·26 + 10, height 0"
    (nodeSize g1 n) 62.0 0.0

/-! ### Inside node label padding / container minimum size -/

/-- elk-rs `inside_node_label_padding_uses_grid_cell_maxima_and_spacing` graph. -/
private def paddingGraph : ElkGraph × NodeId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n) := g.createNode (some root)
  let g := g.setNodeProp root CoreOptions.NODE_LABELS_PADDING
    ({ top := 2.0, right := 3.0, bottom := 4.0, left := 5.0 } : ElkPadding)
  let g := g.setNodeProp root CoreOptions.SPACING_LABEL_LABEL 1.0
  let (g, _) := addNodeLabel g n 6.0 5.0 (some (EnumSet.of #[.inside, .vTop, .hLeft]))
  let (g, _) := addNodeLabel g n 10.0 4.0 (some (EnumSet.of #[.inside, .vTop, .hCenter]))
  let (g, _) := addNodeLabel g n 7.0 8.0 (some (EnumSet.of #[.inside, .vCenter, .hLeft]))
  let (g, _) := addNodeLabel g n 11.0 6.0 (some (EnumSet.of #[.inside, .vBottom, .hRight]))
  return (g, n)

/-- Root (label-label 1) ⊃ node with two inside top-left labels 6×5 and 4×3. -/
private def stackedLabelsGraph : ElkGraph × NodeId :=
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n) := g.createNode (some root)
  let g := g.setNodeProp root CoreOptions.SPACING_LABEL_LABEL 1.0
  let (g, _) := addNodeLabel g n 6.0 5.0 (some (EnumSet.of #[.inside, .vTop, .hLeft]))
  let (g, _) := addNodeLabel g n 4.0 3.0 (some (EnumSet.of #[.inside, .vTop, .hLeft]))
  (g, n)

def insidePaddingTests : Suite := suite "alg.common.nodespacing.NodeLabelAndSizeCalculator.computeInsideNodeLabel*" do
  let (g, n) := paddingGraph
  let (p, _) ← runWith g fun a => NodeLabelAndSizeCalculator.computeInsideNodeLabelPadding a n .right
  checkPadding "rust: padding uses grid cell maxima and spacing (t 9, r 16, b 12, l 14)" p 9.0 16.0 12.0 14.0
  -- Horizontal layout mode stacks labels (6, 5 + 3 + 1); vertical mode puts them side by side
  -- (6 + 4 + 1, 5); each positive side adds padding 5 and the container gap 2
  let (g, n) := stackedLabelsGraph
  let (pr, _) ← runWith g fun a => NodeLabelAndSizeCalculator.computeInsideNodeLabelPadding a n .right
  checkPadding "hand: RIGHT: top 9 + 7, left 6 + 7" pr 16.0 0.0 0.0 13.0
  let (pd, _) ← runWith g fun a => NodeLabelAndSizeCalculator.computeInsideNodeLabelPadding a n .down
  checkPadding "hand: DOWN: top 5 + 7, left 11 + 7" pd 12.0 0.0 0.0 18.0
  let (ms, _) ← runWith g fun a =>
    NodeLabelAndSizeCalculator.computeInsideNodeLabelContainerMinimumSize a n .right
  checkVec "hand: container minimum size: columns (6, 0, 6) + gap 2 + 10, rows (9, 0, 9) + 2 + 10" ms 24.0 30.0
  -- elk-rs inside_node_label_container_minimum_size_handles_tabular_and_center_only_modes
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n) := g.createNode (some root)
  let g := g.setNodeProp root CoreOptions.SPACING_LABEL_LABEL 1.0
  let g := g.setNodeProp root CoreOptions.NODE_LABELS_PADDING (ElkPadding.ofAny 1.0)
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_OPTIONS (EnumSet.of #[SizeOptions.forceTabularNodeLabels])
  let (g, _) := addNodeLabel g n 10.0 3.0 (some (EnumSet.of #[.inside, .vTop, .hLeft]))
  let (g, _) := addNodeLabel g n 4.0 3.0 (some (EnumSet.of #[.inside, .vBottom, .hRight]))
  let (tab, _) ← runWith g fun a =>
    NodeLabelAndSizeCalculator.computeInsideNodeLabelContainerMinimumSize a n .right
  checkVec "rust: tabular minimum size (24, 10)" tab 24.0 10.0
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_CONSTRAINTS (EnumSet.of #[SizeConstraint.minimumSize])
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_OPTIONS (EnumSet.of #[SizeOptions.minimumSizeAccountsForPadding])
  let g := g.setNodeProp n CoreOptions.NODE_SIZE_MINIMUM (⟨40.0, 20.0⟩ : KVector)
  let g := g.setNodeProp root CoreOptions.NODE_LABELS_PADDING (ElkPadding.ofAny 0.0)
  let (center, _) ← runWith g fun a =>
    NodeLabelAndSizeCalculator.computeInsideNodeLabelContainerMinimumSize a n .right
  checkVec "rust: center-only minimum size (40, 20)" center 40.0 20.0

/-! ### `NodeMarginCalculator` -/

/-- elk-rs `create_single_node_graph`: root ⊃ node at (10, 20), 40×30. -/
private def singleNodeGraph : ElkGraph × NodeId × NodeId :=
  let (g, root) := ElkGraphUtil.createGraph
  let (g, n) := g.createNode (some root)
  (setGeometry g n 10.0 20.0 40.0 30.0, root, n)

/-- elk-rs `create_port_tail_label_setup`: label-node spacing 2; source (20×20, outside port
labels) with an EAST port at (20, 8) 2×4 with a label 10×4; an edge to a target node with a TAIL
label 6×3. -/
private def portTailLabelGraph : ElkGraph × NodeId × NodeId := Id.run do
  let (g, root) := ElkGraphUtil.createGraph
  let g := g.setNodeProp root CoreOptions.SPACING_LABEL_NODE 2.0
  let (g, source) := g.createNode (some root)
  let g := setGeometry g source 0.0 0.0 20.0 20.0
  let g := g.setNodeProp source CoreOptions.PORT_LABELS_PLACEMENT PortLabelPlacement.outsideSet
  let (g, port) := addPort g source (some .east) 20.0 8.0 2.0 4.0
  let (g, _) := addLabelTo g (.port port) 0.0 0.0 10.0 4.0
  let (g, target) := g.createNode (some root)
  let g := setGeometry g target 80.0 0.0 20.0 20.0
  let (g, edge) := ElkGraphUtil.createSimpleEdge g (.port port) (.node target)
  let (g, el) := addLabelTo g (.edge edge) 0.0 0.0 6.0 3.0
  return (g.setLabelProp el CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.tail, root, source)

private def margins (g : ElkGraph) (root n : NodeId) (c : NodeMarginCalculator := {}) : IO ElkMargin := do
  let (_, g1) ← runWith g fun a => c.process a root
  return nodeMargin g1 n

def nodeMarginTests : Suite := suite "alg.common.nodespacing.NodeMarginCalculator" do
  -- Node labels
  let (g, root, n) := singleNodeGraph
  let (gl, _) := addLabelTo g (.node n) (-6.0) 5.0 4.0 8.0
  checkFloat "rust: includes node labels (left 6)" (← margins gl root n).left 6.0
  checkFloat "rust: excludes node labels when configured" (← margins gl root n NodeMarginCalculator.new.excludeLabels).left 0.0
  -- Ports
  let (gp, _) := addPort g n none 38.0 8.0 6.0 10.0
  checkFloat "rust: includes ports (right 4)" (← margins gp root n).right 4.0
  checkFloat "rust: excludes ports when configured" (← margins gp root n NodeMarginCalculator.new.excludePorts).right 0.0
  -- Port labels
  let (gpl, p) := addPort g n none 5.0 10.0 4.0 4.0
  let (gpl, _) := addLabelTo gpl (.port p) 36.0 0.0 10.0 4.0
  checkFloat "rust: includes port labels (right 11)" (← margins gpl root n).right 11.0
  checkFloat "rust: excludes port labels when configured"
    (← margins gpl root n NodeMarginCalculator.new.excludePortLabels).right 0.0
  -- Edge end labels at ports
  let (gt, rootT, source) := portTailLabelGraph
  checkFloat "rust: tail label right of an EAST port with outside port labels (right 22)"
    (← margins gt rootT source).right 22.0
  checkFloat "rust: edge end labels ignored when disabled (right 10)"
    (← margins gt rootT source NodeMarginCalculator.new.excludeEdgeHeadTailLabels).right 10.0
  -- elk-rs node_margin_calculator_places_head_label_left_of_west_port
  let (gh, rootH) := ElkGraphUtil.createGraph
  let gh := gh.setNodeProp rootH CoreOptions.SPACING_LABEL_NODE 2.0
  let (gh, src) := gh.createNode (some rootH)
  let gh := setGeometry gh src 0.0 0.0 20.0 20.0
  let (gh, tgt) := gh.createNode (some rootH)
  let gh := setGeometry gh tgt 50.0 0.0 20.0 20.0
  let (gh, tp) := addPort gh tgt (some .west) (-2.0) 8.0 2.0 4.0
  let (gh, e) := ElkGraphUtil.createSimpleEdge gh (.node src) (.port tp)
  let (gh, hl) := addLabelTo gh (.edge e) 0.0 0.0 6.0 3.0
  let gh := gh.setLabelProp hl CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.head
  checkFloat "rust: head label left of a WEST port (left 12)" (← margins gh rootH tgt).left 12.0
  -- Node-to-node edge: TAIL label right of the source (20 + 2 + 6 - 20), HEAD label left of the
  -- target (50 - (50 - 2 - 6)); a CENTER label is ignored
  let (gn, rootN) := ElkGraphUtil.createGraph
  let gn := gn.setNodeProp rootN CoreOptions.SPACING_LABEL_NODE 2.0
  let (gn, a) := gn.createNode (some rootN)
  let gn := setGeometry gn a 0.0 0.0 20.0 20.0
  let (gn, b) := gn.createNode (some rootN)
  let gn := setGeometry gn b 50.0 0.0 20.0 20.0
  let (gn, e) := ElkGraphUtil.createSimpleEdge gn (.node a) (.node b)
  let (gn, tl) := addLabelTo gn (.edge e) 0.0 0.0 6.0 3.0
  let (gn, hl) := addLabelTo gn (.edge e) 0.0 0.0 6.0 3.0
  let (gn, _) := addLabelTo gn (.edge e) 0.0 0.0 100.0 100.0
  let gn := (gn.setLabelProp tl CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.tail).setLabelProp hl
    CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.head
  let (_, gn1) ← runWith gn fun ad => NodeMarginCalculator.new.process ad rootN
  checkFloat "hand: TAIL label at the node: source right 2 + 6" (nodeMargin gn1 a).right 8.0
  checkFloat "hand: HEAD label at the node: target left 2 + 6" (nodeMargin gn1 b).left 8.0
  checkFloat "hand: CENTER label ignored (source bottom 0)" (nodeMargin gn1 a).bottom 0.0
  -- NORTH port with an outside label (5, -4) 6×3 and a TAIL label 5×2: required label space
  -- (-2 + 6 + 2, -2 + 3 + 2) = (6, 3); tail box y = -2 - (2 + 3 + 2 + 2) = -11
  let (gq, rootQ) := ElkGraphUtil.createGraph
  let gq := gq.setNodeProp rootQ CoreOptions.SPACING_LABEL_NODE 2.0
  let (gq, q) := gq.createNode (some rootQ)
  let gq := setGeometry gq q 0.0 0.0 20.0 20.0
  let gq := gq.setNodeProp q CoreOptions.PORT_LABELS_PLACEMENT PortLabelPlacement.outsideSet
  let (gq, qp) := addPort gq q (some .north) 8.0 (-2.0) 4.0 2.0
  let (gq, _) := addLabelTo gq (.port qp) 5.0 (-4.0) 6.0 3.0
  let (gq, far) := gq.createNode (some rootQ)
  let gq := setGeometry gq far 0.0 (-100.0) 20.0 20.0
  let (gq, qe) := ElkGraphUtil.createSimpleEdge gq (.port qp) (.node far)
  let (gq, ql) := addLabelTo gq (.edge qe) 0.0 0.0 5.0 2.0
  let gq := gq.setLabelProp ql CoreOptions.EDGE_LABELS_PLACEMENT EdgeLabelPlacement.tail
  let mq ← margins gq rootQ q
  checkFloat "hand: NORTH port tail label above the port labels (top 11)" mq.top 11.0
  -- The node-level pass sees the port's edge too (NodeAdapter.getOutgoingEdges = all outgoing
  -- edges, like elk-rs): a second tail box right of the node at x = 20 + 2
  checkFloat "hand: node-level tail box (22, 0, 5, 2) gives right 2 + 5" mq.right 7.0
  checkFloat "hand: without edge end labels only the port label counts (top 2 + 4)"
    (← margins gq rootQ q NodeMarginCalculator.new.excludeEdgeHeadTailLabels).top 6.0
  -- processNode with a single node
  let (_, g1) ← runWith gl fun ad => NodeMarginCalculator.new.processNode ad root n
  checkFloat "processNode: same margin as process" (nodeMargin g1 n).left 6.0

def suites : Array Tests.Suite :=
  #[helperTests, processTests, processNodeTests, insidePaddingTests, nodeMarginTests]

end Tests.AlgCommon.NodeSpacing.Calculators
