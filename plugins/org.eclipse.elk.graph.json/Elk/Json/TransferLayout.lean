import Elk.Json.Importer
import Elk.Core.Util.FloatConst
open Elk.Core.Util.FloatConst
/-!
# JSON layout transfer (`org.eclipse.elk.graph.json.JsonImporter`, part 3: `transferLayout`)

Writes the laid-out `ElkGraph` back into the JSON document the importer
read, honouring the `elk.json.shapeCoords`/`elk.json.edgeCoords` modes. The
compaction and port-shift corrections are ported from elk-rs verbatim; they
keep the JSON output of special cases (inside self loops, zero-size ports)
identical to Java ELK (see HISTORY.md for the follow-up).
-/

namespace Elk.Json

open Elk Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Core.Data
open ImportM

namespace JsonImporter

/-! Float constants of the per-element checks (top-level, so they are loaded instead of being
rebuilt by `Float.ofScientific` on every evaluation). -/
private def EPS9 : Float := 1e-9
private def TWO : Float := 2.0
private def FOUR : Float := 4.0
private def TWELVE : Float := 12.0
private def TWENTY_FOUR : Float := 24.0
private def SIXTY_FOUR : Float := 64.0

/-- Whether `s.toUpper` contains `sub` (upper-case ASCII). `String.toUpper` only maps ASCII
letters, so a byte-wise search with ASCII case folding is equivalent (and allocates nothing). -/
def containsUpper (s sub : String) : Bool :=
  let n := s.utf8ByteSize
  let m := sub.utf8ByteSize
  let up (b : UInt8) : UInt8 := if b >= 97 && b <= 122 then b - 32 else b
  let rec matchAt (i k : Nat) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => true
    | fuel + 1 => up (ElkEnum.utf8ByteAt s (i + k)) == ElkEnum.utf8ByteAt sub k && matchAt i (k + 1) fuel
  let rec search (i : Nat) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 => matchAt i 0 m || search (i + 1) fuel
  if m > n then false else search 0 (n - m + 1)

/-- `parse_bool_layout_option`. -/
def parseBoolLayoutOption (v : Value) : Option Bool :=
  match v with
  | .bool b => some b
  | .str s => PropValue.parseBool? (s.trimAscii.toString)
  | _ => none

/-- `parse_port_constraints_layout_option`. -/
def parsePortConstraintsLayoutOption (v : Value) : Option PortConstraints :=
  match v with
  | .num n =>
    match n.toInt? with
    | some i => if i >= 0 then ElkEnum.ofOrdinal? i.toNat else none
    | none => none
  | .str s =>
    -- the canonical spellings are fixed points of the normalisation below
    match s with
    | "UNDEFINED" => some .undefined
    | "FREE" => some .free
    | "FIXED_SIDE" => some .fixedSide
    | "FIXED_ORDER" => some .fixedOrder
    | "FIXED_RATIO" => some .fixedRatio
    | "FIXED_POS" => some .fixedPos
    | _ =>
    let normalized := ((s.trimAscii.toString.toUpper.replace "-" "_").replace " " "_")
    match normalized with
    | "UNDEFINED" => some .undefined
    | "FREE" => some .free
    | "FIXED_SIDE" | "FIXEDSIDE" => some .fixedSide
    | "FIXED_ORDER" | "FIXEDORDER" => some .fixedOrder
    | "FIXED_RATIO" | "FIXEDRATIO" => some .fixedRatio
    | "FIXED_POS" | "FIXEDPOS" => some .fixedPos
    | _ => none
  | _ => none

@[inline] def modAt (path : JsonPath) (f : Value → Value) : ImportM Unit :=
  modI (·.modifyModel (·.modifyAtFrom path 0 f))

@[inline] def getAt (path : JsonPath) : ImportM (Option Value) := do
  return (← getI).model.getAtFrom path 0

/-- `json_object_mut`: the object at the path (error if missing or not an object). -/
def objectAt (path : JsonPath) : ImportM Value := do
  match ← getAt path with
  | some v@(.obj _) => return v
  | some _ => throwJsonImport "Expected JSON object."
  | none => throwJsonImport "JSON pointer did not resolve."

/-- `json_parent`: the JSON parent element of a graph element. -/
def jsonParent (el : ElementId) : ImportM (Option ElementId) := do
  let g ← getG
  match el with
  | .node n => return ((g.node n).parent).map ElementId.node
  | .port p => return ((g.port p).parent).map ElementId.node
  | .edge e => return (tableGet? (← getI).edgeOriginalParent e.idx).map ElementId.node
  | .label l => return (g.label l).parent

/-- `shape_ancestor`: edges resolve to their original parent node. -/
def shapeAncestor (el : ElementId) : ImportM (Option ElementId) := do
  match el with
  | .edge e => return (tableGet? (← getI).edgeOriginalParent e.idx).map ElementId.node
  | other => return some other

def globalX (el : ElementId) : ImportM Float := do
  match el with
  | .edge _ => return 0.0
  | _ =>
    let t := (← getI).tables
    return t.globalX.get! (t.index el)

def globalY (el : ElementId) : ImportM Float := do
  match el with
  | .edge _ => return 0.0
  | _ =>
    let t := (← getI).tables
    return t.globalY.get! (t.index el)

def shapeCoordsMode (el : ElementId) : ImportM ShapeCoords := do
  let t := (← getI).tables
  return t.shapeCoords.getD (t.index el) .parent

def edgeCoordsMode (el : ElementId) : ImportM EdgeCoords := do
  let t := (← getI).tables
  return t.edgeCoords.getD (t.index el) .container

/-- Coordinate modes of an element with properties `props` and JSON parent `parent`
(`record_coordinate_modes`: `INHERIT` resolves through the JSON parent chain). -/
def coordinateModes (props : PropertyMap) (parent : Option ElementId) : ImportM (ShapeCoords × EdgeCoords) := do
  let mut shapeMode := (props.get? CoreOptions.JSON_SHAPE_COORDS).getD .inherit
  if shapeMode == .inherit then
    shapeMode ← match parent with
      | some p => shapeCoordsMode p
      | none => pure .parent
  let mut edgeMode := (props.get? CoreOptions.JSON_EDGE_COORDS).getD .inherit
  if edgeMode == .inherit then
    edgeMode ← match parent with
      | some p => edgeCoordsMode p
      | none => pure .container
  return (shapeMode, edgeMode)

/-- `record_coordinate_modes`: resolves `INHERIT` through the JSON parent chain. -/
def recordCoordinateModes (el : ElementId) : ImportM Unit := do
  let parent ← jsonParent el
  let (sm, em) ← coordinateModes ((← getG).props el) parent
  let i := (← getI).tables.index el
  modI (·.modifyTables (·.setModes i sm em))

/-! Pure readers of the transfer tables (`globalX`, `shapeCoordsMode`, … on a table value read
once), so the per-shape records below return plain floats and enum values. -/

@[inline] def tableGX (t : TransferTables) : ElementId → Float
  | .edge _ => fl0p0
  | el => t.globalX.get! (t.index el)

@[inline] def tableGY (t : TransferTables) : ElementId → Float
  | .edge _ => fl0p0
  | el => t.globalY.get! (t.index el)

/-- `coordinateModes`' shape mode: the element's own mode unless it is `INHERIT` (or unset), then
the JSON parent's (`PARENT` at the root). -/
@[inline] def resolveShapeMode (t : TransferTables) (props : PropertyMap) (parent : Option ElementId) : ShapeCoords :=
  match props.get? CoreOptions.JSON_SHAPE_COORDS with
  | some .parent => .parent
  | some .root => .root
  | _ =>
    match parent with
    | some p => t.shapeCoords.getD (t.index p) .parent
    | none => .parent

/-- `coordinateModes`' edge mode (`CONTAINER` at the root). -/
@[inline] def resolveEdgeMode (t : TransferTables) (props : PropertyMap) (parent : Option ElementId) : EdgeCoords :=
  match props.get? CoreOptions.JSON_EDGE_COORDS with
  | some .container => .container
  | some .parent => .parent
  | some .root => .root
  | _ =>
    match parent with
    | some p => t.edgeCoords.getD (t.index p) .container
    | none => .container

/-- The global coordinates (`record_global_coords_*`) and the coordinate modes
(`record_coordinate_modes`) of a node, port or label, in one state update. `parent` is both the
element's parent and its JSON parent (they coincide for shapes). The two records touch different
entries, so recording them together keeps the reference order's results. The values come from one
read of the tables (which must be dead before the update, so it stays in place). -/
def recordShape (el : ElementId) (parent : Option ElementId) (x y : Float) (props : PropertyMap) : ImportM Unit := do
  let st ← getI
  -- `shape_ancestor`: edges resolve to their original parent node
  let ancestor : Option ElementId := match parent with
    | some (.edge e) => (tableGet? st.edgeOriginalParent e.idx).map ElementId.node
    | other => other
  let t := st.tables
  let dx := match ancestor with
    | some a => tableGX t a
    | none => 0.0
  let dy := match ancestor with
    | some a => tableGY t a
    | none => 0.0
  let sm := resolveShapeMode t props parent
  let em := resolveEdgeMode t props parent
  let gx := x + dx
  let gy := y + dy
  let i := t.index el
  modI (·.modifyTables (·.setShape i gx gy sm em))

/-- The coordinate adjustment of one edge (`adjust_edge_x` / `adjust_edge_y`) with its per-edge
lookups (coordinate mode, `insideSelfLoops.yo`, global offsets, self-loop compaction) done once.
`kind`: `0` keeps the value, `1` adds the containing node's global offset (`ROOT`), `2` adds it and
subtracts the original parent's (`PARENT`). `err`: `1` "Edge has no container.", `2` "Edge has no
original parent." (thrown at the first adjustment, like the reference). -/
structure EdgeAdjust where
  kind : UInt8 := 0
  cx : Float := fl0p0
  cy : Float := fl0p0
  ox : Float := fl0p0
  oy : Float := fl0p0
  /-- Self loop of a compacted node: x values right of `sourceX + 1e-9` move left by `delta`. -/
  selfLoop : Bool := false
  sourceX : Float := fl0p0
  delta : Float := fl0p0
  err : UInt8 := 0

/-- `EdgeAdjust` of edge `e` on the importer state and graph (pure; the values it reads are fixed
during the edge's transfer: global coordinates and compaction deltas of nodes are recorded before any
edge). -/
def edgeAdjustOf (st : ImporterState) (g : ElkGraph) (e : EdgeId) : EdgeAdjust :=
  let t := st.tables
  let original := tableGet? st.edgeOriginalParent e.idx
  let mode : EdgeCoords := match original with
    | some p => t.edgeCoords.getD (t.index (.node p)) .container
    | none => .container
  let edge := g.edge e
  let yo := edge.props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false
  match edge.containingNode with
  | none => { err := 1 }
  | some containing =>
    let cx := tableGX t (.node containing)
    let cy := tableGY t (.node containing)
    let base : EdgeAdjust := match mode with
      | .root => if yo then {} else { kind := 1, cx, cy }
      | .parent =>
        if yo then {}
        else
          match original with
          | some orig => { kind := 2, cx, cy, ox := tableGX t (.node orig), oy := tableGY t (.node orig) }
          | none => { err := 2 }
      | _ => {}
    let sourceNode := (edge.sources[0]?).bind (ElkGraphUtil.connectableShapeToNode g)
    let targetNode := (edge.targets[0]?).bind (ElkGraphUtil.connectableShapeToNode g)
    match sourceNode, targetNode with
    | some s, some tn =>
      if s == tn then
        match st.insideSelfLoopNodeXDelta.get? s with
        | some delta => { base with selfLoop := true, sourceX := tableGX t (.node s), delta }
        | none => base
      else base
    | _, _ => base

/-- `EdgeAdjust` of an edge (no state change). -/
def edgeAdjust (e : EdgeId) : ImportM EdgeAdjust := do
  return edgeAdjustOf (← getI) (← getG) e

/-- Throws the error recorded in an `EdgeAdjust`. -/
@[noinline] def EdgeAdjust.throwErr (a : EdgeAdjust) : ImportM Float :=
  if a.err == 1 then throwJsonImport "Edge has no container."
  else throwJsonImport "Edge has no original parent."

/-- `adjust_edge_x` with a precomputed `EdgeAdjust` (same operations in the same order). -/
@[inline] def EdgeAdjust.adjX (a : EdgeAdjust) (x : Float) : ImportM Float :=
  if a.err != 0 then a.throwErr
  else
    let adjusted := if a.kind == 1 then x + a.cx else if a.kind == 2 then x + a.cx - a.ox else x
    pure (if a.selfLoop && adjusted > a.sourceX + EPS9 then adjusted - a.delta else adjusted)

/-- `adjust_edge_y` with a precomputed `EdgeAdjust`. -/
@[inline] def EdgeAdjust.adjY (a : EdgeAdjust) (y : Float) : ImportM Float :=
  if a.err != 0 then a.throwErr
  else pure (if a.kind == 1 then y + a.cy else if a.kind == 2 then y + a.cy - a.oy else y)

/-- `adjust_edge_x`. -/
def adjustEdgeX (e : EdgeId) (x : Float) : ImportM Float := do
  (← edgeAdjust e).adjX x

/-- `adjust_edge_y`. -/
def adjustEdgeY (e : EdgeId) (y : Float) : ImportM Float := do
  (← edgeAdjust e).adjY y

def adjustParentX (parent : ElementId) (x : Float) : ImportM Float := do
  match parent with
  | .edge e => adjustEdgeX e x
  | _ =>
    match ← shapeCoordsMode parent with
    | .root => return x + (← globalX parent)
    | _ => return x

def adjustParentY (parent : ElementId) (y : Float) : ImportM Float := do
  match parent with
  | .edge e => adjustEdgeY e y
  | _ =>
    match ← shapeCoordsMode parent with
    | .root => return y + (← globalY parent)
    | _ => return y

/-- Writes `x`, `y`, `width`, `height` (in this order) into the object at `path`. -/
@[inline] private def setXywh (path : JsonPath) (x y w h : Float) : ImportM Unit :=
  let vx := Value.ofFloatElk x
  let vy := Value.ofFloatElk y
  let vw := Value.ofFloatElk w
  let vh := Value.ofFloatElk h
  modI (·.modifyModel (·.setXywhAtFrom path 0 vx vy vw vh))

/-- `transfer_xywh_to_json`: writes `x`, `y`, `width`, `height` (in this order). For shape parents
`adjustParentX`/`adjustParentY` are evaluated on one read of the tables (plain floats). -/
def transferXywh (x y w h : Float) (path : JsonPath) (parent : Option ElementId) : ImportM Unit := do
  match parent with
  | some (.edge e) =>
    let ax ← adjustEdgeX e x
    let ay ← adjustEdgeY e y
    setXywh path ax ay w h
  | some p =>
    let t := (← getI).tables
    let root := match t.shapeCoords.getD (t.index p) .parent with
      | .root => true
      | _ => false
    let ax := if root then x + tableGX t p else x
    let ay := if root then y + tableGY t p else y
    setXywh path ax ay w h
  | none => setXywh path x y w h

/-- `recompute_fixed_order_vertical_port_surrounding_height`. -/
def recomputeFixedOrderVerticalPortSurroundingHeight (n : NodeId) : ImportM (Option Float) := do
  let g ← getG
  let ports := (g.node n).ports
  if ports.size < 2 then return none
  let mut minY := Float.posInf
  let mut maxY := Float.negInf
  let mut counted := 0
  let mut allZeroSized := true
  for p in ports do
    let port := g.port p
    let side := port.props.getD CoreOptions.PORT_SIDE .undefined
    if side != .east && side != .west then return none
    if port.width.abs > EPS9 || port.height.abs > EPS9 then allZeroSized := false
    minY := fmin minY port.y
    maxY := fmax maxY (port.y + port.height)
    counted := counted + 1
  if !allZeroSized || counted < 2 || !minY.isFinite || !maxY.isFinite || minY <= 0.0 then return none
  return some (maxY + minY)

/-- The decisions of `transfer_layout_node` that depend on the node's JSON options and on the laid-out
node, its ports and children (shared by `transferLayoutNode` and the overlay transfer
`TransferOverlay`). -/
structure NodeCompaction where
  /-- `should_compact_inside_self_loop_node`. -/
  insideSelfLoop : Bool
  /-- `should_compact_passthrough_node`. -/
  passthrough : Bool
  /-- `should_compact_vertical_passthrough_node`. -/
  vertical : Bool
  /-- `PORTS` and `PORT_LABELS` size constraints with `FIXED_ORDER` port constraints (the height
  compensation of `recompute_fixed_order_vertical_port_surrounding_height`). -/
  fixedOrderPortLabels : Bool
  /-- The node's width as written to JSON (`Number.ofFloatElk`, read back as a double). -/
  nodeWidth : Float
  /-- The node's height as written to JSON. -/
  nodeHeight : Float

/-- `NodeCompaction` of a node: its JSON object `jsonObj` (the options), the graph and `rootHint`
(`rootIncludeChildrenHint`). -/
def nodeCompaction (jsonObj : Value) (g : ElkGraph) (node : ElkNode) (rootHint : Bool) : NodeCompaction := Id.run do
  -- `(Number.ofFloatElk x).toFloat` is `x` (bit for bit): the integer form is only taken for exactly
  -- integral doubles below `2^63`, which `Float.ofInt` gives back exactly
  let nodeWidth := node.width
  let nodeHeight := node.height
  -- without ports every compaction needs a zero-sized port and the height compensation two ports
  if node.ports.isEmpty then
    return { insideSelfLoop := false, passthrough := false, vertical := false, fixedOrderPortLabels := false,
             nodeWidth, nodeHeight }
  let layoutOptions := match JsonAdapter.optObject jsonObj Key.layoutOptions with
    | some o => some o
    | none => JsonAdapter.optObject jsonObj Key.properties
  let lookup (lo : Value) (full short : String) : Option Value :=
    match lo.get? full with
    | some v => some v
    | none => lo.get? short
  let hasExplicitSizeConstraints := layoutOptions.any fun lo =>
    lo.hasKey CoreOptions.NODE_SIZE_CONSTRAINTS.id || lo.hasKey "nodeSize.constraints"
  let hasPortsAndPortLabelsSizeConstraints :=
    ((layoutOptions.bind fun lo => lookup lo CoreOptions.NODE_SIZE_CONSTRAINTS.id "nodeSize.constraints").bind (·.getStr?)).any fun text =>
      containsUpper text "PORTS" && containsUpper text "PORT_LABELS"
  let hasExplicitPortConstraints := layoutOptions.any fun lo =>
    lo.hasKey CoreOptions.PORT_CONSTRAINTS.id || lo.hasKey "portConstraints"
  let insideSelfLoopsActive :=
    ((layoutOptions.bind fun lo => lookup lo CoreOptions.INSIDE_SELF_LOOPS_ACTIVATE.id "insideSelfLoops.activate").bind parseBoolLayoutOption).getD false
  let portConstraints :=
    ((layoutOptions.bind fun lo => lookup lo CoreOptions.PORT_CONSTRAINTS.id "portConstraints").bind parsePortConstraintsLayoutOption).getD .undefined
  -- port analysis
  let mut hasLeft := false
  let mut hasRight := false
  let mut allCentered := true
  let mut hasPorts := false
  let mut onlyNorthOrSouth := true
  let mut northSouthOnBoundary := true
  let mut allZero := !node.ports.isEmpty
  for p in node.ports do
    let port := g.port p
    let mut side := port.props.getD CoreOptions.PORT_SIDE .undefined
    if side == .undefined then
      if port.y.abs <= EPS9 then side := .north
      else if (port.y - nodeHeight).abs <= EPS9 then side := .south
    hasPorts := true
    if port.x.abs <= EPS9 then hasLeft := true
    if (port.x - nodeWidth).abs <= EPS9 then hasRight := true
    if (port.y - nodeHeight / TWO).abs > EPS9 then allCentered := false
    match side with
    | .north => if port.y.abs > EPS9 then northSouthOnBoundary := false
    | .south => if (port.y - nodeHeight).abs > EPS9 then northSouthOnBoundary := false
    | _ => onlyNorthOrSouth := false
    if !(port.width.abs <= EPS9 && port.height.abs <= EPS9) then allZero := false
  let allPortsZeroSized := allZero
  let hasWestAndEastCenterZeroPorts := allZero && hasLeft && hasRight && allCentered
  let hasOnlyNorthOrSouthBoundaryZeroPorts := allZero && hasPorts && onlyNorthOrSouth && northSouthOnBoundary
  let children := node.children
  let singleChild : Option ElkNode := if children.size == 1 then some (g.node children[0]!) else none
  let hasSinglePointChild := singleChild.any fun c =>
    (c.x - TWELVE).abs <= EPS9 && (c.y - TWELVE).abs <= EPS9 && c.width.abs <= EPS9 && c.height.abs <= EPS9
  let hasSinglePointChildCentered := singleChild.any fun c =>
    (c.x - nodeWidth / TWO).abs <= EPS9 && (c.y - TWELVE).abs <= EPS9 && c.width.abs <= EPS9 && c.height.abs <= EPS9
  let hasNoChildren := children.isEmpty
  let shouldCompactInsideSelfLoopNode := insideSelfLoopsActive && hasNoChildren && !hasExplicitSizeConstraints
    && (!hasExplicitPortConstraints || portConstraints.isSideFixed) && allPortsZeroSized
  let shouldCompactPassthroughNode := !insideSelfLoopsActive && !rootHint && !hasExplicitSizeConstraints
    && hasWestAndEastCenterZeroPorts && hasSinglePointChild
    && (nodeWidth - TWENTY_FOUR).abs <= EPS9 && (nodeHeight - TWENTY_FOUR).abs <= EPS9
  let shouldCompactVerticalPassthroughNode := !insideSelfLoopsActive && !rootHint && !hasExplicitSizeConstraints
    && hasOnlyNorthOrSouthBoundaryZeroPorts && hasSinglePointChildCentered
    && (nodeWidth - SIXTY_FOUR).abs <= EPS9 && (nodeHeight - TWENTY_FOUR).abs <= EPS9
  return { insideSelfLoop := shouldCompactInsideSelfLoopNode, passthrough := shouldCompactPassthroughNode,
           vertical := shouldCompactVerticalPassthroughNode,
           fixedOrderPortLabels := hasPortsAndPortLabelsSizeConstraints && portConstraints == .fixedOrder,
           nodeWidth, nodeHeight }

/-- `transfer_layout_node` including the elk-rs compaction corrections. -/
def transferLayoutNode (n : NodeId) : ImportM Unit := do
  let some path := (pathGet (← getI).nodePath n.idx).segs? | throwJsonImport "Node did not exist in input."
  -- the members read below (`layoutOptions`/`properties`) are not touched by `transferXywh`, and
  -- `width`/`height` read back the values it writes
  let jsonObj ← objectAt path
  let g ← getG
  let node := g.node n
  let c := nodeCompaction jsonObj g node (← getI).rootIncludeChildrenHint
  let parent := node.parent.map ElementId.node
  recordShape (.node n) parent node.x node.y node.props
  transferXywh node.x node.y node.width node.height path parent
  let nodeWidth := c.nodeWidth
  let nodeHeight := c.nodeHeight
  if (c.insideSelfLoop || c.passthrough) && nodeWidth > FOUR then
    let delta := nodeWidth - FOUR
    modI fun s => { s with insideSelfLoopNodeXDelta := s.insideSelfLoopNodeXDelta.insert n delta }
    if let some p := node.parent then
      if c.passthrough then
        modI fun s => { s with passthroughCompactedParentKeys := s.passthroughCompactedParentKeys.push p }
      else if c.insideSelfLoop then
        if (g.node p).children.size == 1 then
          modI fun s => { s with passthroughCompactedParentKeys := s.passthroughCompactedParentKeys.push p }
    modAt path (·.set Key.width (.ofFloatElk FOUR))
  if c.vertical && nodeHeight > FOUR then
    let delta := nodeHeight - FOUR
    modI fun s => { s with compactedVerticalNodeYDelta := s.compactedVerticalNodeYDelta.insert n delta }
    if let some p := node.parent then
      modI fun s => { s with verticalCompactedParentKeys := s.verticalCompactedParentKeys.push p }
    modAt path (·.set Key.height (.ofFloatElk FOUR))
  if c.fixedOrderPortLabels then
    if let some compensated ← recomputeFixedOrderVerticalPortSurroundingHeight n then
      let current := (((← objectAt path).get? Key.height).bind (·.getFloat?)).getD fl0p0
      if compensated > current + EPS9 then
        modAt path (·.set Key.height (.ofFloatElk compensated))

/-- `transfer_layout_port`. -/
def transferLayoutPort (p : PortId) : ImportM Unit := do
  let some path := (pathGet (← getI).portPath p.idx).segs? | throwJsonImport "Port did not exist in input."
  -- (the importer registers paths of JSON objects only, and the transfer never replaces them, so
  -- the `json_object_mut` check of the reference always succeeds here)
  let port := (← getG).port p
  let parent := port.parent.map ElementId.node
  recordShape (.port p) parent port.x port.y port.props
  transferXywh port.x port.y port.width port.height path parent
  if let some parentNode := port.parent then
    -- both deltas are read before any update (the updates do not touch them), and the state value
    -- is dropped before the updates so that they stay in place
    let st ← getI
    let dx? := st.insideSelfLoopNodeXDelta.get? parentNode
    let dy? := st.compactedVerticalNodeYDelta.get? parentNode
    if dx?.isSome || dy?.isSome then
      let side := port.props.getD CoreOptions.PORT_SIDE .undefined
      if let some delta := dx? then
        if side == .east then
          if let some x := ((← objectAt path).get? Key.x).bind (·.getFloat?) then
            modAt path (·.set Key.x (.ofFloatElk (x - delta)))
            modI fun s => { s with shiftedEastPortXDelta := s.shiftedEastPortXDelta.insert p delta }
      if let some delta := dy? then
        if side == .south then
          if let some y := ((← objectAt path).get? Key.y).bind (·.getFloat?) then
            modAt path (·.set Key.y (.ofFloatElk (y - delta)))
            modI fun s => { s with shiftedSouthPortYDelta := s.shiftedSouthPortYDelta.insert p delta }

def adjustXForShiftedEastPort (shape : ConnectableId) (x : Float) : ImportM Float := do
  match shape with
  | .port p => return (((← getI).shiftedEastPortXDelta.get? p).map (x - ·)).getD x
  | .node _ => return x

def adjustYForShiftedSouthPort (shape : ConnectableId) (y : Float) : ImportM Float := do
  match shape with
  | .port p => return (((← getI).shiftedSouthPortYDelta.get? p).map (y - ·)).getD y
  | .node _ => return y

private def pointObject (x y : Float) : Value := .obj #[(Key.x, .ofFloatElk x), (Key.y, .ofFloatElk y)]

/-- `transfer_layout_edge`. -/
def transferLayoutEdge (e : EdgeId) : ImportM Unit := do
  let some path := (pathGet (← getI).edgePath e.idx).segs? | throwJsonImport "Edge did not exist in input."
  recordCoordinateModes (.edge e)
  let st ← getI
  let g ← getG
  let edge := g.edge e
  let adj ← edgeAdjust e
  let edgeId := ((tableGet? st.edgeIds e.idx).map (·.asString)).getD ""
  let isSelfLoop :=
    match edge.sources[0]?, edge.targets[0]? with
    | some s, some t => ElkGraphUtil.connectableShapeToNode g s == ElkGraphUtil.connectableShapeToNode g t
    | _, _ => false
  let mut jsonSections : Array Value := #[]
  for h : i in [0:edge.sections.size] do
    let sec := edge.sections[i]
    let s := g.edgeSection sec
    let base : Value ← match (pathGet st.sectionPath sec.idx).segs? with
      | some sp => do
        match ← getAt sp with
        | some v@(.obj _) => pure v
        | _ => pure (.obj #[])
      | none =>
        let fallbackId := s.identifier.getD s!"{edgeId}_s{i}"
        pure (.obj #[(Key.id, .str fallbackId)])
    let mut startX ← adj.adjX s.startX
    let mut startY ← adj.adjY s.startY
    let mut endX ← adj.adjX s.endX
    let mut endY ← adj.adjY s.endY
    if !isSelfLoop then
      if let some shape := s.incomingShape then
        startX ← adjustXForShiftedEastPort shape startX
        startY ← adjustYForShiftedSouthPort shape startY
      if let some shape := s.outgoingShape then
        endX ← adjustXForShiftedEastPort shape endX
        endY ← adjustYForShiftedSouthPort shape endY
    let mut obj := base.set Key.startPoint (pointObject startX startY)
    obj := obj.set Key.endPoint (pointObject endX endY)
    if !s.bendPoints.isEmpty then
      let mut bends : Array Value := Array.emptyWithCapacity s.bendPoints.size
      for b in s.bendPoints do
        bends := bends.push (pointObject (← adj.adjX b.x) (← adj.adjY b.y))
      obj := obj.set Key.bendPoints (.arr bends)
    if let some shape := s.incomingShape then
      if let some id := idByElement st shape then obj := obj.set Key.incomingShape id.toValue
    if let some shape := s.outgoingShape then
      if let some id := idByElement st shape then obj := obj.set Key.outgoingShape id.toValue
    if !s.incomingSections.isEmpty then
      let ids := s.incomingSections.filterMap fun sid => (tableGet? st.sectionIds sid.idx).map (·.toValue)
      obj := obj.set Key.incomingSections (.arr ids)
    if !s.outgoingSections.isEmpty then
      let ids := s.outgoingSections.filterMap fun sid => (tableGet? st.sectionIds sid.idx).map (·.toValue)
      obj := obj.set Key.outgoingSections (.arr ids)
    jsonSections := jsonSections.push obj
  let junctionPoints : Option KVectorChain :=
    if edge.props.has CoreOptions.JUNCTION_POINTS then edge.props.get CoreOptions.JUNCTION_POINTS else none
  let containerId ← match tableGet? st.edgeOriginalParent e.idx with
    | some orig =>
      if (← edgeCoordsMode (.node orig)) == .container then
        pure (edge.containingNode.bind fun c => (g.node c).identifier)
      else pure none
    | none => pure none
  if !jsonSections.isEmpty then
    modAt path fun o => (o.remove Key.sections).set Key.sections (.arr jsonSections)
  if let some jps := junctionPoints then
    if !jps.isEmpty then
      let mut arr : Array Value := #[]
      for jp in jps do
        arr := arr.push (pointObject (← adj.adjX jp.x) (← adj.adjY jp.y))
      modAt path (·.set Key.junctionPoints (.arr arr))
  if let some cid := containerId then
    modAt path (·.set Key.container (.str cid))
where
  idByElement (st : ImporterState) : ConnectableId → Option JsonId
    | .node n => tableGet? st.nodeIds n.idx
    | .port p => tableGet? st.portIds p.idx

/-- `transfer_layout_label`. -/
def transferLayoutLabel (l : LabelId) : ImportM Unit := do
  let some path := (pathGet (← getI).labelPath l.idx).segs? | throwJsonImport "Label did not exist in input."
  -- (`path` holds a JSON object, see `transferLayoutPort`)
  let label := (← getG).label l
  let parent := label.parent
  recordShape (.label l) parent label.x label.y label.props
  transferXywh label.x label.y label.width label.height path parent

/-- `recompute_compacted_parent_width_candidate`. -/
def recomputeCompactedParentWidthCandidate (parentObj : Value) : Option Float := Id.run do
  let some children := JsonAdapter.optArray parentObj Key.children | return none
  if children.isEmpty then return none
  let mut maxChildRight := Float.negInf
  for child in children do
    if !child.isObj then continue
    let some x := (child.get? Key.x).bind (·.getFloat?) | continue
    let some width := (child.get? Key.width).bind (·.getFloat?) | continue
    maxChildRight := fmax maxChildRight (x + width + TWELVE)
  if !maxChildRight.isFinite then return none
  let childSpanCandidate := maxChildRight
  let mut edgeMaxX := Float.negInf
  if let some edges := JsonAdapter.optArray parentObj Key.edges then
    for edge in edges do
      let some sections := JsonAdapter.optArray edge Key.sections | continue
      for sec in sections do
        if let some sx := ((sec.get? Key.startPoint).bind (·.get? Key.x)).bind (·.getFloat?) then
          edgeMaxX := fmax edgeMaxX sx
        if let some ex := ((sec.get? Key.endPoint).bind (·.get? Key.x)).bind (·.getFloat?) then
          edgeMaxX := fmax edgeMaxX ex
        if let some bends := JsonAdapter.optArray sec Key.bendPoints then
          for b in bends do
            if let some bx := (b.get? Key.x).bind (·.getFloat?) then
              edgeMaxX := fmax edgeMaxX bx
  if edgeMaxX.isFinite then
    let mut candidate := fmax childSpanCandidate edgeMaxX
    if children.size > 1 then
      candidate := fmax candidate (childSpanCandidate + edgeMaxX)
    return some candidate
  else
    return some childSpanCandidate

private def dedup (keys : Array NodeId) : Array NodeId := Id.run do
  let mut seen : Std.HashSet NodeId := {}
  let mut out : Array NodeId := #[]
  for k in keys do
    if !seen.contains k then
      seen := seen.insert k
      out := out.push k
  return out

/-- `fix_parent_widths_for_compacted_passthrough_nodes`. -/
def fixParentWidthsForCompactedPassthroughNodes : ImportM Unit := do
  let st ← getI
  if st.passthroughCompactedParentKeys.isEmpty || st.rootIncludeChildrenHint then return
  for parentKey in dedup st.passthroughCompactedParentKeys do
    let some path := (pathGet st.nodePath parentKey.idx).segs? | continue
    let parentObj ← objectAt path
    let hasPorts := (JsonAdapter.optArray parentObj Key.ports).any (!·.isEmpty)
    if hasPorts then continue
    let some candidate := recomputeCompactedParentWidthCandidate parentObj | continue
    let some current := (parentObj.get? Key.width).bind (·.getFloat?) | continue
    if candidate > fl0p0 && candidate + EPS9 < current then
      modAt path (·.set Key.width (.ofFloatElk candidate))

/-- `fix_parent_heights_for_compacted_vertical_nodes`. -/
def fixParentHeightsForCompactedVerticalNodes : ImportM Unit := do
  let st ← getI
  if st.verticalCompactedParentKeys.isEmpty || st.rootIncludeChildrenHint then return
  for parentKey in dedup st.verticalCompactedParentKeys do
    let some path := (pathGet st.nodePath parentKey.idx).segs? | continue
    let parentObj ← objectAt path
    let hasPorts := (JsonAdapter.optArray parentObj Key.ports).any (!·.isEmpty)
    if hasPorts then continue
    let some children := JsonAdapter.optArray parentObj Key.children | continue
    if children.isEmpty then continue
    let childPrefix := path ++ #[.key Key.children]
    let mut ordered : Array (Nat × Float × Float) := #[]
    for h : i in [0:children.size] do
      let child := children[i]
      let some y := (child.get? Key.y).bind (·.getFloat?) | continue
      let childPath := childPrefix ++ #[.idx i]
      let childKey := (st.nodePath.findIdx? fun p => p.segs? == some childPath).map (⟨·⟩ : Nat → NodeId)
      let delta := (childKey.bind fun k => st.compactedVerticalNodeYDelta.get? k).getD fl0p0
      ordered := ordered.push (i, y, delta)
    let sortedChildren := stableSort ordered (fun a b => Float.comparePartial a.2.1 b.2.1)
    let mut cumulative := fl0p0
    let mut total := fl0p0
    for (i, originalY, delta) in sortedChildren do
      if cumulative.abs > EPS9 then
        modAt (childPrefix ++ #[.idx i]) (·.set Key.y (.ofFloatElk (originalY - cumulative)))
      if delta > fl0p0 then
        cumulative := cumulative + delta
        total := total + delta
    if total > fl0p0 then
      if let some current := (parentObj.get? Key.height).bind (·.getFloat?) then
        modAt path (·.set Key.height (.ofFloatElk (fmax (current - total) fl0p0)))

/-- `transfer_nodes_and_ports`: stack based traversal (children pushed in order, popped last-first). -/
def transferNodesAndPorts (root : NodeId) : ImportM Unit := do
  let mut stack : Array NodeId := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    transferLayoutNode n
    let node := (← getG).node n
    for p in node.ports do transferLayoutPort p
    for c in node.children do stack := stack.push c

/-- `transfer_edges_and_labels`. -/
def transferEdgesAndLabels (root : NodeId) : ImportM Unit := do
  let mut stack : Array NodeId := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    let g ← getG
    let node := g.node n
    for l in node.labels do transferLayoutLabel l
    for p in node.ports do
      for l in (g.port p).labels do transferLayoutLabel l
    for e in node.containedEdges do
      transferLayoutEdge e
      for l in ((← getG).edge e).labels do transferLayoutLabel l
    for c in node.children do stack := stack.push c

/-- `transfer_layout`: writes the layout of the imported graph into the JSON model. -/
def transferLayout : ImportM Unit := do
  let st ← getI
  let some root := st.rootNode | throwJsonImport "No input model available."
  let hint := Id.run do
    let opts := match JsonAdapter.optObject st.model Key.layoutOptions with
      | some o => some o
      | none => JsonAdapter.optObject st.model Key.properties
    let v := opts.bind fun o => match o.get? "org.eclipse.elk.hierarchyHandling" with
      | some v => some v
      | none => o.get? "hierarchyHandling"
    return ((v.bind (·.getStr?)).map fun s => s.toUpper == "INCLUDE_CHILDREN").getD false
  let g ← getG
  let tables := TransferTables.create g.nodes.size g.ports.size g.labels.size g.edges.size
  modI fun s => { s with rootIncludeChildrenHint := hint, tables }
  transferNodesAndPorts root
  transferEdgesAndLabels root
  fixParentWidthsForCompactedPassthroughNodes
  fixParentHeightsForCompactedVerticalNodes

end JsonImporter

/-- Convenience: import a document into a fresh arena. Returns the root node,
the importer state (needed for `transferLayout`) and the graph. -/
def importGraph (doc : Value) (defaults : Option GlobalOptions := none) : IO (NodeId × ImporterState × ElkGraph) := do
  let ((root, st), g) ← (ImportM.run (JsonImporter.transform doc) { defaults }).run {}
  return (root, st, g)

end Elk.Json
