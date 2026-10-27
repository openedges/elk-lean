import Elk.Json.Importer
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

/-- Updates the transfer tables (taken out of the state first, so they stay uniquely referenced). -/
@[inline] def modifyTables (s : ImporterState) (f : TransferTables → TransferTables) : ImporterState :=
  let t := s.tables
  let s := { s with tables := {} }
  { s with tables := f t }

/-- Whether `s.toUpper` contains `sub` (upper-case ASCII). `String.toUpper` only maps ASCII
letters, so a byte-wise search with ASCII case folding is equivalent (and allocates nothing). -/
private def containsUpper (s sub : String) : Bool :=
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
  modI fun s => { s with model := s.model.modifyAtFrom path 0 f }

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

/-- `record_coordinate_modes`: resolves `INHERIT` through the JSON parent chain. -/
def recordCoordinateModes (el : ElementId) : ImportM Unit := do
  let parent ← jsonParent el
  let props := (← getG).props el
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
  let sm := shapeMode
  let em := edgeMode
  modI fun s => modifyTables s fun t =>
    let i := t.index el
    { t with shapeCoords := t.shapeCoords.set! i sm, edgeCoords := t.edgeCoords.set! i em }

private def recordGlobal (el : ElementId) (parent : Option ElementId) (x y : Float) : ImportM Unit := do
  let ancestor ← match parent with
    | some p => shapeAncestor p
    | none => pure none
  let dx ← match ancestor with
    | some a => globalX a
    | none => pure 0.0
  let dy ← match ancestor with
    | some a => globalY a
    | none => pure 0.0
  modI fun s => modifyTables s fun t =>
    let i := t.index el
    { t with globalX := t.globalX.set! i (x + dx), globalY := t.globalY.set! i (y + dy) }

def recordGlobalCoordsNode (n : NodeId) : ImportM Unit := do
  let node := (← getG).node n
  recordGlobal (.node n) (node.parent.map ElementId.node) node.x node.y

def recordGlobalCoordsPort (p : PortId) : ImportM Unit := do
  let port := (← getG).port p
  recordGlobal (.port p) (port.parent.map ElementId.node) port.x port.y

def recordGlobalCoordsLabel (l : LabelId) : ImportM Unit := do
  let label := (← getG).label l
  recordGlobal (.label l) label.parent label.x label.y

/-- `adjust_edge_x`. -/
def adjustEdgeX (e : EdgeId) (x : Float) : ImportM Float := do
  let st ← getI
  let g ← getG
  let original := tableGet? st.edgeOriginalParent e.idx
  let mode ← match original with
    | some p => edgeCoordsMode (.node p)
    | none => pure .container
  let edge := g.edge e
  let yo := edge.props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false
  let some containing := edge.containingNode | throwJsonImport "Edge has no container."
  let mut adjusted ← match mode with
    | .root => if yo then pure x else do pure (x + (← globalX (.node containing)))
    | .parent =>
      if yo then pure x
      else do
        let some orig := original | throwJsonImport "Edge has no original parent."
        pure (x + (← globalX (.node containing)) - (← globalX (.node orig)))
    | _ => pure x
  let sourceNode := (edge.sources[0]?).bind (ElkGraphUtil.connectableShapeToNode g)
  let targetNode := (edge.targets[0]?).bind (ElkGraphUtil.connectableShapeToNode g)
  if let (some s, some t) := (sourceNode, targetNode) then
    if s == t then
      if let some delta := st.insideSelfLoopNodeXDelta.get? s then
        let sourceX ← globalX (.node s)
        if adjusted > sourceX + 1e-9 then adjusted := adjusted - delta
  return adjusted

/-- `adjust_edge_y`. -/
def adjustEdgeY (e : EdgeId) (y : Float) : ImportM Float := do
  let st ← getI
  let g ← getG
  let original := tableGet? st.edgeOriginalParent e.idx
  let mode ← match original with
    | some p => edgeCoordsMode (.node p)
    | none => pure .container
  let edge := g.edge e
  let yo := edge.props.getD CoreOptions.INSIDE_SELF_LOOPS_YO false
  let some containing := edge.containingNode | throwJsonImport "Edge has no container."
  match mode with
  | .root => if yo then return y else return y + (← globalY (.node containing))
  | .parent =>
    if yo then return y
    let some orig := original | throwJsonImport "Edge has no original parent."
    return y + (← globalY (.node containing)) - (← globalY (.node orig))
  | _ => return y

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

/-- `transfer_xywh_to_json`: writes `x`, `y`, `width`, `height` (in this order). -/
def transferXywh (x y w h : Float) (path : JsonPath) (parent : Option ElementId) : ImportM Unit := do
  let ax ← match parent with
    | some p => adjustParentX p x
    | none => pure x
  let ay ← match parent with
    | some p => adjustParentY p y
    | none => pure y
  modAt path fun o =>
    match o with
    | .obj kvs =>
      let kvs := Value.setEntry kvs "x" (.ofFloatElk ax)
      let kvs := Value.setEntry kvs "y" (.ofFloatElk ay)
      let kvs := Value.setEntry kvs "width" (.ofFloatElk w)
      .obj (Value.setEntry kvs "height" (.ofFloatElk h))
    | other => other

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
    if port.width.abs > 1e-9 || port.height.abs > 1e-9 then allZeroSized := false
    minY := fmin minY port.y
    maxY := fmax maxY (port.y + port.height)
    counted := counted + 1
  if !allZeroSized || counted < 2 || !minY.isFinite || !maxY.isFinite || minY <= 0.0 then return none
  return some (maxY + minY)

/-- `transfer_layout_node` including the elk-rs compaction corrections. -/
def transferLayoutNode (n : NodeId) : ImportM Unit := do
  let some path := tableGet? (← getI).nodePath n.idx | throwJsonImport "Node did not exist in input."
  -- the members read below (`layoutOptions`/`properties`) are not touched by `transferXywh`, and
  -- `width`/`height` read back the values it writes
  let jsonObj ← objectAt path
  let layoutOptions := match JsonAdapter.optObject jsonObj "layoutOptions" with
    | some o => some o
    | none => JsonAdapter.optObject jsonObj "properties"
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
  recordGlobalCoordsNode n
  recordCoordinateModes (.node n)
  let parent ← jsonParent (.node n)
  let g ← getG
  let node := g.node n
  transferXywh node.x node.y node.width node.height path parent
  let nodeWidth := (Number.ofFloatElk node.width).toFloat
  let nodeHeight := (Number.ofFloatElk node.height).toFloat
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
      if port.y.abs <= 1e-9 then side := .north
      else if (port.y - nodeHeight).abs <= 1e-9 then side := .south
    hasPorts := true
    if port.x.abs <= 1e-9 then hasLeft := true
    if (port.x - nodeWidth).abs <= 1e-9 then hasRight := true
    if (port.y - nodeHeight / 2.0).abs > 1e-9 then allCentered := false
    match side with
    | .north => if port.y.abs > 1e-9 then northSouthOnBoundary := false
    | .south => if (port.y - nodeHeight).abs > 1e-9 then northSouthOnBoundary := false
    | _ => onlyNorthOrSouth := false
    if !(port.width.abs <= 1e-9 && port.height.abs <= 1e-9) then allZero := false
  let allPortsZeroSized := allZero
  let hasWestAndEastCenterZeroPorts := allZero && hasLeft && hasRight && allCentered
  let hasOnlyNorthOrSouthBoundaryZeroPorts := allZero && hasPorts && onlyNorthOrSouth && northSouthOnBoundary
  let children := node.children
  let singleChild : Option ElkNode := if children.size == 1 then some (g.node children[0]!) else none
  let hasSinglePointChild := singleChild.any fun c =>
    (c.x - 12.0).abs <= 1e-9 && (c.y - 12.0).abs <= 1e-9 && c.width.abs <= 1e-9 && c.height.abs <= 1e-9
  let hasSinglePointChildCentered := singleChild.any fun c =>
    (c.x - nodeWidth / 2.0).abs <= 1e-9 && (c.y - 12.0).abs <= 1e-9 && c.width.abs <= 1e-9 && c.height.abs <= 1e-9
  let hasNoChildren := children.isEmpty
  let rootHint := (← getI).rootIncludeChildrenHint
  let shouldCompactInsideSelfLoopNode := insideSelfLoopsActive && hasNoChildren && !hasExplicitSizeConstraints
    && (!hasExplicitPortConstraints || portConstraints.isSideFixed) && allPortsZeroSized
  let shouldCompactPassthroughNode := !insideSelfLoopsActive && !rootHint && !hasExplicitSizeConstraints
    && hasWestAndEastCenterZeroPorts && hasSinglePointChild
    && (nodeWidth - 24.0).abs <= 1e-9 && (nodeHeight - 24.0).abs <= 1e-9
  let shouldCompactVerticalPassthroughNode := !insideSelfLoopsActive && !rootHint && !hasExplicitSizeConstraints
    && hasOnlyNorthOrSouthBoundaryZeroPorts && hasSinglePointChildCentered
    && (nodeWidth - 64.0).abs <= 1e-9 && (nodeHeight - 24.0).abs <= 1e-9
  if (shouldCompactInsideSelfLoopNode || shouldCompactPassthroughNode) && nodeWidth > 4.0 then
    let delta := nodeWidth - 4.0
    modI fun s => { s with insideSelfLoopNodeXDelta := s.insideSelfLoopNodeXDelta.insert n delta }
    if let some p := node.parent then
      if shouldCompactPassthroughNode then
        modI fun s => { s with passthroughCompactedParentKeys := s.passthroughCompactedParentKeys.push p }
      else if shouldCompactInsideSelfLoopNode then
        if (g.node p).children.size == 1 then
          modI fun s => { s with passthroughCompactedParentKeys := s.passthroughCompactedParentKeys.push p }
    modAt path (·.set "width" (.ofFloatElk 4.0))
  if shouldCompactVerticalPassthroughNode && nodeHeight > 4.0 then
    let delta := nodeHeight - 4.0
    modI fun s => { s with compactedVerticalNodeYDelta := s.compactedVerticalNodeYDelta.insert n delta }
    if let some p := node.parent then
      modI fun s => { s with verticalCompactedParentKeys := s.verticalCompactedParentKeys.push p }
    modAt path (·.set "height" (.ofFloatElk 4.0))
  if hasPortsAndPortLabelsSizeConstraints && portConstraints == .fixedOrder then
    if let some compensated ← recomputeFixedOrderVerticalPortSurroundingHeight n then
      let current := (((← objectAt path).get? "height").bind (·.getFloat?)).getD 0.0
      if compensated > current + 1e-9 then
        modAt path (·.set "height" (.ofFloatElk compensated))

/-- `transfer_layout_port`. -/
def transferLayoutPort (p : PortId) : ImportM Unit := do
  let some path := tableGet? (← getI).portPath p.idx | throwJsonImport "Port did not exist in input."
  let _ ← objectAt path
  recordGlobalCoordsPort p
  recordCoordinateModes (.port p)
  let parent ← jsonParent (.port p)
  let port := (← getG).port p
  transferXywh port.x port.y port.width port.height path parent
  if let some parentNode := port.parent then
    let st ← getI
    let side := port.props.getD CoreOptions.PORT_SIDE .undefined
    if let some delta := st.insideSelfLoopNodeXDelta.get? parentNode then
      if side == .east then
        if let some x := ((← objectAt path).get? "x").bind (·.getFloat?) then
          modAt path (·.set "x" (.ofFloatElk (x - delta)))
          modI fun s => { s with shiftedEastPortXDelta := s.shiftedEastPortXDelta.insert p delta }
    if let some delta := st.compactedVerticalNodeYDelta.get? parentNode then
      if side == .south then
        if let some y := ((← objectAt path).get? "y").bind (·.getFloat?) then
          modAt path (·.set "y" (.ofFloatElk (y - delta)))
          modI fun s => { s with shiftedSouthPortYDelta := s.shiftedSouthPortYDelta.insert p delta }

def adjustXForShiftedEastPort (shape : ConnectableId) (x : Float) : ImportM Float := do
  match shape with
  | .port p => return (((← getI).shiftedEastPortXDelta.get? p).map (x - ·)).getD x
  | .node _ => return x

def adjustYForShiftedSouthPort (shape : ConnectableId) (y : Float) : ImportM Float := do
  match shape with
  | .port p => return (((← getI).shiftedSouthPortYDelta.get? p).map (y - ·)).getD y
  | .node _ => return y

private def pointObject (x y : Float) : Value := .obj #[("x", .ofFloatElk x), ("y", .ofFloatElk y)]

/-- `transfer_layout_edge`. -/
def transferLayoutEdge (e : EdgeId) : ImportM Unit := do
  let some path := tableGet? (← getI).edgePath e.idx | throwJsonImport "Edge did not exist in input."
  recordCoordinateModes (.edge e)
  let st ← getI
  let g ← getG
  let edge := g.edge e
  let edgeId := ((tableGet? st.edgeIds e.idx).map (·.asString)).getD ""
  let isSelfLoop :=
    match edge.sources[0]?, edge.targets[0]? with
    | some s, some t => ElkGraphUtil.connectableShapeToNode g s == ElkGraphUtil.connectableShapeToNode g t
    | _, _ => false
  let mut jsonSections : Array Value := #[]
  for h : i in [0:edge.sections.size] do
    let sec := edge.sections[i]
    let s := g.edgeSection sec
    let base : Value ← match tableGet? st.sectionPath sec.idx with
      | some sp => do
        match ← getAt sp with
        | some v@(.obj _) => pure v
        | _ => pure (.obj #[])
      | none =>
        let fallbackId := s.identifier.getD s!"{edgeId}_s{i}"
        pure (.obj #[("id", .str fallbackId)])
    let mut startX ← adjustEdgeX e s.startX
    let mut startY ← adjustEdgeY e s.startY
    let mut endX ← adjustEdgeX e s.endX
    let mut endY ← adjustEdgeY e s.endY
    if !isSelfLoop then
      if let some shape := s.incomingShape then
        startX ← adjustXForShiftedEastPort shape startX
        startY ← adjustYForShiftedSouthPort shape startY
      if let some shape := s.outgoingShape then
        endX ← adjustXForShiftedEastPort shape endX
        endY ← adjustYForShiftedSouthPort shape endY
    let mut obj := base.set "startPoint" (pointObject startX startY)
    obj := obj.set "endPoint" (pointObject endX endY)
    if !s.bendPoints.isEmpty then
      let mut bends : Array Value := #[]
      for b in s.bendPoints do
        bends := bends.push (pointObject (← adjustEdgeX e b.x) (← adjustEdgeY e b.y))
      obj := obj.set "bendPoints" (.arr bends)
    if let some shape := s.incomingShape then
      if let some id := idByElement st shape then obj := obj.set "incomingShape" id.toValue
    if let some shape := s.outgoingShape then
      if let some id := idByElement st shape then obj := obj.set "outgoingShape" id.toValue
    if !s.incomingSections.isEmpty then
      let ids := s.incomingSections.filterMap fun sid => (tableGet? st.sectionIds sid.idx).map (·.toValue)
      obj := obj.set "incomingSections" (.arr ids)
    if !s.outgoingSections.isEmpty then
      let ids := s.outgoingSections.filterMap fun sid => (tableGet? st.sectionIds sid.idx).map (·.toValue)
      obj := obj.set "outgoingSections" (.arr ids)
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
    modAt path fun o => (o.remove "sections").set "sections" (.arr jsonSections)
  if let some jps := junctionPoints then
    if !jps.isEmpty then
      let mut arr : Array Value := #[]
      for jp in jps do
        arr := arr.push (pointObject (← adjustEdgeX e jp.x) (← adjustEdgeY e jp.y))
      modAt path (·.set "junctionPoints" (.arr arr))
  if let some cid := containerId then
    modAt path (·.set "container" (.str cid))
where
  idByElement (st : ImporterState) : ConnectableId → Option JsonId
    | .node n => tableGet? st.nodeIds n.idx
    | .port p => tableGet? st.portIds p.idx

/-- `transfer_layout_label`. -/
def transferLayoutLabel (l : LabelId) : ImportM Unit := do
  let some path := tableGet? (← getI).labelPath l.idx | throwJsonImport "Label did not exist in input."
  let _ ← objectAt path
  recordGlobalCoordsLabel l
  recordCoordinateModes (.label l)
  let parent ← jsonParent (.label l)
  let label := (← getG).label l
  transferXywh label.x label.y label.width label.height path parent

/-- `recompute_compacted_parent_width_candidate`. -/
def recomputeCompactedParentWidthCandidate (parentObj : Value) : Option Float := Id.run do
  let some children := JsonAdapter.optArray parentObj "children" | return none
  if children.isEmpty then return none
  let mut maxChildRight := Float.negInf
  for child in children do
    if !child.isObj then continue
    let some x := (child.get? "x").bind (·.getFloat?) | continue
    let some width := (child.get? "width").bind (·.getFloat?) | continue
    maxChildRight := fmax maxChildRight (x + width + 12.0)
  if !maxChildRight.isFinite then return none
  let childSpanCandidate := maxChildRight
  let mut edgeMaxX := Float.negInf
  if let some edges := JsonAdapter.optArray parentObj "edges" then
    for edge in edges do
      let some sections := JsonAdapter.optArray edge "sections" | continue
      for sec in sections do
        if let some sx := ((sec.get? "startPoint").bind (·.get? "x")).bind (·.getFloat?) then
          edgeMaxX := fmax edgeMaxX sx
        if let some ex := ((sec.get? "endPoint").bind (·.get? "x")).bind (·.getFloat?) then
          edgeMaxX := fmax edgeMaxX ex
        if let some bends := JsonAdapter.optArray sec "bendPoints" then
          for b in bends do
            if let some bx := (b.get? "x").bind (·.getFloat?) then
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
    let some path := tableGet? st.nodePath parentKey.idx | continue
    let parentObj ← objectAt path
    let hasPorts := (JsonAdapter.optArray parentObj "ports").any (!·.isEmpty)
    if hasPorts then continue
    let some candidate := recomputeCompactedParentWidthCandidate parentObj | continue
    let some current := (parentObj.get? "width").bind (·.getFloat?) | continue
    if candidate > 0.0 && candidate + 1e-9 < current then
      modAt path (·.set "width" (.ofFloatElk candidate))

/-- `fix_parent_heights_for_compacted_vertical_nodes`. -/
def fixParentHeightsForCompactedVerticalNodes : ImportM Unit := do
  let st ← getI
  if st.verticalCompactedParentKeys.isEmpty || st.rootIncludeChildrenHint then return
  for parentKey in dedup st.verticalCompactedParentKeys do
    let some path := tableGet? st.nodePath parentKey.idx | continue
    let parentObj ← objectAt path
    let hasPorts := (JsonAdapter.optArray parentObj "ports").any (!·.isEmpty)
    if hasPorts then continue
    let some children := JsonAdapter.optArray parentObj "children" | continue
    if children.isEmpty then continue
    let childPrefix := path ++ #[.key "children"]
    let mut ordered : Array (Nat × Float × Float) := #[]
    for h : i in [0:children.size] do
      let child := children[i]
      let some y := (child.get? "y").bind (·.getFloat?) | continue
      let childPath := childPrefix ++ #[.idx i]
      let childKey := (st.nodePath.findIdx? fun p => p == some childPath).map (⟨·⟩ : Nat → NodeId)
      let delta := (childKey.bind fun k => st.compactedVerticalNodeYDelta.get? k).getD 0.0
      ordered := ordered.push (i, y, delta)
    let sortedChildren := stableSort ordered (fun a b => Float.comparePartial a.2.1 b.2.1)
    let mut cumulative := 0.0
    let mut total := 0.0
    for (i, originalY, delta) in sortedChildren do
      if cumulative.abs > 1e-9 then
        modAt (childPrefix ++ #[.idx i]) (·.set "y" (.ofFloatElk (originalY - cumulative)))
      if delta > 0.0 then
        cumulative := cumulative + delta
        total := total + delta
    if total > 0.0 then
      if let some current := (parentObj.get? "height").bind (·.getFloat?) then
        modAt path (·.set "height" (.ofFloatElk (fmax (current - total) 0.0)))

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
    let opts := match JsonAdapter.optObject st.model "layoutOptions" with
      | some o => some o
      | none => JsonAdapter.optObject st.model "properties"
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
