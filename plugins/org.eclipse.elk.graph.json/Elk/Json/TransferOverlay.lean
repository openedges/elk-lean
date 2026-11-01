import Elk.Json.TransferLayout
/-!
# Layout transfer as an overlay (`org.eclipse.elk.graph.json.JsonImporter`, part 4)

`JsonImporter.transferLayout` writes every result into the JSON document through its path from the
root (a walk down the document per write, and new number/section objects that the printer then
reads and frees). `transferLayoutOverlay` runs the same computation in the same order (same
coordinate tables, compaction records and errors) but keeps the results in flat tables
(`Overlay`): the final `x`/`y`/`width`/`height` of every shape and the sections, junction points and
container of every edge. The document stays as it was imported. `OverlayPrinter` then prints the
document with the results in place (no intermediate tree), and `Overlay.materialize` builds the
document `transferLayout` would have produced (pretty/sorted output and the test reference).

Applying the results needs the element of every JSON object: `ElemIndex` (recorded by the importer)
gives the ids of the elements of an object's `ports`/`labels`/`edges` arrays and the node preorder of
`children`. Writes of one element only touch its own object (`transferLayout` replaces or appends
the first member of a key, removes the first `sections` member), so they can be applied in document
order. The overlay is not used (`Overlay.ok` false, `transferLayout` runs instead) when the parent
size corrections (`fixParentWidthsForCompactedPassthroughNodes`, `fix…Heights…`, which read the
rewritten document) apply, when two nodes share an id, or when a section's path is not in its
edge's `sections` array.
-/
/-! Float literals as global constants (FL, PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def EPS9 : Float := 1e-9
private def FOUR : Float := 4.0

namespace Elk.Json

open Elk Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Math Elk.Core.Options Elk.Core.Data
open ImportM

/-- One edge section as `transfer_layout_edge` writes it: the input section object (`base`, its
index in the edge's first `sections` array) or a new `{"id": …}` object (the section's identifier
`ident`, else `<edge id>_s<index>`), with
`startPoint`, `endPoint`, `bendPoints` (when there are any), `incomingShape`/`outgoingShape` (when
the shape has a JSON id) and `incomingSections`/`outgoingSections` (when the section has any) set
in this order. -/
structure SectionOut where
  base : Option Nat
  ident : Option String
  index : Nat
  sx : Float
  sy : Float
  ex : Float
  ey : Float
  /-- Bend points as `x₀, y₀, x₁, y₁, …`. -/
  bends : FloatArray
  inShape : Option JsonId
  outShape : Option JsonId
  inSecs : Option (Array JsonId)
  outSecs : Option (Array JsonId)

instance : Inhabited SectionOut :=
  ⟨{ base := none, ident := none, index := 0, sx := 0, sy := 0, ex := 0, ey := 0, bends := .empty, inShape := none,
     outShape := none, inSecs := none, outSecs := none }⟩

/-- The id of a new section object: the section's identifier, else `<edgeId>_s<index>`. -/
def SectionOut.fallbackId (so : SectionOut) (edgeId : String) : String :=
  so.ident.getD s!"{edgeId}_s{so.index}"

/-- The writes of `transfer_layout_edge` into an edge object, in this order: `sections` (the first
member removed, then set; only when `sections` is not empty), `junctionPoints` (`x₀, y₀, …`) and
`container`. `edgeId` is the edge's JSON id as a string (`""` without one). -/
structure EdgeOut where
  edgeId : String
  sections : Array SectionOut
  junction : Option FloatArray
  container : Option String
  deriving Inhabited

/-- The results of `transferLayoutOverlay`. Shapes use the dense index of `TransferTables` (nodes,
then ports, then labels); `done` marks the transferred ones. -/
structure Overlay where
  sx : FloatArray
  sy : FloatArray
  sw : FloatArray
  sh : FloatArray
  done : ByteArray
  edges : Array (Option EdgeOut)
  /-- Cleared when the overlay cannot reproduce `transferLayout` (see the module doc). -/
  ok : Bool

instance : Inhabited Overlay := ⟨⟨.empty, .empty, .empty, .empty, .empty, #[], false⟩⟩

namespace Overlay

/-- An empty overlay for `shapes` shapes and `edges` edges. -/
def create (shapes edges : Nat) : Overlay :=
  let z : FloatArray := ⟨Array.replicate shapes 0.0⟩
  ⟨z, z, z, z, ⟨Array.replicate shapes 0⟩, Array.replicate edges none, true⟩

/-- `transfer_xywh_to_json` of the shape with dense index `i`. (Constructor-match updates keep the
tables in place, PLAN §7.1 item 13.) -/
@[inline] def setShape (o : Overlay) (i : Nat) (x y w h : Float) : Overlay :=
  match o with
  | ⟨sx, sy, sw, sh, done, edges, ok⟩ => ⟨sx.set! i x, sy.set! i y, sw.set! i w, sh.set! i h, done.set! i 1, edges, ok⟩

/-- Sets `x` of shape `i`. -/
@[inline] def setX (o : Overlay) (i : Nat) (v : Float) : Overlay :=
  match o with
  | ⟨sx, sy, sw, sh, done, edges, ok⟩ => ⟨sx.set! i v, sy, sw, sh, done, edges, ok⟩

/-- Sets `y` of shape `i`. -/
@[inline] def setY (o : Overlay) (i : Nat) (v : Float) : Overlay :=
  match o with
  | ⟨sx, sy, sw, sh, done, edges, ok⟩ => ⟨sx, sy.set! i v, sw, sh, done, edges, ok⟩

/-- Sets `width` of shape `i`. -/
@[inline] def setW (o : Overlay) (i : Nat) (v : Float) : Overlay :=
  match o with
  | ⟨sx, sy, sw, sh, done, edges, ok⟩ => ⟨sx, sy, sw.set! i v, sh, done, edges, ok⟩

/-- Sets `height` of shape `i`. -/
@[inline] def setH (o : Overlay) (i : Nat) (v : Float) : Overlay :=
  match o with
  | ⟨sx, sy, sw, sh, done, edges, ok⟩ => ⟨sx, sy, sw, sh.set! i v, done, edges, ok⟩

/-- Records the writes into edge `i`. -/
@[inline] def setEdge (o : Overlay) (i : Nat) (e : EdgeOut) : Overlay :=
  match o with
  | ⟨sx, sy, sw, sh, done, edges, ok⟩ => ⟨sx, sy, sw, sh, done, edges.set! i (some e), ok⟩

/-- Clears `ok`. -/
@[inline] def markBad (o : Overlay) : Overlay :=
  match o with
  | ⟨sx, sy, sw, sh, done, edges, _⟩ => ⟨sx, sy, sw, sh, done, edges, false⟩

/-- Whether shape `i` was transferred. -/
@[inline] def isDone (o : Overlay) (i : Nat) : Bool := o.done.get! i == 1

end Overlay

/-- The overlay transfer: the overlay over the importer monad. -/
abbrev OverlayM := StateRefT Overlay ImportM

namespace JsonImporter

@[inline] private def modO (f : Overlay → Overlay) : OverlayM Unit := modifyThe Overlay f

/-! A double that `transferLayout` reads back from the document after writing it
(`Value.ofFloatElk`, then `getFloat?`) is the double itself (see `nodeCompaction`). -/

/-- `transferXywh` into the overlay: the coordinates adjusted to the parent's coordinate mode (the
same operations in the same order; shape parents on one read of the tables). -/
private def overlayXywh (i : Nat) (x y w h : Float) (parent : Option ElementId) : OverlayM Unit := do
  match parent with
  | some (.edge e) =>
    let ax ← adjustEdgeX e x
    let ay ← adjustEdgeY e y
    modO (·.setShape i ax ay w h)
  | some p =>
    let t := (← getI).tables
    let root := match t.shapeCoords.getD (t.index p) .parent with
      | .root => true
      | _ => false
    let ax := if root then x + tableGX t p else x
    let ay := if root then y + tableGY t p else y
    modO (·.setShape i ax ay w h)
  | none => modO (·.setShape i x y w h)

/-- `transferLayoutNode` into the overlay. -/
def overlayLayoutNode (n : NodeId) : OverlayM Unit := do
  let path := pathGet (← getI).nodePath n.idx
  if !pathExists (← getI).nodePath n.idx then throwJsonImport "Node did not exist in input."
  let g ← getG
  let node := g.node n
  -- the document is unchanged, and `transferLayout` reads only the options of this object (which
  -- it never writes); `nodeCompaction` does not look at them for a node without ports (and the path
  -- of an imported node always leads to its object)
  let jsonObj ← if node.ports.isEmpty then pure Value.null else objectAt path.segs
  let c := nodeCompaction jsonObj g node (← getI).rootIncludeChildrenHint
  let parent := node.parent.map ElementId.node
  recordShape (.node n) parent node.x node.y node.props
  let i := n.idx
  overlayXywh i node.x node.y node.width node.height parent
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
    modO (·.setW i FOUR)
  if c.vertical && nodeHeight > FOUR then
    let delta := nodeHeight - FOUR
    modI fun s => { s with compactedVerticalNodeYDelta := s.compactedVerticalNodeYDelta.insert n delta }
    if let some p := node.parent then
      modI fun s => { s with verticalCompactedParentKeys := s.verticalCompactedParentKeys.push p }
    modO (·.setH i FOUR)
  if c.fixedOrderPortLabels then
    if let some compensated ← recomputeFixedOrderVerticalPortSurroundingHeight n then
      let current := (← getThe Overlay).sh.get! i
      if compensated > current + EPS9 then
        modO (·.setH i compensated)

/-- `transferLayoutPort` into the overlay. -/
def overlayLayoutPort (p : PortId) : OverlayM Unit := do
  if !pathExists (← getI).portPath p.idx then throwJsonImport "Port did not exist in input."
  let port := (← getG).port p
  let parent := port.parent.map ElementId.node
  recordShape (.port p) parent port.x port.y port.props
  let i := (← getI).tables.portBase + p.idx
  overlayXywh i port.x port.y port.width port.height parent
  if let some parentNode := port.parent then
    let st ← getI
    let dx? := st.insideSelfLoopNodeXDelta.get? parentNode
    let dy? := st.compactedVerticalNodeYDelta.get? parentNode
    if dx?.isSome || dy?.isSome then
      let side := port.props.getD CoreOptions.PORT_SIDE .undefined
      if let some delta := dx? then
        if side == .east then
          let x := (← getThe Overlay).sx.get! i
          modO (·.setX i (x - delta))
          modI fun s => { s with shiftedEastPortXDelta := s.shiftedEastPortXDelta.insert p delta }
      if let some delta := dy? then
        if side == .south then
          let y := (← getThe Overlay).sy.get! i
          modO (·.setY i (y - delta))
          modI fun s => { s with shiftedSouthPortYDelta := s.shiftedSouthPortYDelta.insert p delta }

/-- The index `j` of a section path `child edgePath sections j`. -/
private def sectionIndexIn (edgePath sp : JPath) : Option Nat :=
  match sp with
  | .child p k j => if k == Key.sections && p == edgePath then some j else none
  | _ => none

/-- `transferLayoutEdge` into the overlay. -/
def overlayLayoutEdge (e : EdgeId) : OverlayM Unit := do
  let path := pathGet (← getI).edgePath e.idx
  if !pathExists (← getI).edgePath e.idx then throwJsonImport "Edge did not exist in input."
  let g ← getG
  let edge := g.edge e
  -- `recordCoordinateModes (.edge e)`: the JSON parent of an edge is its original parent
  let parent := (tableGet? (← getI).edgeOriginalParent e.idx).map ElementId.node
  let t := (← getI).tables
  let sm := resolveShapeMode t edge.props parent
  let em := resolveEdgeMode t edge.props parent
  let di := t.index (.edge e)
  modI (·.modifyTables (·.setModes di sm em))
  let st ← getI
  let adj ← edgeAdjust e
  let edgeId := ((tableGet? st.edgeIds e.idx).map (·.asString)).getD ""
  let isSelfLoop :=
    match edge.sources[0]?, edge.targets[0]? with
    | some s, some t => ElkGraphUtil.connectableShapeToNode g s == ElkGraphUtil.connectableShapeToNode g t
    | _, _ => false
  let mut sections : Array SectionOut := Array.emptyWithCapacity edge.sections.size
  for h : i in [0:edge.sections.size] do
    let sec := edge.sections[i]
    let s := g.edgeSection sec
    let base ← match pathGet st.sectionPath sec.idx with
      | .missing => pure none
      | sp =>
        match sectionIndexIn path sp with
        | some j => pure (some j)
        | none => modO Overlay.markBad; pure none
    let mut startX ← adj.adjX s.startX
    let mut startY ← adj.adjY s.startY
    let mut endX ← adj.adjX s.endX
    let mut endY ← adj.adjY s.endY
    if !isSelfLoop then
      if let some shape := s.incomingShape then
        startX := shiftedEastX st shape startX
        startY := shiftedSouthY st shape startY
      if let some shape := s.outgoingShape then
        endX := shiftedEastX st shape endX
        endY := shiftedSouthY st shape endY
    let mut bends : FloatArray := .emptyWithCapacity (2 * s.bendPoints.size)
    for b in s.bendPoints do
      let bx ← adj.adjX b.x
      let by_ ← adj.adjY b.y
      bends := (bends.push bx).push by_
    let inShape := s.incomingShape.bind (idByElement st)
    let outShape := s.outgoingShape.bind (idByElement st)
    let inSecs := if s.incomingSections.isEmpty then none
      else some (s.incomingSections.filterMap fun sid => tableGet? st.sectionIds sid.idx)
    let outSecs := if s.outgoingSections.isEmpty then none
      else some (s.outgoingSections.filterMap fun sid => tableGet? st.sectionIds sid.idx)
    sections := sections.push
      { base, ident := s.identifier, index := i, sx := startX, sy := startY, ex := endX, ey := endY, bends, inShape, outShape, inSecs, outSecs }
  let junctionPoints : Option KVectorChain :=
    if edge.props.has CoreOptions.JUNCTION_POINTS then edge.props.get CoreOptions.JUNCTION_POINTS else none
  let containerId ← match tableGet? st.edgeOriginalParent e.idx with
    | some orig =>
      if (← edgeCoordsMode (.node orig)) == .container then
        pure (edge.containingNode.bind fun c => (g.node c).identifier)
      else pure none
    | none => pure none
  let mut junction : Option FloatArray := none
  if let some jps := junctionPoints then
    if !jps.isEmpty then
      let mut arr : FloatArray := .emptyWithCapacity (2 * jps.size)
      for jp in jps do
        let jx ← adj.adjX jp.x
        let jy ← adj.adjY jp.y
        arr := (arr.push jx).push jy
      junction := some arr
  modO (·.setEdge e.idx { edgeId, sections, junction, container := containerId })
where
  /-- `adjustXForShiftedEastPort` on a state read once. -/
  shiftedEastX (st : ImporterState) (shape : ConnectableId) (x : Float) : Float :=
    match shape with
    | .port p => match st.shiftedEastPortXDelta.get? p with
      | some d => x - d
      | none => x
    | .node _ => x
  /-- `adjustYForShiftedSouthPort` on a state read once. -/
  shiftedSouthY (st : ImporterState) (shape : ConnectableId) (y : Float) : Float :=
    match shape with
    | .port p => match st.shiftedSouthPortYDelta.get? p with
      | some d => y - d
      | none => y
    | .node _ => y
  idByElement (st : ImporterState) : ConnectableId → Option JsonId
    | .node n => tableGet? st.nodeIds n.idx
    | .port p => tableGet? st.portIds p.idx

/-- `transferLayoutLabel` into the overlay. -/
def overlayLayoutLabel (l : LabelId) : OverlayM Unit := do
  if !pathExists (← getI).labelPath l.idx then throwJsonImport "Label did not exist in input."
  let label := (← getG).label l
  let parent := label.parent
  recordShape (.label l) parent label.x label.y label.props
  let i := (← getI).tables.labelBase + l.idx
  overlayXywh i label.x label.y label.width label.height parent

/-- `transferNodesAndPorts` into the overlay. -/
def overlayNodesAndPorts (root : NodeId) : OverlayM Unit := do
  let mut stack : Array NodeId := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    overlayLayoutNode n
    let node := (← getG).node n
    for p in node.ports do overlayLayoutPort p
    for c in node.children do stack := stack.push c

/-- `transferEdgesAndLabels` into the overlay. -/
def overlayEdgesAndLabels (root : NodeId) : OverlayM Unit := do
  let mut stack : Array NodeId := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    let g ← getG
    let node := g.node n
    for l in node.labels do overlayLayoutLabel l
    for p in node.ports do
      for l in (g.port p).labels do overlayLayoutLabel l
    for e in node.containedEdges do
      overlayLayoutEdge e
      for l in ((← getG).edge e).labels do overlayLayoutLabel l
    for c in node.children do stack := stack.push c

/-- `transferLayout` into an overlay (the document is not changed). Same errors, in the same order,
and the same importer state (coordinate tables, compaction records) as `transferLayout` before its
parent size corrections; `Overlay.ok` is false when the overlay does not reproduce it. -/
def transferLayoutOverlay : ImportM Overlay := do
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
  let ov := Overlay.create tables.edgeBase g.edges.size
  let ov := if st.index.regular then ov else ov.markBad
  modI fun s => { s with rootIncludeChildrenHint := hint, tables }
  let ((), ov) ← (do overlayNodesAndPorts root; overlayEdgesAndLabels root : OverlayM Unit).run ov
  let st ← getI
  -- `fixParentWidthsForCompactedPassthroughNodes` / `fixParentHeightsForCompactedVerticalNodes`
  let fixes := (!st.passthroughCompactedParentKeys.isEmpty || !st.verticalCompactedParentKeys.isEmpty)
    && !st.rootIncludeChildrenHint
  return if fixes then ov.markBad else ov

end JsonImporter

/-! ## The document with the overlay applied -/

namespace Overlay

/-- The placement and dense-index data the overlay is applied with. -/
structure Ctx where
  ix : ElemIndex
  ov : Overlay
  portBase : Nat
  labelBase : Nat

/-- The context of an importer state and its overlay. -/
def Ctx.ofState (st : ImporterState) (ov : Overlay) : Ctx :=
  { ix := st.index, ov, portBase := st.tables.portBase, labelBase := st.tables.labelBase }

/-- `{"x": x, "y": y}` (`pointObject` of the transfer). -/
def pointValue (x y : Float) : Value := .obj #[(Key.x, .ofFloatElk x), (Key.y, .ofFloatElk y)]

/-- Points `x₀, y₀, x₁, y₁, …` as an array of `pointValue`s. -/
def pointsValue (xs : FloatArray) : Value := Id.run do
  let mut out : Array Value := Array.emptyWithCapacity (xs.size / 2)
  let mut i := 0
  while i + 1 < xs.size do
    out := out.push (pointValue (xs.get! i) (xs.get! (i + 1)))
    i := i + 2
  return .arr out

/-- The section object of `transfer_layout_edge` (`input`: the edge's first `sections` member). -/
def sectionValue (edgeId : String) (input : Option Value) (so : SectionOut) : Value :=
  let base : Value := match so.base with
    | some j =>
      match input with
      | some (.arr xs) =>
        match xs[j]? with
        | some v@(.obj _) => v
        | _ => .obj #[]
      | _ => .obj #[]
    | none => .obj #[(Key.id, .str (so.fallbackId edgeId))]
  let obj := base.set Key.startPoint (pointValue so.sx so.sy)
  let obj := obj.set Key.endPoint (pointValue so.ex so.ey)
  let obj := if so.bends.size == 0 then obj else obj.set Key.bendPoints (pointsValue so.bends)
  let obj := match so.inShape with
    | some id => obj.set Key.incomingShape id.toValue
    | none => obj
  let obj := match so.outShape with
    | some id => obj.set Key.outgoingShape id.toValue
    | none => obj
  let obj := match so.inSecs with
    | some ids => obj.set Key.incomingSections (.arr (ids.map JsonId.toValue))
    | none => obj
  match so.outSecs with
  | some ids => obj.set Key.outgoingSections (.arr (ids.map JsonId.toValue))
  | none => obj

/-- `transferXywh` of shape `i` on an object's members. -/
@[inline] def applyXywh (ov : Overlay) (i : Nat) (kvs : Array (String × Value)) : Array (String × Value) :=
  if ov.isDone i then
    Value.setEntry (Value.setEntry (Value.setEntry (Value.setEntry kvs Key.x (.ofFloatElk (ov.sx.get! i)))
      Key.y (.ofFloatElk (ov.sy.get! i))) Key.width (.ofFloatElk (ov.sw.get! i))) Key.height (.ofFloatElk (ov.sh.get! i))
  else kvs

/-- `f` applied to the elements of the first member named `key` when it is an array (the array the
importer read). -/
@[inline] def modifyArrayMember (kvs : Array (String × Value)) (key : String) (f : Array Value → Array Value) :
    Array (String × Value) :=
  let j := Value.keyIndex kvs key
  if j < kvs.size then
    kvs.modifyIn j fun kv => match kv with
      | (k, .arr xs) => (k, .arr (f xs))
      | kv => kv
  else kvs

/-- `f id` on the objects of `xs` from `i` on, where the objects get consecutive ids from `id`. -/
@[specialize] partial def mapConsecutive (f : Nat → Value → Value) (xs : Array Value) (i id : Nat) : Array Value :=
  if h : i < xs.size then
    if xs[i].isObj then mapConsecutive f (xs.modifyIn i (f id)) (i + 1) (id + 1)
    else mapConsecutive f xs (i + 1) id
  else xs

/-- A label object with the overlay applied. -/
def matLabel (c : Ctx) (l : Nat) (v : Value) : Value :=
  match v with
  | .obj kvs => .obj (applyXywh c.ov (c.labelBase + l) kvs)
  | other => other

/-- A port object with the overlay applied. -/
def matPort (c : Ctx) (p : Nat) (v : Value) : Value :=
  match v with
  | .obj kvs =>
    let kvs := modifyArrayMember kvs Key.labels (mapConsecutive (matLabel c) · 0 (c.ix.portFirstLabel.getD p 0))
    .obj (applyXywh c.ov (c.portBase + p) kvs)
  | other => other

/-- An edge object with the overlay applied (`transfer_layout_edge`'s writes in their order). -/
def matEdge (c : Ctx) (e : Nat) (v : Value) : Value :=
  match v with
  | .obj kvs =>
    let kvs := modifyArrayMember kvs Key.labels (mapConsecutive (matLabel c) · 0 (c.ix.edgeFirstLabel.getD e 0))
    match c.ov.edges.getD e none with
    | none => .obj kvs
    | some eo =>
      let o : Value := .obj kvs
      let o := if eo.sections.isEmpty then o
        else
          let input := Value.lookup kvs Key.sections
          (o.remove Key.sections).set Key.sections (.arr (eo.sections.map (sectionValue eo.edgeId input)))
      let o := match eo.junction with
        | some j => o.set Key.junctionPoints (pointsValue j)
        | none => o
      match eo.container with
      | some cid => o.set Key.container (.str cid)
      | none => o
  | other => other

mutual

/-- A node object (node id `n`) and everything below it with the overlay applied. -/
partial def matNode (c : Ctx) (n : Nat) (v : Value) : Value :=
  match v with
  | .obj kvs =>
    let kvs := modifyArrayMember kvs Key.ports (mapConsecutive (matPort c) · 0 (c.ix.nodeFirstPort.getD n 0))
    let kvs := modifyArrayMember kvs Key.labels (mapConsecutive (matLabel c) · 0 (c.ix.nodeFirstLabel.getD n 0))
    let kvs := modifyArrayMember kvs Key.children (matChildren c · 0 (n + 1))
    let kvs := modifyArrayMember kvs Key.edges (mapConsecutive (matEdge c) · 0 (c.ix.nodeFirstEdge.getD n 0))
    .obj (applyXywh c.ov n kvs)
  | other => other

/-- The objects of a `children` array from `i` on, the next one being node `id` (preorder ids). -/
partial def matChildren (c : Ctx) (xs : Array Value) (i id : Nat) : Array Value :=
  if i < xs.size then
    if (xs.getD i .null).isObj then
      matChildren c (xs.modifyIn i (matNode c id)) (i + 1) (c.ix.nodeSubtreeEnd.getD id (id + 1))
    else matChildren c xs (i + 1) id
  else xs

end

/-- The document `transferLayout` would have written (the root object is node `0`). -/
def materialize (c : Ctx) (model : Value) : Value := matNode c 0 model

end Overlay

end Elk.Json
