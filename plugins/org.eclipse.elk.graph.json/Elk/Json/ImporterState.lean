import Std.Data.HashMap
import Std.Data.HashSet
import Elk.Json.Value
import Elk.Json.Printer
import Elk.Json.Parser
import Elk.Core
/-!
# JSON importer state (`org.eclipse.elk.graph.json.JsonImporter`, part 1)

Shared definitions of the importer: the `JsonId` type, the importer state
record, the `ImportM` monad (importer state on top of the ElkGraph arena
state), JSON access helpers (`JsonAdapter`) and `GlobalOptions`
(elk-rs `layout_api::GlobalOptions`, the per-call option defaults).
-/
namespace Elk.Json

open Elk Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Options Elk.Core.Data

/-- `JsonImportException`. -/
def jsonImportExceptionClass : String := "org.eclipse.elk.graph.json.JsonImportException"

def throwJsonImport {m : Type → Type} [MonadExcept IO.Error m] {α : Type} (msg : String) : m α :=
  throw (javaException jsonImportExceptionClass msg)

/-- Element id as written in JSON: a string or an integral number. -/
inductive JsonId where
  | str (s : String)
  | int (i : Int)
  deriving BEq, Hashable, Repr, Inhabited

namespace JsonId
def asString : JsonId → String
  | .str s => s
  | .int i => toString i
def toValue : JsonId → Value
  | .str s => .str s
  | .int i => .num (.int i)
end JsonId

/-- JSON path (replaces elk-rs JSON pointers). -/
abbrev JsonPath := Array Seg

/-- Where the importer found an element object, as a parent link: `child parent key i` is element
`i` of the (first) member `key` of the object at `parent`. One object per element (a `JsonPath`
would copy its parent's segments); `missing` for elements that do not come from the document. -/
inductive JPath where
  | missing
  | root
  | child (parent : JPath) (key : String) (idx : Nat)
  deriving Inhabited, BEq

namespace JPath

/-- The segments from the root. -/
def segs : JPath → JsonPath
  | .missing | .root => #[]
  | .child p k i => ((segs p).push (.key k)).push (.idx i)

/-- The segments, `none` for `missing`. -/
def segs? : JPath → Option JsonPath
  | .missing => none
  | p => some p.segs

end JPath

/-- Entry `i` of a path table (`missing` past its end). -/
@[inline] def pathGet (t : Array JPath) (i : Nat) : JPath := t.getD i .missing

/-- Whether element `i` has a path (it was imported from a JSON object). -/
@[inline] def pathExists (t : Array JPath) (i : Nat) : Bool :=
  match pathGet t i with
  | .missing => false
  | _ => true

/-- Stores `v` at index `i` of a path table, growing it with `missing`. -/
def pathSet (t : Array JPath) (i : Nat) (v : JPath) : Array JPath :=
  if i < t.size then t.set! i v
  else if i == t.size then t.push v
  else (t ++ Array.replicate (i - t.size) JPath.missing).push v

/-- Per-call option defaults (`GlobalOptions`): the first spelling of every
canonical option id wins; canonical lookups are cached. -/
structure GlobalOptions where
  values : Array (String × Value) := #[]
  canonicalIds : Std.HashMap String String := {}

/-- Value of a table indexed by element ids (`none` for ids without an entry). -/
@[inline] def tableGet? {α : Type} (t : Array (Option α)) (i : Nat) : Option α := (t[i]?).join

/-- Stores `v` at index `i` of a table indexed by element ids, growing it with `none`. -/
def tableSet {α : Type} (t : Array (Option α)) (i : Nat) (v : α) : Array (Option α) :=
  if i < t.size then t.set! i (some v)
  -- elements are created densely: the next id is usually the table size
  else if i == t.size then t.push (some v)
  else (t ++ Array.replicate (i - t.size) none).push (some v)

/-- `tableSet` when `v` is present; the table is unchanged otherwise. -/
@[noinline] def tableSetOpt {α : Type} (t : Array (Option α)) (i : Nat) : Option α → Array (Option α)
  | some v => tableSet t i v
  | none => t

/-- Per-element results of `transferLayout` in one dense index space: nodes first, then ports,
labels and edges (`ElementId` → `base + id`). Absent entries hold the hash-map defaults of the
former representation (`0` for global coordinates, `PARENT`/`CONTAINER` for the modes). -/
structure TransferTables where
  portBase : Nat := 0
  labelBase : Nat := 0
  edgeBase : Nat := 0
  size : Nat := 0
  globalX : FloatArray := .empty
  globalY : FloatArray := .empty
  shapeCoords : Array ShapeCoords := #[]
  edgeCoords : Array EdgeCoords := #[]

namespace TransferTables

/-- Tables for a graph with the given element counts. -/
def create (nodes ports labels edges : Nat) : TransferTables :=
  let size := nodes + ports + labels + edges
  { portBase := nodes, labelBase := nodes + ports, edgeBase := nodes + ports + labels, size,
    globalX := ⟨Array.replicate size 0.0⟩, globalY := ⟨Array.replicate size 0.0⟩,
    shapeCoords := Array.replicate size .parent, edgeCoords := Array.replicate size .container }

/-- Dense index of an element. -/
@[inline] def index (t : TransferTables) : ElementId → Nat
  | .node n => n.idx
  | .port p => t.portBase + p.idx
  | .label l => t.labelBase + l.idx
  | .edge e => t.edgeBase + e.idx

/-- Records the coordinate modes of the element with dense index `i`. (Branch-free and written as a
constructor match, so the update reuses the table object.) -/
@[inline] def setModes (t : TransferTables) (i : Nat) (sm : ShapeCoords) (em : EdgeCoords) : TransferTables :=
  match t with
  | ⟨portBase, labelBase, edgeBase, size, globalX, globalY, shapeCoords, edgeCoords⟩ =>
    ⟨portBase, labelBase, edgeBase, size, globalX, globalY, shapeCoords.set! i sm, edgeCoords.set! i em⟩

/-- Records the global coordinates and the coordinate modes of the shape with dense index `i`. -/
@[inline] def setShape (t : TransferTables) (i : Nat) (gx gy : Float) (sm : ShapeCoords) (em : EdgeCoords) :
    TransferTables :=
  match t with
  | ⟨portBase, labelBase, edgeBase, size, globalX, globalY, shapeCoords, edgeCoords⟩ =>
    ⟨portBase, labelBase, edgeBase, size, globalX.set! i gx, globalY.set! i gy, shapeCoords.set! i sm,
      edgeCoords.set! i em⟩

end TransferTables

/-- Where the importer created the elements of each JSON element object, for the overlay transfer
(`Elk.Json.TransferOverlay`): an element's `ports`, `labels` and `edges` arrays become elements with
consecutive ids (the object entries in array order), and node ids are the preorder of the `children`
objects. Indexed by element id; `regular` is cleared when an element was not created in id order or
two nodes share a JSON id (edges are then attached through the id map to another node's object). -/
structure ElemIndex where
  /-- Port id of the first object of a node's `ports` array. -/
  nodeFirstPort : Array Nat := #[]
  /-- Label id of the first object of a node's `labels` array. -/
  nodeFirstLabel : Array Nat := #[]
  /-- Edge id of the first object of a node's `edges` array. -/
  nodeFirstEdge : Array Nat := #[]
  /-- One past the last node id of a node's subtree (`children`, recursively). -/
  nodeSubtreeEnd : Array Nat := #[]
  /-- Label id of the first object of a port's `labels` array. -/
  portFirstLabel : Array Nat := #[]
  /-- Label id of the first object of an edge's `labels` array. -/
  edgeFirstLabel : Array Nat := #[]
  regular : Bool := true

namespace ElemIndex

/-- Stores `v` at `i` of an index table that is filled in id order (`regular` cleared otherwise). -/
@[inline] private def put (t : Array Nat) (i v : Nat) (regular : Bool) : Array Nat × Bool :=
  if i == t.size then (t.push v, regular)
  else if i < t.size then (t.set! i v, regular)
  else (t, false)

/-- Records `nodeFirstPort` (when node `n` is created). -/
def setNodeFirstPort (x : ElemIndex) (n v : Nat) : ElemIndex :=
  match x with
  | ⟨a, b, c, d, e, f, r⟩ =>
    let (a, r) := put a n v r
    let (d, r) := put d n 0 r
    ⟨a, b, c, d, e, f, r⟩

/-- Records `nodeFirstLabel`. -/
def setNodeFirstLabel (x : ElemIndex) (n v : Nat) : ElemIndex :=
  match x with
  | ⟨a, b, c, d, e, f, r⟩ => let (b, r) := put b n v r; ⟨a, b, c, d, e, f, r⟩

/-- Records `nodeFirstEdge`. -/
def setNodeFirstEdge (x : ElemIndex) (n v : Nat) : ElemIndex :=
  match x with
  | ⟨a, b, c, d, e, f, r⟩ =>
    -- `transformEdges` visits the nodes in creation order, so the table is filled in order
    let (c, r) := put c n v r
    ⟨a, b, c, d, e, f, r⟩

/-- Records `nodeSubtreeEnd` (after the children of node `n`). -/
def setNodeSubtreeEnd (x : ElemIndex) (n v : Nat) : ElemIndex :=
  match x with
  | ⟨a, b, c, d, e, f, r⟩ => let (d, r) := put d n v r; ⟨a, b, c, d, e, f, r⟩

/-- Records `portFirstLabel`. -/
def setPortFirstLabel (x : ElemIndex) (p v : Nat) : ElemIndex :=
  match x with
  | ⟨a, b, c, d, e, f, r⟩ => let (e, r) := put e p v r; ⟨a, b, c, d, e, f, r⟩

/-- Records `edgeFirstLabel`. -/
def setEdgeFirstLabel (x : ElemIndex) (ed v : Nat) : ElemIndex :=
  match x with
  | ⟨a, b, c, d, e, f, r⟩ => let (f, r) := put f ed v r; ⟨a, b, c, d, e, f, r⟩

/-- Clears `regular`. -/
def markIrregular (x : ElemIndex) : ElemIndex :=
  match x with
  | ⟨a, b, c, d, e, f, _⟩ => ⟨a, b, c, d, e, f, false⟩

end ElemIndex

/-- Importer scratch state (one import + one transfer). Element-keyed tables are arrays indexed by
the element id (the importer creates the elements densely). -/
structure ImporterState where
  model : Value := .null
  defaults : Option GlobalOptions := none
  optionCache : Std.HashMap String (Option LayoutOptionData) := {}
  nodeIdMap : Std.HashMap JsonId NodeId := {}
  portIdMap : Std.HashMap JsonId PortId := {}
  edgeIdMap : Std.HashMap JsonId EdgeId := {}
  sectionIdMap : Std.HashMap JsonId SectionId := {}
  nodePath : Array JPath := #[]
  portPath : Array JPath := #[]
  edgePath : Array JPath := #[]
  sectionPath : Array JPath := #[]
  labelPath : Array JPath := #[]
  nodeIds : Array (Option JsonId) := #[]
  portIds : Array (Option JsonId) := #[]
  edgeIds : Array (Option JsonId) := #[]
  sectionIds : Array (Option JsonId) := #[]
  edgeOriginalParent : Array (Option NodeId) := #[]
  tables : TransferTables := {}
  insideSelfLoopNodeXDelta : Std.HashMap NodeId Float := {}
  shiftedEastPortXDelta : Std.HashMap PortId Float := {}
  compactedVerticalNodeYDelta : Std.HashMap NodeId Float := {}
  shiftedSouthPortYDelta : Std.HashMap PortId Float := {}
  passthroughCompactedParentKeys : Array NodeId := #[]
  verticalCompactedParentKeys : Array NodeId := #[]
  rootIncludeChildrenHint : Bool := false
  rootNode : Option NodeId := none
  /-- Values of ENUM/ENUMSET options parsed during this import: `(option id, value string, value)`
  (the option parsers are pure, so equal inputs give equal values; see `JsonImporter.setOption`). -/
  enumMemo : Array (String × String × PropValue) := #[]
  /-- Element placement in the JSON document (`ElemIndex`). -/
  index : ElemIndex := {}

instance : Inhabited ImporterState := ⟨{}⟩

namespace ImporterState

/-! Updates of single fields written as a constructor match: the compiler reuses the state
object (a `{ s with … }` update projects the fields and allocates a new 28-field object). -/

/-- Applies `f` to `model`. -/
@[inline] def modifyModel (s : ImporterState) (f : Value → Value) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩ =>
    ⟨(f model), defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩

/-- Applies `f` to `tables`. -/
@[inline] def modifyTables (s : ImporterState) (f : TransferTables → TransferTables) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩ =>
    ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, (f tables), insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩

/-- `registerNode`: id map, JSON id and path of a node. -/
@[inline] def addNode (s : ImporterState) (id : JsonId) (n : NodeId) (path : JPath) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩ =>
    ⟨model, defaults, optionCache, (nodeIdMap.insert id n), portIdMap, edgeIdMap, sectionIdMap, (pathSet nodePath n.idx path), portPath, edgePath, sectionPath, labelPath, (tableSet nodeIds n.idx id), portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩

/-- `registerPort`: id map, JSON id and path of a port. -/
@[inline] def addPort (s : ImporterState) (id : JsonId) (p : PortId) (path : JPath) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩ =>
    ⟨model, defaults, optionCache, nodeIdMap, (portIdMap.insert id p), edgeIdMap, sectionIdMap, nodePath, (pathSet portPath p.idx path), edgePath, sectionPath, labelPath, nodeIds, (tableSet portIds p.idx id), edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩

/-- `registerEdge`: id map, JSON id, path and original parent of an edge. -/
@[inline] def addEdge (s : ImporterState) (id : JsonId) (e : EdgeId) (path : JPath) (containing : Option NodeId) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩ =>
    ⟨model, defaults, optionCache, nodeIdMap, portIdMap, (edgeIdMap.insert id e), sectionIdMap, nodePath, portPath, (pathSet edgePath e.idx path), sectionPath, labelPath, nodeIds, portIds, (tableSet edgeIds e.idx id), sectionIds, (tableSetOpt edgeOriginalParent e.idx containing), tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩

/-- `registerSection`: id map, JSON id and path of a section. -/
@[inline] def addSection (s : ImporterState) (id : JsonId) (sec : SectionId) (path : JPath) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩ =>
    ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, (sectionIdMap.insert id sec), nodePath, portPath, edgePath, (pathSet sectionPath sec.idx path), labelPath, nodeIds, portIds, edgeIds, (tableSet sectionIds sec.idx id), edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩

/-- Path of a label. -/
@[inline] def addLabelPath (s : ImporterState) (l : LabelId) (path : JPath) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩ =>
    ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, (pathSet labelPath l.idx path), nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩

/-- Records a parsed ENUM/ENUMSET option value (`enumMemo`). -/
@[inline] def pushEnumMemo (s : ImporterState) (entry : String × String × PropValue) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩ =>
    ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, (enumMemo.push entry), index⟩

/-- Stores the (cache-updated) per-call defaults. -/
@[inline] def setDefaults (s : ImporterState) (g : GlobalOptions) : ImporterState :=
  match s with
  | ⟨model, _defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩ =>
    ⟨model, (some g), optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩

/-- Applies `f` to `index`. -/
@[inline] def modifyIndex (s : ImporterState) (f : ElemIndex → ElemIndex) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, index⟩ =>
    ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo, (f index)⟩

end ImporterState


/-- Importer monad: importer state over the ElkGraph arena state. -/
abbrev ImportM := StateRefT ImporterState ElkM

namespace ImportM
@[inline] def getI : ImportM ImporterState := getThe ImporterState
@[inline] def modI (f : ImporterState → ImporterState) : ImportM Unit := modifyThe ImporterState f
@[inline] def getG : ImportM ElkGraph := getThe ElkGraph
@[inline] def modG (f : ElkGraph → ElkGraph) : ImportM Unit := modifyThe ElkGraph f
/-- Runs an importer computation with a fresh state on top of `ElkM`. -/
@[inline] def run {α : Type} (x : ImportM α) (st : ImporterState := {}) : ElkM (α × ImporterState) :=
  StateRefT'.run x st
end ImportM

/-! `JsonAdapter`: typed access to JSON members with ELK's error messages. -/
namespace JsonAdapter

/-- `asId`: strings and integral numbers. -/
def asId (v : Value) : ImportM JsonId := do
  match v with
  | .str s => return .str s
  | .num n =>
    match n.toInt? with
    | some i => return .int i
    | none => throwJsonImport s!"Id must be a string or an integer: '{v.render}'."
  | _ => throwJsonImport s!"Id must be a string or an integer: '{v.render}'."

/-- `getId`: the mandatory `id` member. -/
@[inline] def getId (obj : Value) : ImportM JsonId := do
  match obj.get? Key.id with
  | some v => asId v
  | none => throwJsonImport "Every element must have an id."

/-- `stringVal`: primitive values as strings (numbers in Rust `Display` form). -/
@[inline] def stringVal (v : Value) : ImportM String := do
  match v with
  | .str s => return s
  | .num n => return n.toRustString
  | .bool b => return if b then "true" else "false"
  | .null => return "null"
  | _ => throwJsonImport "Expected a primitive JSON value."

@[inline] def optString (obj : Value) (key : String) : ImportM (Option String) := do
  match obj.get? key with
  | some v => return some (← stringVal v)
  | none => return none

/-- `idSave`: the `id` member as a string, if present. -/
@[inline] def idSave (obj : Value) : ImportM (Option String) := optString obj Key.id

/-- `optDouble`: numbers, numeric strings; `null` counts as absent. -/
@[inline] def optDouble (obj : Value) (key : String) : ImportM (Option Float) := do
  match obj.get? key with
  | some (.num n) => return some n.toFloat
  | some (.str s) =>
    match parseFloat? s with
    | some f => return some f
    | none => throwJsonImport "Invalid number value."
  | some .null => return none
  | some _ => throwJsonImport "Invalid number value."
  | none => return none

@[inline] def optArray (obj : Value) (key : String) : Option (Array Value) := (obj.get? key).bind (·.getArr?)

@[inline] def optObject (obj : Value) (key : String) : Option Value :=
  match obj.get? key with
  | some v@(.obj _) => some v
  | _ => none

@[inline] def hasKey (obj : Value) (key : String) : Bool := obj.hasKey key

/-! The accessors above for an ELK member name `key` with bit `b`, given the member mask
`m = obj.keyMaskOf` (`Value.getK`): an absent member is answered from the mask, a present one is
looked up as before (first occurrence), so results and errors are those of the plain accessors. -/

/-- `getId` (`m`: member mask of `obj`). -/
@[inline] def getIdK (obj : Value) (m : UInt64) : ImportM JsonId :=
  if m &&& Key.bId == 0 then throwJsonImport "Every element must have an id." else getId obj

/-- `optString` of a member name (`m`: member mask of `obj`, `b`: bit of `key`). -/
@[inline] def optStringK (obj : Value) (m b : UInt64) (key : String) : ImportM (Option String) :=
  if m &&& b == 0 then pure none else optString obj key

/-- `idSave` (`m`: member mask of `obj`). -/
@[inline] def idSaveK (obj : Value) (m : UInt64) : ImportM (Option String) := optStringK obj m Key.bId Key.id

/-- `optDouble` of a member name (`m`: member mask of `obj`, `b`: bit of `key`). -/
@[inline] def optDoubleK (obj : Value) (m b : UInt64) (key : String) : ImportM (Option Float) :=
  if m &&& b == 0 then pure none else optDouble obj key

/-- `optArray` of a member name (`m`: member mask of `obj`, `b`: bit of `key`). -/
@[inline] def optArrayK (obj : Value) (m b : UInt64) (key : String) : Option (Array Value) :=
  if m &&& b == 0 then none else optArray obj key

/-- `optObject` of a member name (`m`: member mask of `obj`, `b`: bit of `key`). -/
@[inline] def optObjectK (obj : Value) (m b : UInt64) (key : String) : Option Value :=
  if m &&& b == 0 then none else optObject obj key

/-- `hasKey` of a member name (`m`: member mask of `obj`, `b`: bit of `key`): the mask alone decides. -/
@[inline] def hasKeyK (m b : UInt64) : Bool := m &&& b != 0

end JsonAdapter

/-- `double_value_valid`: non-finite coordinates become `0`. -/
def doubleValueValid : Option Float → Float
  | some v => if v.isFinite then v else 0.0
  | none => 0.0

namespace GlobalOptions

/-- Canonical option id for a key (full id, legacy id or unique suffix), cached. -/
def canonicalId (g : GlobalOptions) (key : String) : IO (String × GlobalOptions) := do
  match g.canonicalIds.get? key with
  | some c => return (c, g)
  | none =>
    let c := match ← LayoutMetaDataService.getOptionDataBySuffix key with
      | some d => d.id
      | none => key
    return (c, { g with canonicalIds := g.canonicalIds.insert key c })

/-- `GlobalOptions::parse`: parses the options JSON object; later spellings of
an already seen canonical id are dropped. -/
def parse (optionsJson : String) : IO (Except String GlobalOptions) := do
  if optionsJson.isEmpty then return .ok {}
  match Elk.Json.parse optionsJson with
  | .error e => return .error s!"Failed to parse options JSON: {e}"
  | .ok (.obj kvs) =>
    let mut g : GlobalOptions := {}
    let mut seen : Std.HashSet String := {}
    for (k, v) in kvs do
      let (c, g') ← g.canonicalId k
      g := g'
      if !seen.contains c then
        seen := seen.insert c
        g := { g with values := g.values.push (k, v) }
    return .ok g
  | .ok _ => return .ok {}

/-- Keys of an authored options object plus the global keys whose canonical
id is not authored, in the (sorted, like serde's `Map`) order elk-rs visits
them, each paired with the effective value. -/
def effectiveOptions (g : GlobalOptions) (element : Value) : IO (Array (String × Value) × GlobalOptions) := do
  let selected := match element.get? Key.layoutOptions with
    | some v => some v
    | none => element.get? Key.properties
  let authoredObj : Option (Array (String × Value)) :=
    match (element.get? Key.layoutOptions).bind (·.getObj?) with
    | some o => some o
    | none => (element.get? Key.properties).bind (·.getObj?)
  if g.values.isEmpty || (selected.any fun v => !v.isObj) then
    return (authoredObj.getD #[], g)
  let authored := selected.bind (·.getObj?)
  let mut g := g
  let mut existing : Std.HashSet String := {}
  let mut keys : Array String := #[]
  let mut keySet : Std.HashSet String := {}
  if let some a := authored then
    for (k, _) in a do
      let (c, g') ← g.canonicalId k
      g := g'
      existing := existing.insert c
      if !keySet.contains k then
        keySet := keySet.insert k
        keys := keys.push k
  for (k, _) in g.values do
    let (c, g') ← g.canonicalId k
    g := g'
    if !existing.contains c && !keySet.contains k then
      keySet := keySet.insert k
      keys := keys.push k
  let sorted := stableSort keys (fun a b => compare a b)
  let mut out : Array (String × Value) := #[]
  for k in sorted do
    let v := match authored.bind (fun a => (a.find? (·.1 == k)).map (·.2)) with
      | some v => v
      | none => ((g.values.find? (·.1 == k)).map (·.2)).getD .null
    out := out.push (k, v)
  return (out, g)

/-- `materialize`: writes the defaults into every element's `layoutOptions`
(or `properties`) object unless the canonical id is already authored. -/
partial def materialize (g : GlobalOptions) (root : Value) : IO Value := do
  if g.values.isEmpty then return root
  let mut g := g
  let mut resolved : Array (String × Value × String) := #[]
  for (k, v) in g.values do
    let (c, g') ← g.canonicalId k
    g := g'
    resolved := resolved.push (k, v, c)
  let rec apply (gg : GlobalOptions) (element : Value) : IO (Value × GlobalOptions) := do
    match element with
    | .obj _ =>
      let field := if element.hasKey Key.layoutOptions then Key.layoutOptions
        else if element.hasKey Key.properties then Key.properties else Key.layoutOptions
      let mut gg := gg
      let mut existing : Std.HashSet String := {}
      if let some (.obj kvs) := element.get? field then
        for (k, _) in kvs do
          let (c, g') ← gg.canonicalId k
          gg := g'
          existing := existing.insert c
      let mut element := element.modifyKey field (.obj #[]) fun lo =>
        resolved.foldl (fun lo (k, v, c) => if existing.contains c then lo else lo.set k v) lo
      for arrKey in #[Key.children, Key.edges, Key.ports, Key.labels] do
        if let some (.arr items) := element.get? arrKey then
          let mut items' : Array Value := #[]
          for item in items do
            let (item', g') ← apply gg item
            gg := g'
            items' := items'.push item'
          element := element.set arrKey (.arr items')
      return (element, gg)
    | other => return (other, gg)
  return (← apply g root).1

end GlobalOptions

end Elk.Json
