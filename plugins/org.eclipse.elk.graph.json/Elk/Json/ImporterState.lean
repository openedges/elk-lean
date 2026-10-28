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
  nodePath : Array (Option JsonPath) := #[]
  portPath : Array (Option JsonPath) := #[]
  edgePath : Array (Option JsonPath) := #[]
  sectionPath : Array (Option JsonPath) := #[]
  labelPath : Array (Option JsonPath) := #[]
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

instance : Inhabited ImporterState := ⟨{}⟩

namespace ImporterState

/-! Updates of single fields written as a constructor match: the compiler reuses the state
object (a `{ s with … }` update projects the fields and allocates a new 27-field object). -/

/-- Applies `f` to `model`. -/
@[inline] def modifyModel (s : ImporterState) (f : Value → Value) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩ =>
    ⟨(f model), defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩

/-- Applies `f` to `tables`. -/
@[inline] def modifyTables (s : ImporterState) (f : TransferTables → TransferTables) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩ =>
    ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, (f tables), insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩

/-- `registerNode`: id map, JSON id and path of a node. -/
@[inline] def addNode (s : ImporterState) (id : JsonId) (n : NodeId) (path : JsonPath) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩ =>
    ⟨model, defaults, optionCache, (nodeIdMap.insert id n), portIdMap, edgeIdMap, sectionIdMap, (tableSet nodePath n.idx path), portPath, edgePath, sectionPath, labelPath, (tableSet nodeIds n.idx id), portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩

/-- `registerPort`: id map, JSON id and path of a port. -/
@[inline] def addPort (s : ImporterState) (id : JsonId) (p : PortId) (path : JsonPath) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩ =>
    ⟨model, defaults, optionCache, nodeIdMap, (portIdMap.insert id p), edgeIdMap, sectionIdMap, nodePath, (tableSet portPath p.idx path), edgePath, sectionPath, labelPath, nodeIds, (tableSet portIds p.idx id), edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩

/-- `registerEdge`: id map, JSON id, path and original parent of an edge. -/
@[inline] def addEdge (s : ImporterState) (id : JsonId) (e : EdgeId) (path : JsonPath) (containing : Option NodeId) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩ =>
    ⟨model, defaults, optionCache, nodeIdMap, portIdMap, (edgeIdMap.insert id e), sectionIdMap, nodePath, portPath, (tableSet edgePath e.idx path), sectionPath, labelPath, nodeIds, portIds, (tableSet edgeIds e.idx id), sectionIds, (tableSetOpt edgeOriginalParent e.idx containing), tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩

/-- `registerSection`: id map, JSON id and path of a section. -/
@[inline] def addSection (s : ImporterState) (id : JsonId) (sec : SectionId) (path : JsonPath) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩ =>
    ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, (sectionIdMap.insert id sec), nodePath, portPath, edgePath, (tableSet sectionPath sec.idx path), labelPath, nodeIds, portIds, edgeIds, (tableSet sectionIds sec.idx id), edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩

/-- Path of a label. -/
@[inline] def addLabelPath (s : ImporterState) (l : LabelId) (path : JsonPath) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩ =>
    ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, (tableSet labelPath l.idx path), nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩

/-- Records a parsed ENUM/ENUMSET option value (`enumMemo`). -/
@[inline] def pushEnumMemo (s : ImporterState) (entry : String × String × PropValue) : ImporterState :=
  match s with
  | ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩ =>
    ⟨model, defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, (enumMemo.push entry)⟩

/-- Stores the (cache-updated) per-call defaults. -/
@[inline] def setDefaults (s : ImporterState) (g : GlobalOptions) : ImporterState :=
  match s with
  | ⟨model, _defaults, optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩ =>
    ⟨model, (some g), optionCache, nodeIdMap, portIdMap, edgeIdMap, sectionIdMap, nodePath, portPath, edgePath, sectionPath, labelPath, nodeIds, portIds, edgeIds, sectionIds, edgeOriginalParent, tables, insideSelfLoopNodeXDelta, shiftedEastPortXDelta, compactedVerticalNodeYDelta, shiftedSouthPortYDelta, passthroughCompactedParentKeys, verticalCompactedParentKeys, rootIncludeChildrenHint, rootNode, enumMemo⟩

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
def getId (obj : Value) : ImportM JsonId := do
  match obj.get? Key.id with
  | some v => asId v
  | none => throwJsonImport "Every element must have an id."

/-- `stringVal`: primitive values as strings (numbers in Rust `Display` form). -/
def stringVal (v : Value) : ImportM String := do
  match v with
  | .str s => return s
  | .num n => return n.toRustString
  | .bool b => return if b then "true" else "false"
  | .null => return "null"
  | _ => throwJsonImport "Expected a primitive JSON value."

def optString (obj : Value) (key : String) : ImportM (Option String) := do
  match obj.get? key with
  | some v => return some (← stringVal v)
  | none => return none

/-- `idSave`: the `id` member as a string, if present. -/
def idSave (obj : Value) : ImportM (Option String) := optString obj Key.id

/-- `optDouble`: numbers, numeric strings; `null` counts as absent. -/
def optDouble (obj : Value) (key : String) : ImportM (Option Float) := do
  match obj.get? key with
  | some (.num n) => return some n.toFloat
  | some (.str s) =>
    match parseFloat? s with
    | some f => return some f
    | none => throwJsonImport "Invalid number value."
  | some .null => return none
  | some _ => throwJsonImport "Invalid number value."
  | none => return none

def optArray (obj : Value) (key : String) : Option (Array Value) := (obj.get? key).bind (·.getArr?)

def optObject (obj : Value) (key : String) : Option Value :=
  match obj.get? key with
  | some v@(.obj _) => some v
  | _ => none

def hasKey (obj : Value) (key : String) : Bool := obj.hasKey key

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
