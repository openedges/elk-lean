import Std.Data.HashMap
import Elk.Core.Data.LayoutOptionData
import Elk.Core.Data.LayoutAlgorithmData
/-!
# `org.eclipse.elk.core.data.{ILayoutMetaDataProvider, LayoutMetaDataService}`

The metadata service is a global registry (`IO.Ref`) of algorithms, options
and categories. Providers describe their contributions as a pure `Registry`
value which the service merges, resolving option dependencies and option
support declarations afterwards (elk-rs `Registry::apply_dependencies`).

Listing order is the registration order (elk-rs iterates `HashMap`s in an
unspecified order; elk-lean keeps the deterministic insertion order).

The core providers (`CoreOptions`, `BoxLayouterOptions`,
`LabelManagementOptions`, the fixed/random/box/layered algorithm entries) live
above this module; `Elk.Core.Init` installs them through `initHook` so the
first `getInstance` call registers them lazily, like elk-rs `get_instance()`.
-/
namespace Elk.Core.Data

open Elk Elk.Graph

/-- Pending contributions of one `ILayoutMetaDataProvider.apply` call
(`LayoutMetaDataRegistry` in elk-rs). -/
structure Registry where
  algorithms : Array LayoutAlgorithmData := #[]
  options : Array LayoutOptionData := #[]
  categories : Array LayoutCategoryData := #[]
  /-- `(sourceOption, targetOption, requiredValue)`. -/
  dependencies : Array (String × String × Option PropValue) := #[]
  /-- `(algorithm, option, defaultValue)`. -/
  optionSupport : Array (String × String × Option PropValue) := #[]

namespace Registry
def registerAlgorithm (r : Registry) (a : LayoutAlgorithmData) : Registry := { r with algorithms := r.algorithms.push a }
def registerOption (r : Registry) (o : LayoutOptionData) : Registry := { r with options := r.options.push o }
def registerCategory (r : Registry) (c : LayoutCategoryData) : Registry := { r with categories := r.categories.push c }
def addDependency (r : Registry) (source target : String) (required : Option PropValue) : Registry :=
  { r with dependencies := r.dependencies.push (source, target, required) }
def addOptionSupport (r : Registry) (algorithm option : String) (default : Option PropValue) : Registry :=
  { r with optionSupport := r.optionSupport.push (algorithm, option, default) }
end Registry

/-- `ILayoutMetaDataProvider`: a pure description of contributions. -/
structure LayoutMetaDataProvider where
  apply : Registry → Registry

/-- The registry state (`LayoutMetaDataStorage`). -/
structure LayoutMetaDataService where
  algorithms : Std.HashMap String LayoutAlgorithmData := {}
  algorithmOrder : Array String := #[]
  options : Std.HashMap String LayoutOptionData := {}
  optionOrder : Array String := #[]
  /-- legacy id → current option id -/
  legacyOptions : Std.HashMap String String := {}
  categories : Std.HashMap String LayoutCategoryData := {}
  categoryOrder : Array String := #[]
  algorithmSuffixMap : Std.HashMap String String := {}
  optionSuffixMap : Std.HashMap String String := {}

instance : Inhabited LayoutMetaDataService := ⟨{}⟩

namespace LayoutMetaDataService

/-- `idMatchesSuffix`: `id` equals `suffix` or ends with `"." ++ suffix`. -/
def idMatchesSuffix (id suffix : String) : Bool :=
  id == suffix || id.endsWith ("." ++ suffix)

/-! ### Pure registry operations -/

def registerLayoutAlgorithm (s : LayoutMetaDataService) (a : LayoutAlgorithmData) : LayoutMetaDataService :=
  let order := if s.algorithms.contains a.id then s.algorithmOrder else s.algorithmOrder.push a.id
  { s with algorithms := s.algorithms.insert a.id a, algorithmOrder := order, algorithmSuffixMap := {} }

def registerLayoutOption (s : LayoutMetaDataService) (o : LayoutOptionData) : LayoutMetaDataService :=
  let order := if s.options.contains o.id then s.optionOrder else s.optionOrder.push o.id
  let legacy := o.legacyIds.foldl (fun m l => m.insert l o.id) s.legacyOptions
  { s with options := s.options.insert o.id o, optionOrder := order, legacyOptions := legacy, optionSuffixMap := {} }

def registerLayoutCategory (s : LayoutMetaDataService) (c : LayoutCategoryData) : LayoutMetaDataService :=
  let order := if s.categories.contains c.id then s.categoryOrder else s.categoryOrder.push c.id
  { s with categories := s.categories.insert c.id c, categoryOrder := order }

private def backupCategoryId : String := ""

/-- `Registry::apply_dependencies`: assigns algorithms to their categories,
records option dependencies and option support. -/
def applyRegistry (s : LayoutMetaDataService) (r : Registry) : LayoutMetaDataService := Id.run do
  let mut s := s
  for a in r.algorithms do s := s.registerLayoutAlgorithm a
  for o in r.options do s := s.registerLayoutOption o
  for c in r.categories do s := s.registerLayoutCategory c
  -- categories: every algorithm (not only the ones from this registry, like elk-rs)
  for aid in s.algorithmOrder do
    let some alg := s.algorithms.get? aid | continue
    let cid := alg.categoryId.getD ""
    let cid := if cid.isEmpty then backupCategoryId else cid
    if cid == backupCategoryId && !s.categories.contains backupCategoryId then
      s := s.registerLayoutCategory { id := backupCategoryId, name := "Other" }
    match s.categories.get? cid with
    | some cat =>
      if !cat.layouters.contains aid then
        s := { s with categories := s.categories.insert cid { cat with layouters := cat.layouters.push aid } }
    | none => pure ()
  for (src, tgt, value) in r.dependencies do
    match s.options.get? src, s.options.get? tgt with
    | some source, some _ =>
      let source := { source with dependencies := source.dependencies.push { optionId := tgt, requiredValue := value } }
      s := { s with options := s.options.insert src source }
    | _, _ => pure ()
  for (aid, oid, value) in r.optionSupport do
    match s.algorithms.get? aid, s.options.get? oid with
    | some alg, some opt =>
      s := { s with algorithms := s.algorithms.insert aid (alg.addKnownOptionDefault opt.id value) }
    | _, _ => pure ()
  return { s with optionSuffixMap := {} }

def applyProvider (s : LayoutMetaDataService) (p : LayoutMetaDataProvider) : LayoutMetaDataService :=
  s.applyRegistry (p.apply {})

def algorithmData? (s : LayoutMetaDataService) (id : String) : Option LayoutAlgorithmData := s.algorithms.get? id

def algorithmDataList (s : LayoutMetaDataService) : Array LayoutAlgorithmData :=
  s.algorithmOrder.filterMap s.algorithms.get?

def optionData? (s : LayoutMetaDataService) (id : String) : Option LayoutOptionData :=
  match s.options.get? id with
  | some o => some o
  | none => (s.legacyOptions.get? id).bind s.options.get?

def optionDataList (s : LayoutMetaDataService) : Array LayoutOptionData :=
  s.optionOrder.filterMap s.options.get?

def categoryData? (s : LayoutMetaDataService) (id : String) : Option LayoutCategoryData := s.categories.get? id

def categoryDataList (s : LayoutMetaDataService) : Array LayoutCategoryData :=
  s.categoryOrder.filterMap s.categories.get?

/-- `getAlgorithmDataBySuffix`: unique id-suffix match, cached. Returns the
match and the service with an updated cache. -/
def algorithmDataBySuffix (s : LayoutMetaDataService) (suffix : String) : Option LayoutAlgorithmData × LayoutMetaDataService := Id.run do
  if suffix.trimAscii.toString.isEmpty then return (none, s)
  match s.algorithmSuffixMap.get? suffix with
  | some id => return (s.algorithms.get? id, s)
  | none => pure ()
  let mut found : Option String := none
  for aid in s.algorithmOrder do
    if idMatchesSuffix aid suffix then
      if found.isSome then return (none, s)
      found := some aid
  match found with
  | some aid => return (s.algorithms.get? aid, { s with algorithmSuffixMap := s.algorithmSuffixMap.insert suffix aid })
  | none => return (none, s)

/-- `getOptionDataBySuffix`: unique suffix match over ids, then legacy ids; cached. -/
def optionDataBySuffix (s : LayoutMetaDataService) (suffix : String) : Option LayoutOptionData × LayoutMetaDataService := Id.run do
  if suffix.trimAscii.toString.isEmpty then return (none, s)
  match s.optionSuffixMap.get? suffix with
  | some id => return (s.options.get? id, s)
  | none => pure ()
  let mut found : Option String := none
  for oid in s.optionOrder do
    if idMatchesSuffix oid suffix then
      if found.isSome then return (none, s)
      found := some oid
  if found.isNone then
    for oid in s.optionOrder do
      let some o := s.options.get? oid | continue
      for legacy in o.legacyIds do
        if idMatchesSuffix legacy suffix then
          if found.isSome then return (none, s)
          found := some oid
  match found with
  | some oid => return (s.options.get? oid, { s with optionSuffixMap := s.optionSuffixMap.insert suffix oid })
  | none => return (none, s)

/-- `getOptionData(algorithmData, targetType)`: options known to the
algorithm (plus `elk.algorithm`) that apply to the target. -/
def optionDataForAlgorithm (s : LayoutMetaDataService) (a : LayoutAlgorithmData) (target : LayoutOptionTarget) : Array LayoutOptionData :=
  s.optionDataList.filter fun o =>
    (a.knowsOption o.id || o.id == "org.eclipse.elk.algorithm") && o.targets.contains target

/-! ### Global instance -/

/-- Hook installed by `Elk.Core.Init`; runs once before the first use. -/
builtin_initialize initHookRef : IO.Ref (Option (IO Unit)) ← IO.mkRef none

builtin_initialize initializedRef : IO.Ref Bool ← IO.mkRef false

builtin_initialize instanceRef : IO.Ref LayoutMetaDataService ← IO.mkRef {}

/-- Hooks of the algorithm plugins (run after the core hook, in registration order). -/
builtin_initialize extraInitHooksRef : IO.Ref (Array (IO Unit)) ← IO.mkRef #[]

/-- Registers the lazy core initialisation (called at module initialisation of `Elk.Core.Init`). -/
def setInitHook (hook : IO Unit) : IO Unit := initHookRef.set (some hook)

/-- Adds a plugin initialisation hook (e.g. the layered metadata provider); runs after the core
hook the first time the service is used. Hooks added after initialisation run immediately. -/
def addInitHook (hook : IO Unit) : IO Unit := do
  if ← initializedRef.get then hook
  else extraInitHooksRef.modify (·.push hook)

/-- Runs the core initialisation once (`get_instance()` semantics). -/
def ensureInitialized : IO Unit := do
  if !(← initializedRef.get) then
    initializedRef.set true
    match ← initHookRef.get with
    | some hook => hook
    | none => pure ()
    for hook in (← extraInitHooksRef.get) do hook

/-- `LayoutMetaDataService.getInstance()`: a snapshot of the registry. -/
def getInstance : IO LayoutMetaDataService := do
  ensureInitialized
  instanceRef.get

/-- `unload()`: clears the registry (tests). The init hook will run again on the next access. -/
def unload : IO Unit := do
  instanceRef.set {}
  initializedRef.set false

/-- Applies a registry update to the global instance. -/
def modifyInstance (f : LayoutMetaDataService → LayoutMetaDataService) : IO Unit := do
  ensureInitialized
  instanceRef.modify f

/-- `registerLayoutMetaDataProvider(s)`. -/
def registerLayoutMetaDataProvider (p : LayoutMetaDataProvider) : IO Unit := modifyInstance (·.applyProvider p)

def registerLayoutMetaDataProviders (ps : Array LayoutMetaDataProvider) : IO Unit :=
  modifyInstance fun s => ps.foldl (·.applyProvider ·) s

/-- Registers an algorithm directly (core algorithms, placeholder entries). -/
def registerAlgorithm (a : LayoutAlgorithmData) : IO Unit := modifyInstance (·.registerLayoutAlgorithm a)

def getAlgorithmData (id : String) : IO (Option LayoutAlgorithmData) := do return (← getInstance).algorithmData? id
def getAlgorithmDataList : IO (Array LayoutAlgorithmData) := do return (← getInstance).algorithmDataList
def getOptionData (id : String) : IO (Option LayoutOptionData) := do return (← getInstance).optionData? id
def getOptionDataList : IO (Array LayoutOptionData) := do return (← getInstance).optionDataList
def getCategoryData (id : String) : IO (Option LayoutCategoryData) := do return (← getInstance).categoryData? id
def getCategoryDataList : IO (Array LayoutCategoryData) := do return (← getInstance).categoryDataList

def getAlgorithmDataBySuffix (suffix : String) : IO (Option LayoutAlgorithmData) := do
  ensureInitialized
  instanceRef.modifyGet fun s => s.algorithmDataBySuffix suffix

/-- `getAlgorithmDataBySuffixOrDefault(algorithmId, defaultId)`. -/
def getAlgorithmDataBySuffixOrDefault (algorithmId defaultId : Option String) : IO (Option LayoutAlgorithmData) := do
  for candidate in #[algorithmId, defaultId] do
    if let some id := candidate then
      let t := id.trimAscii.toString
      if !t.isEmpty then
        if let some d ← getAlgorithmDataBySuffix t then return some d
  return none

def getOptionDataBySuffix (suffix : String) : IO (Option LayoutOptionData) := do
  ensureInitialized
  instanceRef.modifyGet fun s => s.optionDataBySuffix suffix

def getOptionDataForAlgorithm (a : LayoutAlgorithmData) (target : LayoutOptionTarget) : IO (Array LayoutOptionData) := do
  return (← getInstance).optionDataForAlgorithm a target

/-- Resolves an option key (full id, legacy id or unique suffix) to its data. -/
def resolveOption (key : String) : IO (Option LayoutOptionData) := do
  match ← getOptionData key with
  | some d => return some d
  | none => getOptionDataBySuffix key

/-- `IndividualSpacings.parse`: `id:value;,;id:value` using the registered option parsers. -/
def parseIndividualSpacings (value : String) : IO (Except String (Array (PropKey × PropValue))) := do
  if value.trimAscii.toString.isEmpty then return .ok #[]
  let mut entries : Array (PropKey × PropValue) := #[]
  for entry in value.splitOn ";,;" do
    match entry.splitOn ":" with
    | [] | [_] => return .error "Invalid option entry."
    | optionId :: rest =>
      let optionValue := ":".intercalate rest
      let some data ← getOptionDataBySuffix optionId | return .error s!"Invalid option id: {optionId}"
      let some parsed := data.parseValue optionValue | return .error s!"Invalid option value: {optionValue}"
      entries := entries.push (PropKey.ofString data.id, parsed)
  return .ok entries

end LayoutMetaDataService

end Elk.Core.Data
