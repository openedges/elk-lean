import Elk.Json
/-!
# elkjs-compatible string API (`layout_api.rs`)

`layoutJson graph options` runs the full pipeline: parse → global option
defaults → import → `RecursiveGraphLayoutEngine` → materialise defaults →
transfer layout → serialise. Errors are reported like ELK Java's `Throwable.toString()`
(`<fully qualified exception class>: <message>`, `catchLayout`).
-/
namespace Elk.Api

open Elk Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Data Elk.Json

/-- Registers the core metadata (algorithm plugins add their providers here). -/
def ensureInitialized : IO Unit := do
  LayoutMetaDataService.ensureInitialized

/-- Whether `msg` is already in Java's `Throwable.toString()` form: it starts with a fully
qualified exception class of the JDK or of ELK (`java.…`/`org.eclipse.…`, last segment ending in
`Exception` or `Error`), followed by `": "` or the end of the text. -/
def isJavaThrowableText (msg : String) : Bool :=
  let head := match msg.splitOn ": " with
    | h :: _ => h
    | [] => ""
  let simpleName := match (head.splitOn ".").reverse with
    | n :: _ => n
    | [] => ""
  (head.startsWith "java." || head.startsWith "org.eclipse.") &&
    head.all (fun c => c.isAlphanum || c == '.' || c == '_' || c == '$') &&
    (simpleName.endsWith "Exception" || simpleName.endsWith "Error")

/-- elk-rs `catch_layout` with ELK Java's error text: an error that already names its Java
exception class (`isJavaThrowableText`, e.g. `java.lang.IllegalArgumentException: …` or
`org.eclipse.elk.graph.json.JsonImportException: …`, which is what `Throwable.toString()` gives
for the exception ELK Java throws) or mentions an `org.eclipse.elk.core.` class passes unchanged;
anything else is wrapped as `UnsupportedConfigurationException`. (elk-rs also wraps
`java.lang.*` errors, as `UnsupportedConfigurationException: java.lang.…`.) -/
def catchLayout {α : Type} (act : IO α) : IO (Except String α) := do
  try
    return .ok (← act)
  catch e =>
    let msg := toString e
    if isJavaThrowableText msg || (msg.splitOn "org.eclipse.elk.core.").length > 1 then return .error msg
    else return .error s!"{unsupportedConfigurationExceptionClass}: {msg}"

/-- The pipeline of `layoutValue`/`layoutJson` up to the transfer: parse the options, import, lay
out, materialise the defaults and transfer the layout. Returns the importer state and the transfer
overlay (`JsonImporter.transferLayoutOverlay`, the document unchanged), or `none` when the overlay
does not apply and `JsonImporter.transferLayout` has rewritten `st.model`. -/
def layoutTransfer (input : Value) (optionsJson : String) (forceRootAlgorithm : Option String) :
    IO (ImporterState × Option Overlay) := do
  let defaults ← match ← GlobalOptions.parse optionsJson with
    | .ok g => pure g
    | .error e => throw (IO.userError e)
  let ((root, st), g) ← (ImportM.run (JsonImporter.transform input) { defaults := some defaults }).run {}
  -- elk-rs `model_parity_layout_runner` in trace mode sets the root `ALGORITHM` to layered right
  -- after the import (`force_layered_algorithm`); `forceRootAlgorithm` reproduces that
  let g := match forceRootAlgorithm with
    | some alg => g.modifyNode root fun n => { n with props := n.props.set Elk.Core.Options.CoreOptions.ALGORITHM alg }
    | none => g
  let ((), g) ← (RecursiveGraphLayoutEngine.layout root (ProgressMonitor.null)).run g
  let materialized ← (st.defaults.getD defaults).materialize st.model
  let st := { st with model := materialized }
  -- the transfer reads the graph only
  let ((ov, st'), _) ← (ImportM.run JsonImporter.transferLayoutOverlay st).run g
  if ov.ok then return (st', some ov)
  let (((), st), _) ← (ImportM.run JsonImporter.transferLayout st).run g
  return (st, none)

/-- `layout_value`: lays out a parsed document. Returns the laid-out document. -/
def layoutValue (input : Value) (optionsJson : String := "") (forceRootAlgorithm : Option String := none) :
    IO (Except String Value) := do
  ensureInitialized
  catchLayout do
    match ← layoutTransfer input optionsJson forceRootAlgorithm with
    | (st, some ov) => return Overlay.materialize (.ofState st ov) st.model
    | (st, none) => return st.model

/-- `layout_json`: string in, string out (elkjs `layout()` contract). The compact output with
document key order is printed straight from the overlay (`OverlayPrinter.render`). -/
def layoutJson (graphJson : String) (optionsJson : String := "") (lenient : Bool := false)
    (pretty : Bool := false) (sortKeys : Bool := false) (forceRootAlgorithm : Option String := none) :
    IO (Except String String) := do
  match Elk.Json.parse graphJson lenient with
  | .error e => return .error s!"Failed to parse graph JSON: {e}"
  | .ok input =>
    ensureInitialized
    catchLayout do
      -- the laid-out document is about 3 to 5 times the input (positions, sections), pretty
      -- printing adds the indentation
      let cap := (if pretty then 8 else 4) * graphJson.utf8ByteSize + 256
      match ← layoutTransfer input optionsJson forceRootAlgorithm with
      | (st, some ov) =>
        let c := Overlay.Ctx.ofState st ov
        if pretty || sortKeys then
          let v := Overlay.materialize c st.model
          return if pretty then v.renderPretty sortKeys cap else v.render sortKeys cap
        else return OverlayPrinter.render c st.model cap
      | (st, none) => return if pretty then st.model.renderPretty sortKeys cap else st.model.render sortKeys cap

private def graphFeatureName : GraphFeature → String
  | .selfLoops => "SELF_LOOPS"
  | .insideSelfLoops => "INSIDE_SELF_LOOPS"
  | .multiEdges => "MULTI_EDGES"
  | .edgeLabels => "EDGE_LABELS"
  | .ports => "PORTS"
  | .compound => "COMPOUND"
  | .clusters => "CLUSTERS"
  | .disconnected => "DISCONNECTED"

private def optionTypeName : LayoutOptionType → String
  | .undefined => "UNDEFINED"
  | .boolean => "BOOLEAN"
  | .int => "INT"
  | .string => "STRING"
  | .double => "DOUBLE"
  | .enum => "ENUM"
  | .enumSet => "ENUMSET"
  | .object => "OBJECT"

private def optionTargetName : LayoutOptionTarget → String
  | .parents => "PARENTS"
  | .nodes => "NODES"
  | .edges => "EDGES"
  | .ports => "PORTS"
  | .labels => "LABELS"

/-- `known_layout_algorithms`: JSON array of registered algorithms. -/
def knownLayoutAlgorithmsValue : IO Value := do
  ensureInitialized
  let algs ← LayoutMetaDataService.getAlgorithmDataList
  return .arr (algs.map fun a => .obj #[
    ("id", .str a.id), ("name", .str a.name), ("description", .str a.description),
    ("category", .str (a.categoryId.getD "")),
    ("knownOptions", .arr (a.knownOptionIds.map Value.str)),
    ("supportedFeatures", .arr ((a.supportedFeatures.toArray).map fun f => Value.str (graphFeatureName f)))])

/-- `known_layout_options`: JSON array of registered options. -/
def knownLayoutOptionsValue : IO Value := do
  ensureInitialized
  let opts ← LayoutMetaDataService.getOptionDataList
  return .arr (opts.map fun o => .obj #[
    ("id", .str o.id), ("name", .str o.name), ("description", .str o.description),
    ("group", .str o.group), ("type", .str (optionTypeName o.type)),
    ("targets", .arr ((o.targets.toArray).map fun t => Value.str (optionTargetName t)))])

/-- `known_layout_categories`. -/
def knownLayoutCategoriesValue : IO Value := do
  ensureInitialized
  let cats ← LayoutMetaDataService.getCategoryDataList
  return .arr (cats.map fun c => .obj #[
    ("id", .str c.id), ("name", .str c.name), ("description", .str c.description),
    ("knownLayouters", .arr (c.layouters.map Value.str))])

def knownLayoutAlgorithms : IO String := do return (← knownLayoutAlgorithmsValue).render
def knownLayoutOptions : IO String := do return (← knownLayoutOptionsValue).render
def knownLayoutCategories : IO String := do return (← knownLayoutCategoriesValue).render

end Elk.Api
