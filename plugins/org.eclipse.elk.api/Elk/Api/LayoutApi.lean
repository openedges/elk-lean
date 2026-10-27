import Elk.Json
/-!
# elkjs-compatible string API (`layout_api.rs`)

`layoutJson graph options` runs the full pipeline: parse → global option
defaults → import → `RecursiveGraphLayoutEngine` → materialise defaults →
transfer layout → serialise. Errors are reported with the Java exception
class convention (`org.eclipse.elk.core.UnsupportedConfigurationException: …`).
-/
namespace Elk.Api

open Elk Elk.Graph Elk.Core Elk.Core.Util Elk.Core.Data Elk.Json

/-- Registers the core metadata (algorithm plugins add their providers here). -/
def ensureInitialized : IO Unit := do
  LayoutMetaDataService.ensureInitialized

/-- elk-rs `catch_layout`: errors carrying an ELK exception class pass through,
anything else is wrapped as `UnsupportedConfigurationException`. -/
def catchLayout {α : Type} (act : IO α) : IO (Except String α) := do
  try
    return .ok (← act)
  catch e =>
    let msg := toString e
    if (msg.splitOn "org.eclipse.elk.core.").length > 1 then return .error msg
    else return .error s!"{unsupportedConfigurationExceptionClass}: {msg}"

/-- `layout_value`: lays out a parsed document. Returns the laid-out document. -/
def layoutValue (input : Value) (optionsJson : String := "") (forceRootAlgorithm : Option String := none) :
    IO (Except String Value) := do
  ensureInitialized
  catchLayout do
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
    let (((), st), _) ← (ImportM.run JsonImporter.transferLayout st).run g
    return st.model

/-- `layout_json`: string in, string out (elkjs `layout()` contract). -/
def layoutJson (graphJson : String) (optionsJson : String := "") (lenient : Bool := false)
    (pretty : Bool := false) (sortKeys : Bool := false) (forceRootAlgorithm : Option String := none) :
    IO (Except String String) := do
  match Elk.Json.parse graphJson lenient with
  | .error e => return .error s!"Failed to parse graph JSON: {e}"
  | .ok input =>
    match ← layoutValue input optionsJson forceRootAlgorithm with
    | .error e => return .error e
    | .ok v => return .ok (if pretty then v.renderPretty sortKeys else v.render sortKeys)

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
