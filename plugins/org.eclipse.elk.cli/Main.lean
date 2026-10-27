import Elk.Api
/-!
# `elk` command line interface

```
elk layout [-o OUT] [--options JSON] [--pretty] [--sort-keys] [--lenient] [--defaults] INPUT.(json|elkt)
elk convert [-o OUT.json] [--pretty] [--sort-keys] [--defaults] INPUT.elkt
elk batch --input-manifest IN.tsv --output-manifest OUT.tsv --layout-dir DIR [--trace-dir DIR] [--pretty]
elk algorithms | options | categories
elk --version
```
`layout` and `convert` read ELK Text (`.elkt`) input through `Elk.Text.parseElkt`; `--defaults` applies the
elk-live defaults (node size 30, port size 5) to shapes without a size.
`batch` consumes the elk-rs parity manifest format (`model_rel_path	input_json	java_layout_json	java_status	java_error`)
and appends `rust_layout_json	rust_status	rust_error` columns (elk-lean fills the "rust" side).
-/

open Elk Elk.Json Elk.Api

def usage : String :=
  "usage:\n  elk layout [-o OUT] [--options JSON] [--pretty] [--sort-keys] [--lenient] [--defaults] INPUT.(json|elkt)\n  elk convert [-o OUT.json] [--pretty] [--sort-keys] [--defaults] INPUT.elkt\n  elk batch --input-manifest IN.tsv --output-manifest OUT.tsv --layout-dir DIR [--trace-dir DIR] [--pretty] [--sort-keys]\n  elk algorithms | options | categories\n  elk --version"

structure LayoutArgs where
  input : Option String := none
  output : Option String := none
  options : String := ""
  pretty : Bool := false
  sortKeys : Bool := false
  lenient : Bool := false
  defaults : Bool := false

/-- Writes `out` to `path` (creating directories) or prints it. Files get no trailing newline,
like the elk-rs parity runner (`fs::write`). -/
def writeOutput (path : Option String) (out : String) : IO Unit := do
  match path with
  | some path =>
    if let some dir := (System.FilePath.mk path).parent then IO.FS.createDirAll dir
    IO.FS.writeFile path out
  | none => IO.println out

/-- `true` for ELK Text inputs (`.elkt`). -/
def isElkt (path : String) : Bool := path.endsWith ".elkt"

/-- Parses ELK Text and renders it as ELK JSON (`Elk.Json.JsonExporter`). -/
def elktToJson (text : String) (defaults : Bool) (pretty : Bool := false) (sortKeys : Bool := false) : IO (Except String String) := do
  match ← Elk.Text.parseElkt text with
  | .error e => return .error s!"ELK Text parse error: {e}"
  | .ok (root, g) =>
    let g := if defaults then Elk.Text.applyDefaults g root else g
    let v ← Elk.Json.JsonExporter.exportValue g root {}
    return .ok (if pretty then v.renderPretty sortKeys else v.render sortKeys)

partial def parseLayoutArgs (args : List String) (acc : LayoutArgs) : Except String LayoutArgs :=
  match args with
  | [] => .ok acc
  | "-o" :: v :: rest => parseLayoutArgs rest { acc with output := some v }
  | "--options" :: v :: rest => parseLayoutArgs rest { acc with options := v }
  | "--pretty" :: rest => parseLayoutArgs rest { acc with pretty := true }
  | "--sort-keys" :: rest => parseLayoutArgs rest { acc with sortKeys := true }
  | "--lenient" :: rest => parseLayoutArgs rest { acc with lenient := true }
  | "--defaults" :: rest => parseLayoutArgs rest { acc with defaults := true }
  | a :: rest => if a.startsWith "-" then .error s!"unknown argument: {a}" else parseLayoutArgs rest { acc with input := some a }

def runLayout (args : List String) : IO UInt32 := do
  match parseLayoutArgs args {} with
  | .error e => IO.eprintln e; return 2
  | .ok a =>
    let some input := a.input | IO.eprintln "missing input file"; return 2
    let raw ← IO.FS.readFile input
    let text ← (do
      if isElkt input then
        match ← elktToJson raw a.defaults with
        | .error e => IO.eprintln e; return none
        | .ok json => return some json
      else return some raw)
    let some text := text | return 1
    match ← layoutJson text a.options a.lenient a.pretty a.sortKeys with
    | .error e => IO.eprintln e; return 1
    | .ok out => writeOutput a.output out; return 0

structure ConvertArgs where
  input : Option String := none
  output : Option String := none
  pretty : Bool := false
  sortKeys : Bool := false
  defaults : Bool := false

partial def parseConvertArgs (args : List String) (acc : ConvertArgs) : Except String ConvertArgs :=
  match args with
  | [] => .ok acc
  | "-o" :: v :: rest => parseConvertArgs rest { acc with output := some v }
  | "--pretty" :: rest => parseConvertArgs rest { acc with pretty := true }
  | "--sort-keys" :: rest => parseConvertArgs rest { acc with sortKeys := true }
  | "--defaults" :: rest => parseConvertArgs rest { acc with defaults := true }
  | a :: rest => if a.startsWith "-" then .error s!"unknown argument: {a}" else parseConvertArgs rest { acc with input := some a }

/-- `elk convert`: ELK Text → ELK JSON. -/
def runConvert (args : List String) : IO UInt32 := do
  match parseConvertArgs args {} with
  | .error e => IO.eprintln e; return 2
  | .ok a =>
    let some input := a.input | IO.eprintln "missing input file"; return 2
    let raw ← IO.FS.readFile input
    match ← elktToJson raw a.defaults a.pretty a.sortKeys with
    | .error e => IO.eprintln e; return 1
    | .ok out => writeOutput a.output out; return 0

structure BatchArgs where
  inputManifest : Option String := none
  outputManifest : Option String := none
  layoutDir : Option String := none
  pretty : Bool := false
  sortKeys : Bool := false
  /-- `--trace-dir DIR`: records the layered phase-step traces of every model under
  `DIR/<model_rel_path>/` (the elk-rs parity runner layout). -/
  traceDir : Option String := none

partial def parseBatchArgs (args : List String) (acc : BatchArgs) : Except String BatchArgs :=
  match args with
  | [] => .ok acc
  | "--input-manifest" :: v :: rest => parseBatchArgs rest { acc with inputManifest := some v }
  | "--output-manifest" :: v :: rest => parseBatchArgs rest { acc with outputManifest := some v }
  | "--layout-dir" :: v :: rest => parseBatchArgs rest { acc with layoutDir := some v }
  | "--trace-dir" :: v :: rest => parseBatchArgs rest { acc with traceDir := some v }
  | "--pretty" :: rest => parseBatchArgs rest { acc with pretty := true }
  | "--sort-keys" :: rest => parseBatchArgs rest { acc with sortKeys := true }
  | a :: _ => .error s!"unknown argument: {a}"

def sanitizeTsv (s : String) : String := String.map (fun c => if c == '\t' || c == '\n' || c == '\r' then ' ' else c) s

def runBatch (args : List String) : IO UInt32 := do
  match parseBatchArgs args {} with
  | .error e => IO.eprintln e; return 2
  | .ok a =>
    let some inManifest := a.inputManifest | IO.eprintln "missing --input-manifest"; return 2
    let some outManifest := a.outputManifest | IO.eprintln "missing --output-manifest"; return 2
    let some layoutDir := a.layoutDir | IO.eprintln "missing --layout-dir"; return 2
    let lines ← IO.FS.lines inManifest
    let mut out : Array String := #["model_rel_path\tinput_json\tjava_layout_json\tjava_status\tjava_error\trust_layout_json\trust_status\trust_error"]
    let mut ok := 0
    let mut failed := 0
    let mut first := true
    for line in lines do
      if first then
        first := false
        continue
      if line.trimAscii.toString.isEmpty then continue
      let cols := line.splitOn "\t"
      if cols.length < 5 then continue
      let rel := cols[0]!
      let inputPath := cols[1]!
      let outPath := layoutDir ++ "/" ++ rel ++ ".json"
      if let some traceBase := a.traceDir then
        let dir := traceBase ++ "/" ++ rel
        IO.FS.createDirAll dir
        Elk.Alg.Layered.TraceRecorder.setTraceDirOverride (some dir)
        Elk.Alg.Layered.TraceRecorder.resetStepCounter
      let (status, err) ← (do
        let text ← IO.FS.readFile inputPath
        match ← layoutJson text "" false a.pretty a.sortKeys with
        | .error e => pure ("error", e)
        | .ok res =>
          if let some dir := (System.FilePath.mk outPath).parent then IO.FS.createDirAll dir
          IO.FS.writeFile outPath res
          pure ("ok", ""))
        <|> pure ("error", "unexpected IO failure")
      if status == "ok" then ok := ok + 1 else failed := failed + 1
      IO.println s!"[{ok + failed}/{lines.size - 1}] {status} {rel}{if err.isEmpty then "" else s!": {sanitizeTsv err}"}"
      out := out.push s!"{rel}\t{inputPath}\t{cols[2]!}\t{cols[3]!}\t{cols[4]!}\t{if status == "ok" then outPath else ""}\t{status}\t{sanitizeTsv err}"
    if let some dir := (System.FilePath.mk outManifest).parent then IO.FS.createDirAll dir
    IO.FS.writeFile outManifest ("\n".intercalate out.toList ++ "\n")
    IO.println s!"batch completed: ok={ok}, errors={failed}"
    return (if failed == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--version"] | ["-V"] =>
    IO.println s!"elk-lean {Elk.Api.version} (ELK {Elk.Api.elkVersion})"
    return 0
  | "layout" :: rest => runLayout rest
  | "convert" :: rest => runConvert rest
  | "batch" :: rest => runBatch rest
  | ["algorithms"] => IO.println (← knownLayoutAlgorithms); return 0
  | ["options"] => IO.println (← knownLayoutOptions); return 0
  | ["categories"] => IO.println (← knownLayoutCategories); return 0
  | _ =>
    IO.eprintln usage
    return 2
