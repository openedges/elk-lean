import Elk.Api
/-!
# `elk` command line interface

```
elk layout [-o OUT] [--options JSON] [--pretty] [--sort-keys] [--lenient] [--defaults] [--force-algorithm ID] INPUT.(json|elkt)
elk convert [-o OUT.json] [--pretty] [--sort-keys] [--defaults] INPUT.elkt
elk batch --input-manifest IN.tsv --output-manifest OUT.tsv --layout-dir DIR [--trace-dir DIR] [--pretty]
elk bench [--mode synthetic|models] [--scenarios A,B] [--iterations N] [--warmup N] [--output CSV]
          [--manifest TSV | --input-dir DIR] [--limit N] [--dump-dir DIR]
elk algorithms | options | categories
elk --version
```
`bench` is elk-rs `perf_benchmark --engine rust_api` (same graphs, same CSV; engine `lean_api`).
`layout` and `convert` read ELK Text (`.elkt`) input through `Elk.Text.parseElkt`; `--defaults` applies the
elk-live defaults (node size 30, port size 5) to shapes without a size.
`batch` consumes the elk-rs parity manifest format (`model_rel_path	input_json	java_layout_json	java_status	java_error`)
and appends `rust_layout_json	rust_status	rust_error` columns (elk-lean fills the "rust" side).
-/

open Elk Elk.Json Elk.Api

def usage : String :=
  "usage:\n  elk layout [-o OUT] [--options JSON] [--pretty] [--sort-keys] [--lenient] [--defaults] [--force-algorithm ID] INPUT.(json|elkt)\n  elk convert [-o OUT.json] [--pretty] [--sort-keys] [--defaults] INPUT.elkt\n  elk batch --input-manifest IN.tsv --output-manifest OUT.tsv --layout-dir DIR [--trace-dir DIR] [--pretty] [--sort-keys]\n  elk bench [--mode synthetic|models] [--scenarios A,B] [--iterations N] [--warmup N] [--output CSV] [--manifest TSV | --input-dir DIR] [--limit N] [--dump-dir DIR]\n  elk algorithms | options | categories\n  elk --version"

structure LayoutArgs where
  input : Option String := none
  output : Option String := none
  options : String := ""
  pretty : Bool := false
  sortKeys : Bool := false
  lenient : Bool := false
  defaults : Bool := false
  /-- `--force-algorithm ID`: sets the root `elk.algorithm` after the import (the elk-rs parity
  runner does this with layered in trace mode). -/
  forceAlgorithm : Option String := none

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
  | "--force-algorithm" :: v :: rest => parseLayoutArgs rest { acc with forceAlgorithm := some v }
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
    match ← layoutJson text a.options a.lenient a.pretty a.sortKeys a.forceAlgorithm with
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
        -- like the elk-rs runner, trace mode lays out every model with layered
        let force := if a.traceDir.isSome then some "org.eclipse.elk.layered" else none
        match ← layoutJson text "" false a.pretty a.sortKeys force with
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

/-- `elk bench` arguments (elk-rs `perf_benchmark` flags). -/
structure BenchArgs where
  mode : String := "synthetic"
  scenarios : Option (Array String) := none
  iterations : Nat := 20
  warmup : Nat := 3
  output : Option String := none
  inputDir : Option String := none
  manifest : Option String := none
  limit : Nat := 50
  /-- `--dump-dir DIR`: also writes every benchmark input as `DIR/<scenario>.json` (parity checks). -/
  dumpDir : Option String := none

partial def parseBenchArgs (args : List String) (acc : BenchArgs) : Except String BenchArgs :=
  let num (flag v : String) : Except String Nat :=
    match v.toNat? with
    | some n => .ok n
    | none => .error s!"{flag} expects a number, got '{v}'"
  match args with
  | [] => .ok acc
  | "--mode" :: v :: rest => parseBenchArgs rest { acc with mode := v }
  | "--engine" :: _ :: rest => parseBenchArgs rest acc
  | "--scenarios" :: v :: rest =>
    parseBenchArgs rest { acc with scenarios := some ((v.splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty) |>.toArray) }
  | "--iterations" :: v :: rest => do parseBenchArgs rest { acc with iterations := max (← num "--iterations" v) 1 }
  | "--warmup" :: v :: rest => do parseBenchArgs rest { acc with warmup := ← num "--warmup" v }
  | "--output" :: v :: rest => parseBenchArgs rest { acc with output := some v }
  | "--input-dir" :: v :: rest => parseBenchArgs rest { acc with inputDir := some v }
  | "--manifest" :: v :: rest => parseBenchArgs rest { acc with manifest := some v }
  | "--limit" :: v :: rest => do parseBenchArgs rest { acc with limit := ← num "--limit" v }
  | "--dump-dir" :: v :: rest => parseBenchArgs rest { acc with dumpDir := some v }
  | a :: _ => .error s!"unknown bench argument '{a}'"

/-- `elk bench`: elk-rs `perf_benchmark --engine rust_api` for elk-lean (`lean_api` rows). -/
def runBench (args : List String) : IO UInt32 := do
  let a ← match parseBenchArgs args {} with
    | .ok a => pure a
    | .error e => IO.eprintln e; return 2
  let engine := "lean_api"
  IO.eprintln "elk-lean Performance Benchmark"
  IO.eprintln s!"  Engine: {engine}, Mode: {a.mode}, Iterations: {a.iterations}, Warmup: {a.warmup}"
  IO.eprintln ""
  let cases ← match a.mode with
    | "synthetic" =>
      let all := Elk.Api.PerfBenchmark.syntheticScenarios
      pure (match a.scenarios with
        | some names => all.filter fun (n, _) => names.contains n
        | none => all)
    | "models" =>
      match a.manifest, a.inputDir with
      | some m, _ => IO.eprintln s!"Loading models from manifest: {m}"; Elk.Api.PerfBenchmark.loadModelsFromManifest m a.limit
      | none, some d => IO.eprintln s!"Loading models from directory: {d}"; Elk.Api.PerfBenchmark.loadModelsFromDir d a.limit
      | none, none => IO.eprintln "No manifest or input directory specified. Use --manifest or --input-dir."; return 2
    | m => IO.eprintln s!"Unknown mode: {m}. Use 'synthetic' or 'models'."; return 2
  if a.mode == "models" then
    IO.eprintln s!"Loaded {cases.size} models"
    IO.eprintln ""
  if let some dir := a.dumpDir then
    IO.FS.createDirAll dir
    for (name, json) in cases do
      IO.FS.writeFile (System.FilePath.mk dir / s!"{name}.json") json
  let mut lines : Array String := #[]
  let mut ok := 0
  let mut errors := 0
  for (name, json) in cases do
    match ← Elk.Api.PerfBenchmark.runApiBenchmark json a.iterations a.warmup with
    | .ok (nanos, avgMs, ops) =>
      ok := ok + 1
      if a.mode == "synthetic" || ok <= 5 || ok % 10 == 0 then
        IO.eprintln s!"  {name}: {Elk.Api.PerfBenchmark.fmtFixed avgMs 4} ms/op, {Elk.Api.PerfBenchmark.fmtFixed ops 0} ops/s ({nanos} ns total)"
      lines := lines.push (← Elk.Api.PerfBenchmark.csvLine engine name a.iterations a.warmup nanos avgMs ops)
    | .error e =>
      errors := errors + 1
      if a.mode == "synthetic" || errors <= 3 then IO.eprintln s!"  {name}: ERROR — {e}"
  if a.mode == "models" then
    IO.eprintln ""
    IO.eprintln s!"Done: {ok} ok, {errors} errors"
  IO.eprintln ""
  let csv := "timestamp,engine,scenario,iterations,warmup,elapsed_nanos,avg_ms,ops_per_sec\n" ++ "\n".intercalate lines.toList ++ "\n"
  match a.output with
  | some path =>
    if let some dir := (System.FilePath.mk path).parent then IO.FS.createDirAll dir
    IO.FS.writeFile path csv
    IO.eprintln s!"Results written to {path}"
  | none => IO.print csv
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--version"] | ["-V"] =>
    IO.println s!"elk-lean {Elk.Api.version} (ELK {Elk.Api.elkVersion})"
    return 0
  | "layout" :: rest => runLayout rest
  | "convert" :: rest => runConvert rest
  | "batch" :: rest => runBatch rest
  | "bench" :: rest => runBench rest
  | ["algorithms"] => IO.println (← knownLayoutAlgorithms); return 0
  | ["options"] => IO.println (← knownLayoutOptions); return 0
  | ["categories"] => IO.println (← knownLayoutCategories); return 0
  | _ =>
    IO.eprintln usage
    return 2
