import Elk.Api.LayoutApi
/-!
# Synthetic and model benchmarks (elk-rs `perf_benchmark.rs`, `rust_api` engine)

Generates exactly the JSON graphs of `perf_benchmark.rs` (same LCG, same text) and times
`layoutJson graph "{}"` — the path the NAPI/WASM bindings use — after `warmup` untimed runs.
Results use the elk-rs CSV format
`timestamp,engine,scenario,iterations,warmup,elapsed_nanos,avg_ms,ops_per_sec`
(engine `lean_api`), so `compare_perf_results.py` of elk-rs reads both files.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0
private def fl10p0 : Float := 10.0

namespace Elk.Api.PerfBenchmark

open Elk.Core.Util

/-- `lcg`: `(state * 1103515245 + 12345) & 0x7fffffff` with `u32` wrapping. -/
@[inline] def lcg (state : UInt32) : UInt32 := (state * 1103515245 + 12345) &&& 0x7fffffff

/-- `"    {"id":"n<i>","width":40,"height":30}"` lines joined by `,\n`. -/
private def plainChildren (nodes : Nat) : String :=
  ",\n".intercalate ((Array.range nodes).map fun i =>
    s!"    \{\"id\":\"n{i}\",\"width\":40,\"height\":30}").toList

/-- `generate_dag_json`: five layers (`i * 5 / nodes`), LCG edges kept only when they point to
a later layer, at most `edges * 100` attempts. -/
def generateDagJson (nodes edges : Nat) (seed : UInt32) (layoutOptions : String) : String := Id.run do
  let layerOf := (Array.range nodes).map fun i => i * 5 / max nodes 1
  let mut edgeLines : Array String := #[]
  let mut state := seed
  let mut attempts := 0
  while edgeLines.size < edges && attempts < edges * 100 do
    attempts := attempts + 1
    state := lcg state
    let src := state.toNat % nodes
    state := lcg state
    let tgt := state.toNat % nodes
    if layerOf[src]! < layerOf[tgt]! then
      let eid := edgeLines.size
      edgeLines := edgeLines.push s!"    \{\"id\":\"e{eid}\",\"sources\":[\"n{src}\"],\"targets\":[\"n{tgt}\"]}"
  let routing := if (layoutOptions.splitOn "edgeRouting").length > 1 then ""
    else ",\n    \"org.eclipse.elk.edgeRouting\":\"ORTHOGONAL\""
  let extra := if layoutOptions.isEmpty then "" else s!",\n    {layoutOptions}"
  return s!"\{\n  \"id\":\"root\",\n  \"layoutOptions\":\{\n    \"org.eclipse.elk.algorithm\":\"org.eclipse.elk.layered\",\n    \"org.eclipse.elk.direction\":\"RIGHT\"{routing}{extra}\n  },\n  \"children\":[\n{plainChildren nodes}\n  ],\n  \"edges\":[\n{",\n".intercalate edgeLines.toList}\n  ]\n}"

/-- `generate_tree_json`: node `i` hangs below a random earlier node. -/
def generateTreeJson (nodes : Nat) (seed : UInt32) (algorithm : String) : String := Id.run do
  let mut edgeLines : Array String := #[]
  let mut state := seed
  for i in [1:nodes] do
    state := lcg state
    let parent := state.toNat % i
    edgeLines := edgeLines.push s!"    \{\"id\":\"e{i}\",\"sources\":[\"n{parent}\"],\"targets\":[\"n{i}\"]}"
  return s!"\{\n  \"id\":\"root\",\n  \"layoutOptions\":\{\n    \"org.eclipse.elk.algorithm\":\"{algorithm}\"\n  },\n  \"children\":[\n{plainChildren nodes}\n  ],\n  \"edges\":[\n{",\n".intercalate edgeLines.toList}\n  ]\n}"

/-- `generate_general_graph_json`: `edges` uniformly random edges (self loops included). -/
def generateGeneralGraphJson (nodes edges : Nat) (seed : UInt32) (algorithm : String) : String := Id.run do
  let mut edgeLines : Array String := #[]
  let mut state := seed
  for eid in [0:edges] do
    state := lcg state
    let src := state.toNat % nodes
    state := lcg state
    let tgt := state.toNat % nodes
    edgeLines := edgeLines.push s!"    \{\"id\":\"e{eid}\",\"sources\":[\"n{src}\"],\"targets\":[\"n{tgt}\"]}"
  return s!"\{\n  \"id\":\"root\",\n  \"layoutOptions\":\{\n    \"org.eclipse.elk.algorithm\":\"{algorithm}\"\n  },\n  \"children\":[\n{plainChildren nodes}\n  ],\n  \"edges\":[\n{",\n".intercalate edgeLines.toList}\n  ]\n}"

/-- `generate_rectpacking_json`: random sizes in `20..=80`. -/
def generateRectPackingJson (nodes : Nat) (seed : UInt32) : String := Id.run do
  let mut state := seed
  let mut lines : Array String := #[]
  for i in [0:nodes] do
    state := lcg state
    let w := 20 + state.toNat % 61
    state := lcg state
    let h := 20 + state.toNat % 61
    lines := lines.push s!"    \{\"id\":\"n{i}\",\"width\":{w},\"height\":{h}}"
  return s!"\{\n  \"id\":\"root\",\n  \"layoutOptions\":\{\n    \"org.eclipse.elk.algorithm\":\"org.eclipse.elk.rectpacking\"\n  },\n  \"children\":[\n{",\n".intercalate lines.toList}\n  ],\n  \"edges\":[]\n}"

/-- `generate_hierarchy_nested_json`: three compound nodes with nine-leaf random trees each,
consecutive compounds linked by a cross-hierarchy edge, `INCLUDE_CHILDREN`. -/
def generateHierarchyNestedJson (seed : UInt32) : String := Id.run do
  let compounds := 3
  let leavesPer := 9
  let mut state := seed
  let mut blocks : Array String := #[]
  let mut crossEdges : Array String := #[]
  let mut crossEid := 0
  for c in [0:compounds] do
    let leafNodes := (Array.range leavesPer).map fun l =>
      s!"      \{\"id\":\"c{c}_l{l}\",\"width\":40,\"height\":30}"
    let mut internalEdges : Array String := #[]
    for l in [1:leavesPer] do
      state := lcg state
      let src := state.toNat % l
      internalEdges := internalEdges.push
        s!"      \{\"id\":\"c{c}_ie{l}\",\"sources\":[\"c{c}_l{src}\"],\"targets\":[\"c{c}_l{l}\"]}"
    blocks := blocks.push s!"    \{\n      \"id\":\"compound{c}\",\"width\":0,\"height\":0,\n      \"children\":[\n{",\n".intercalate leafNodes.toList}\n      ],\n      \"edges\":[\n{",\n".intercalate internalEdges.toList}\n      ]\n    }"
    if c + 1 < compounds then
      crossEdges := crossEdges.push s!"    \{\"id\":\"xe{crossEid}\",\"sources\":[\"c{c}_l0\"],\"targets\":[\"c{c + 1}_l0\"]}"
      crossEid := crossEid + 1
  return s!"\{\n  \"id\":\"root\",\n  \"layoutOptions\":\{\n    \"org.eclipse.elk.algorithm\":\"org.eclipse.elk.layered\",\n    \"org.eclipse.elk.direction\":\"RIGHT\",\n    \"org.eclipse.elk.edgeRouting\":\"ORTHOGONAL\",\n    \"org.eclipse.elk.hierarchyHandling\":\"INCLUDE_CHILDREN\"\n  },\n  \"children\":[\n{",\n".intercalate blocks.toList}\n  ],\n  \"edges\":[\n{",\n".intercalate crossEdges.toList}\n  ]\n}"

/-- `synthetic_scenarios_json`: the 26 scenarios in elk-rs order. -/
def syntheticScenarios : Array (String × String) := #[
  ("layered_small", generateDagJson 10 15 42 ""),
  ("layered_medium", generateDagJson 50 100 42 ""),
  ("layered_large", generateDagJson 200 500 42 ""),
  ("layered_xlarge", generateDagJson 1000 3000 42 ""),
  ("force_medium", generateGeneralGraphJson 50 80 100 "org.eclipse.elk.force"),
  ("force_large", generateGeneralGraphJson 200 400 100 "org.eclipse.elk.force"),
  ("force_xlarge", generateGeneralGraphJson 500 1200 100 "org.eclipse.elk.force"),
  ("stress_medium", generateGeneralGraphJson 50 80 100 "org.eclipse.elk.stress"),
  ("stress_large", generateGeneralGraphJson 200 400 100 "org.eclipse.elk.stress"),
  ("stress_xlarge", generateGeneralGraphJson 500 1200 100 "org.eclipse.elk.stress"),
  ("mrtree_medium", generateTreeJson 50 200 "org.eclipse.elk.mrtree"),
  ("mrtree_large", generateTreeJson 200 200 "org.eclipse.elk.mrtree"),
  ("mrtree_xlarge", generateTreeJson 1000 200 "org.eclipse.elk.mrtree"),
  ("radial_medium", generateTreeJson 50 200 "org.eclipse.elk.radial"),
  ("radial_large", generateTreeJson 200 200 "org.eclipse.elk.radial"),
  ("radial_xlarge", generateTreeJson 1000 200 "org.eclipse.elk.radial"),
  ("rectpacking_medium", generateRectPackingJson 50 100),
  ("rectpacking_large", generateRectPackingJson 200 100),
  ("rectpacking_xlarge", generateRectPackingJson 1000 100),
  ("routing_polyline", generateDagJson 50 100 42 "\"org.eclipse.elk.edgeRouting\": \"POLYLINE\""),
  ("routing_orthogonal", generateDagJson 50 100 42 "\"org.eclipse.elk.edgeRouting\": \"ORTHOGONAL\""),
  ("routing_splines", generateDagJson 50 100 42 "\"org.eclipse.elk.edgeRouting\": \"SPLINES\""),
  ("crossmin_layer_sweep", generateDagJson 50 100 42
    "\"org.eclipse.elk.layered.crossingMinimization.strategy\": \"LAYER_SWEEP\", \"org.eclipse.elk.layered.crossingMinimization.greedySwitch.type\": \"TWO_SIDED\""),
  ("crossmin_none", generateDagJson 50 100 42
    "\"org.eclipse.elk.layered.crossingMinimization.strategy\": \"NONE\", \"org.eclipse.elk.layered.crossingMinimization.greedySwitch.type\": \"OFF\""),
  ("hierarchy_flat", generateDagJson 30 50 300 ""),
  ("hierarchy_nested", generateHierarchyNestedJson 300)
]

/-- Rust `{:.N}` for the non-negative timings of the report (round half away from zero). -/
def fmtFixed (x : Float) (digits : Nat) : String :=
  if !x.isFinite then Float.toShortest x
  else
    let neg := x < fl0p0
    let scale := (fl10p0 : Float) ^ digits.toFloat
    let n := (x.abs * scale).round.toUInt64.toNat
    let p := 10 ^ digits
    let frac := toString (n % p)
    let frac := "".pushn '0' (digits - frac.length) ++ frac
    let body := if digits == 0 then toString (n / p) else s!"{n / p}.{frac}"
    if neg && n != 0 then "-" ++ body else body

/-- One benchmark row (`format_csv_line`). -/
def csvLine (engine scenario : String) (iterations warmup elapsedNanos : Nat) (avgMs opsPerSec : Float) :
    IO String := do
  let ts ← unixTimeSecs
  return s!"{ts},{engine},{scenario},{iterations},{warmup},{elapsedNanos},{fmtFixed avgMs 6},{fmtFixed opsPerSec 2}"

/-- `run_api_benchmark`: `warmup` untimed and `iterations` timed `layoutJson json "{}"` calls.
Returns `(elapsed_nanos, avg_ms, ops_per_sec)`. -/
def runApiBenchmark (json : String) (iterations warmup : Nat) : IO (Except String (Nat × Float × Float)) := do
  for _ in [0:warmup] do
    if let .error e ← layoutJson json "{}" then return .error e
  let start ← IO.monoNanosNow
  for _ in [0:iterations] do
    if let .error e ← layoutJson json "{}" then return .error e
  let nanos := max ((← IO.monoNanosNow) - start) 1
  let iters := max iterations 1
  let avgMs := nanos.toFloat / iters.toFloat / 1000000.0
  let opsPerSec := iters.toFloat / (nanos.toFloat / 1000000000.0)
  return .ok (nanos, avgMs, opsPerSec)

/-- `load_models_from_manifest`: rows of a parity manifest whose status column (4th) is `ok`
and whose input JSON exists; names drop `.elkg`/`.elkt` and replace `/` by `_`. -/
def loadModelsFromManifest (path : String) (limit : Nat) : IO (Array (String × String)) := do
  let text ← IO.FS.readFile path
  let mut models : Array (String × String) := #[]
  let mut first := true
  for line in text.splitOn "\n" do
    if first then
      first := false
      if (line.dropWhile (· == '﻿')).startsWith "model_rel_path" then continue
    let cols := (line.splitOn "\t").toArray
    if cols.size < 5 then continue
    if cols[3]! != "ok" then continue
    let input : System.FilePath := cols[1]!
    if !(← input.pathExists) then continue
    let json ← IO.FS.readFile input
    let rel := cols[0]!
    let rel := if rel.endsWith ".elkg" then (rel.dropEnd 5).toString else rel
    let rel := if rel.endsWith ".elkt" then (rel.dropEnd 5).toString else rel
    models := models.push (rel.map (fun c => if c == '/' || c == '\\' then '_' else c), json)
    if limit > 0 && models.size >= limit then break
  return models

/-- `collect_json_files` + `load_models_from_dir`: every `*.json` below `dir`, sorted by path. -/
def loadModelsFromDir (dir : String) (limit : Nat) : IO (Array (String × String)) := do
  let paths ← (System.FilePath.mk dir).walkDir
  let names : Array String := (paths.filter fun p => p.extension == some "json").map fun p => p.toString
  let files := stableSort names fun a b => Ord.compare a b
  let mut models : Array (String × String) := #[]
  for f in files do
    let json ← IO.FS.readFile f
    let rel := if f.startsWith dir then (f.drop dir.length).toString else f
    let rel := (rel.dropWhile (· == '/')).toString
    let rel := if rel.endsWith ".json" then (rel.dropEnd 5).toString else rel
    models := models.push (rel.map (fun c => if c == '/' || c == '\\' then '_' else c), json)
    if limit > 0 && models.size >= limit then break
  return models

end Elk.Api.PerfBenchmark
