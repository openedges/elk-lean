import Std.Data.HashMap
import Elk.Alg.Layered.Graph
import Elk.Json.Value
import Elk.Json.Printer
/-!
# Phase-step trace recorder (elk-rs `trace_recorder.rs` + the trace scope of `elk_layered.rs`)

When `ELK_TRACE_DIR` is set, `ElkLayered` records a JSON snapshot of the root graph after
every processor: `<dir>/step_NNN_<Processor>.json`. The schema, the element id scheme
(`N<i>`/`P<i>` in layer → layerless → external order, `E<edge.id>`), the sorted-key pretty
format and the `NaN`/`Infinity` sentinels are those of elk-rs so that
`scripts/compare_phase_traces.py` can compare both.
-/
/-! Float literals as global constants (FL): inside branches, loops and specialised code the compiler
shares a literal's `Nat`/`Bool` arguments with unrelated variables (CSE) and then parses it on every
evaluation (`FastFloat.ofScientificImpl`); a top-level constant is a load (PLAN §7.1 items 17, 22). -/
private def fl0p0 : Float := 0.0

namespace Elk.Alg.Layered

open Elk.Graph Elk.Core.Math Elk.Json Elk.Alg.Layered.Graph

namespace TraceRecorder

def NAN_SENTINEL : String := "__ELK_TRACE_NAN__"
def POS_INF_SENTINEL : String := "__ELK_TRACE_POS_INF__"
def NEG_INF_SENTINEL : String := "__ELK_TRACE_NEG_INF__"

/-- `number_or_special`: finite numbers as JSON numbers, specials as sentinel strings. -/
def numberOrSpecial (v : Float) : Value :=
  if v.isNaN then .str NAN_SENTINEL
  else if v.isInf then (if v > fl0p0 then .str POS_INF_SENTINEL else .str NEG_INF_SENTINEL)
  else Value.ofFloat v

/-- Snapshot-local ids (`TraceIds`): nodes in layer order, then layerless nodes, then the
external nodes reached through outgoing edges; ports numbered in that node order. -/
structure TraceIds where
  externalNodes : Array LNodeId := #[]
  nodes : Std.HashMap LNodeId String := {}
  ports : Std.HashMap LPortId String := {}

/-- `TraceIds::new(graph)`. -/
def TraceIds.new (a : LGraphArena) (g : LGraphId) : TraceIds := Id.run do
  let gr := a.graph g
  let mut nodes : Array LNodeId := #[]
  for l in gr.layers do nodes := nodes ++ (a.layer l).nodes
  nodes := nodes ++ gr.layerlessNodes
  let mut seen : Std.HashMap LNodeId Unit := {}
  for n in nodes do seen := seen.insert n ()
  let mut externalNodes : Array LNodeId := #[]
  for n in nodes do
    for p in (a.node n).ports do
      for e in (a.port p).outgoingEdges do
        if let some target := (a.edge e).target then
          if let some tn := (a.port target).owner then
            if !seen.contains tn then
              seen := seen.insert tn ()
              externalNodes := externalNodes.push tn
  nodes := nodes ++ externalNodes
  let mut ids : TraceIds := { externalNodes := externalNodes }
  let mut portCount := 0
  for h : index in [0:nodes.size] do
    let n := nodes[index]
    ids := { ids with nodes := ids.nodes.insert n s!"N{index}" }
    for p in (a.node n).ports do
      ids := { ids with ports := ids.ports.insert p s!"P{portCount}" }
      portCount := portCount + 1
  return ids

private def xy (v : KVector) : Value := .obj #[("x", numberOrSpecial v.x), ("y", numberOrSpecial v.y)]

private def sides (top bottom left right : Float) : Value :=
  .obj #[("top", numberOrSpecial top), ("bottom", numberOrSpecial bottom),
         ("left", numberOrSpecial left), ("right", numberOrSpecial right)]

/-- `serialize_label`. -/
def serializeLabel (a : LGraphArena) (l : LLabelId) : Value :=
  let lb := a.label l
  .obj #[("text", .str lb.text), ("x", numberOrSpecial lb.position.x), ("y", numberOrSpecial lb.position.y),
         ("width", numberOrSpecial lb.size.x), ("height", numberOrSpecial lb.size.y)]

/-- `serialize_port`. -/
def serializePort (a : LGraphArena) (ids : TraceIds) (p : LPortId) : Value :=
  let pt := a.port p
  .obj #[("id", .str (ids.ports.getD p "?")), ("side", .str (ElkEnum.javaName pt.side)),
         ("width", numberOrSpecial pt.size.x), ("height", numberOrSpecial pt.size.y),
         ("anchor", xy pt.anchor),
         ("margin", sides pt.margin.top pt.margin.bottom pt.margin.left pt.margin.right),
         ("x", numberOrSpecial pt.position.x), ("y", numberOrSpecial pt.position.y),
         ("labels", .arr (pt.labels.map (serializeLabel a)))]

/-- `serialize_node`: `name` is the element designation, which elk-rs resolves to the id. -/
def serializeNode (a : LGraphArena) (ids : TraceIds) (n : LNodeId) : Value :=
  let nd := a.node n
  let id := ids.nodes.getD n "?"
  let layerIndex : Value := match nd.layer with
    | some l => match a.layerIndex l with
      | some i => Value.ofNat i
      | none => Value.ofInt (-1)
    | none => Value.ofInt (-1)
  .obj #[("id", .str id), ("name", .str id), ("type", .str nd.type.name),
         ("x", numberOrSpecial nd.position.x), ("y", numberOrSpecial nd.position.y),
         ("width", numberOrSpecial nd.size.x), ("height", numberOrSpecial nd.size.y),
         ("layer", layerIndex),
         ("margin", sides nd.margin.top nd.margin.bottom nd.margin.left nd.margin.right),
         ("ports", .arr (nd.ports.map (serializePort a ids))),
         ("labels", .arr (nd.labels.map (serializeLabel a))),
         ("padding", sides nd.padding.top nd.padding.bottom nd.padding.left nd.padding.right)]

/-- `serialize_edge`: `none` for edges without both end ports/nodes (they are skipped). -/
def serializeEdge (a : LGraphArena) (ids : TraceIds) (e : LEdgeId) : Option Value := do
  let ed := a.edge e
  let source ← ed.source
  let target ← ed.target
  let sourceNode ← (a.port source).owner
  let targetNode ← (a.port target).owner
  return .obj #[("id", .str s!"E{ed.id}"),
                ("sourceNode", .str (ids.nodes.getD sourceNode "?")), ("sourcePort", .str (ids.ports.getD source "?")),
                ("targetNode", .str (ids.nodes.getD targetNode "?")), ("targetPort", .str (ids.ports.getD target "?")),
                ("bendPoints", .arr (ed.bendPoints.map xy)),
                ("labels", .arr (ed.labels.map (serializeLabel a)))]

/-- `serialize_lgraph_snapshot` (the JSON value): layers, layerless `nodes`, `edges` (first
occurrence order over layerless then layer nodes), `externalNodes`, sizes. -/
def snapshot (a : LGraphArena) (g : LGraphId) (step : Nat) (processorName : String) : Value := Id.run do
  let gr := a.graph g
  let ids := TraceIds.new a g
  let mut layersJson : Array Value := #[]
  for h : layerIndex in [0:gr.layers.size] do
    let l := gr.layers[layerIndex]
    layersJson := layersJson.push (.obj #[("index", Value.ofNat layerIndex),
      ("nodes", .arr ((a.layer l).nodes.map (serializeNode a ids)))])
  let layerless := gr.layerlessNodes.map (serializeNode a ids)
  let mut seenEdges : Std.HashMap LEdgeId Unit := {}
  let mut edges : Array Value := #[]
  let collect (nodes : Array LNodeId) (seen : Std.HashMap LEdgeId Unit) (acc : Array Value) :
      Std.HashMap LEdgeId Unit × Array Value := Id.run do
    let mut seen := seen
    let mut acc := acc
    for n in nodes do
      for p in (a.node n).ports do
        for e in (a.port p).outgoingEdges do
          if !seen.contains e then
            seen := seen.insert e ()
            if let some v := serializeEdge a ids e then acc := acc.push v
    return (seen, acc)
  (seenEdges, edges) := collect gr.layerlessNodes seenEdges edges
  for l in gr.layers do
    (seenEdges, edges) := collect (a.layer l).nodes seenEdges edges
  let graphSize := gr.actualSize
  return .obj #[("step", Value.ofNat step), ("processor", .str processorName),
    ("nodes", .arr layerless), ("layers", .arr layersJson), ("edges", .arr edges),
    ("externalNodes", .arr (ids.externalNodes.map (serializeNode a ids))),
    ("graphSize", .obj #[("width", numberOrSpecial graphSize.x), ("height", numberOrSpecial graphSize.y)]),
    ("padding", sides gr.padding.top gr.padding.bottom gr.padding.left gr.padding.right),
    ("offset", xy gr.offset),
    ("size", .obj #[("width", numberOrSpecial gr.size.x), ("height", numberOrSpecial gr.size.y)])]

/-- Renders a snapshot like serde's sorted-key pretty printer and substitutes the sentinels. -/
def render (v : Value) : String :=
  ((v.renderPretty (sortKeys := true)).replace s!"\"{NAN_SENTINEL}\"" "NaN"
    |>.replace s!"\"{POS_INF_SENTINEL}\"" "Infinity"
    |>.replace s!"\"{NEG_INF_SENTINEL}\"" "-Infinity")

/-- `step_{step:03}_{name}.json` with `/`, `\` and spaces replaced by `_`. -/
def fileName (step : Nat) (processorName : String) : String :=
  let shortName := (processorName.splitOn "::").getLast!
  let safeName := shortName.map fun c => if c == '/' || c == '\\' || c == ' ' then '_' else c
  let digits := toString step
  let padded := String.ofList (List.replicate (3 - min 3 digits.length) '0') ++ digits
  s!"step_{padded}_{safeName}.json"

/-- `serialize_lgraph_snapshot(lgraph, step, processor_name, output_dir)`. -/
def writeSnapshot (a : LGraphArena) (g : LGraphId) (step : Nat) (processorName : String) (outputDir : String) : IO Unit := do
  IO.FS.createDirAll outputDir
  IO.FS.writeFile (System.FilePath.mk outputDir / fileName step processorName) (render (snapshot a g step processorName))

/-- Programmatic override of `ELK_TRACE_DIR` (used by `elk batch --trace-dir`, which records one
sub-directory per model like the elk-rs parity runner). `none` falls back to the environment. -/
builtin_initialize traceDirOverride : IO.Ref (Option String) ← IO.mkRef none

/-- `ELK_TRACE_DIR` (or the programmatic override), read fresh on every call. -/
def traceDir : IO (Option String) := do
  match ← traceDirOverride.get with
  | some dir => pure (some dir)
  | none => IO.getEnv "ELK_TRACE_DIR"

/-- Sets (or clears) the trace directory override. -/
def setTraceDirOverride (dir : Option String) : IO Unit := traceDirOverride.set dir

/-- `TRACE_STEP_COUNTER`. -/
builtin_initialize stepCounter : IO.Ref Nat ← IO.mkRef 0
/-- `TRACE_LAYOUT_DEPTH`: nesting depth of layered runs (only the outermost run records). -/
builtin_initialize layoutDepth : IO.Ref Nat ← IO.mkRef 0

/-- `ElkLayered.reset_trace_step_counter()`. -/
def resetStepCounter : IO Unit := stepCounter.set 0

/-- `clear_trace_directory`: removes `step_*.json` files from the trace directory. -/
def clearTraceDirectory : IO Unit := do
  let some dir ← traceDir | return
  let entries ← (System.FilePath.mk dir).readDir <|> pure #[]
  for entry in entries do
    let name := entry.fileName
    if name.startsWith "step_" && name.endsWith ".json" then
      try IO.FS.removeFile entry.path catch _ => pure ()

/-- `prepare_trace_directory_for_run`: clears stale snapshots once per traced run. -/
def prepareTraceDirectoryForRun : IO Unit := do
  if (← traceDir).isNone then return
  if (← stepCounter.get) == 0 then clearTraceDirectory

/-- `TraceLayoutScope::enter`/`Drop`: runs `x` one nesting level deeper, restoring the depth
afterwards (also on exceptions). -/
def withLayoutScope {α : Type} (x : IO α) : IO α := do
  let previous ← layoutDepth.get
  layoutDepth.set (previous + 1)
  if previous == 0 then prepareTraceDirectoryForRun
  try x finally layoutDepth.set previous

/-- `record_trace_snapshot_for_root`: records the root graph of the outermost run. -/
def recordSnapshotForRoot (a : LGraphArena) (g : LGraphId) (processorName : String) : IO Unit := do
  if (← layoutDepth.get) != 1 || (a.graph g).parentNode.isSome then return
  let some dir ← traceDir | return
  let step ← stepCounter.get
  stepCounter.set (step + 1)
  try writeSnapshot a g step processorName dir
  catch e => throw (IO.userError s!"failed to write trace snapshot step={step} proc={processorName}: {e}")

end TraceRecorder

end Elk.Alg.Layered
