import Elk.Core.Util.ElkTrace
/-!
# Parallel layout settings (elk-lean addition, agent PAR)

Process-wide switches of the structural parallelism in `RecursiveGraphLayoutEngine`
(`Elk.Core.Parallel.SiblingLayout`, `docs/parallel-layout.md`). ELK Java has no counterpart: Java lays
out the children of a node one after another; elk-lean may lay out independent sibling sub-graphs on
Lean `Task`s and merges them back in sibling order, with byte-identical results.

* **Thread cap** (`threadsRef`): `0` = not configured, which is the library default and means
  sequential. Entry points opt in explicitly: the CLI (`elk --threads N`, `ELK_LEAN_THREADS`, default
  `min(hardware threads, 8)`), the C API (`elk_lean_init_threads`) and through it the Node-API addon.
  The WASM build never configures it (single-threaded runtime) and stays sequential. `1` is
  sequential as well.
* **Helper budget** (`busyRef`): at most `cap - 1` helper tasks run at any time, across nested
  levels and across calls (a task abandoned after an earlier sibling failed keeps its slot until it
  ends); the calling thread always works on one chunk itself. A level that gets no helper slot runs
  sequentially.
* **Task manager probe** (`taskManagerAvailable`): `Task.spawn` without a Lean task manager runs the
  task synchronously on the spawning thread (`lean_task_spawn_core`, `if (!g_task_manager) return
  lean_task_pure(apply_1(c, box(0)))`). The probe spawns one dedicated task and compares thread ids, so
  the parallel path is taken only where tasks really run on other threads; the choice is explicit.
* **Work threshold** (`minWorkRef`): a sibling sub-graph is worth a task when it has at least this many
  elements (nodes + ports + edges of the sub-tree); `ELK_LEAN_PAR_MIN_WORK` overrides it (tests force
  `0` to exercise the parallel path on tiny graphs).
* **Sequential guards** (`guardsRef`): predicates registered by plugins that force the sequential path
  while they hold, e.g. the layered phase-step trace recorder (step numbering and files must stay the
  sequential ones) and the `ELK_TRACE_*` debug output (`ElkTrace.global`).
-/
namespace Elk.Core.Parallel

/-- The default minimum number of elements (nodes + ports + edges) of a sibling sub-tree for a task. -/
def defaultMinWork : Nat := 200

/-- The default thread cap: `min(hardware threads, 8)` (at least 1). -/
def defaultMaxThreads : Nat := 8

/-- Configured thread cap (`0` = not configured = sequential). -/
builtin_initialize threadsRef : IO.Ref Nat ← IO.mkRef 0

/-- Helper tasks currently running (taken from the budget `cap - 1`). -/
builtin_initialize busyRef : IO.Ref Nat ← IO.mkRef 0

/-- Minimum sub-tree size for a task (`ELK_LEAN_PAR_MIN_WORK`, read when the cap is configured). -/
builtin_initialize minWorkRef : IO.Ref Nat ← IO.mkRef defaultMinWork

/-- Cached task manager probe (`none` = not probed yet). -/
builtin_initialize taskManagerRef : IO.Ref (Option Bool) ← IO.mkRef none

/-- Sequential guards registered by plugins (see the module doc). -/
builtin_initialize guardsRef : IO.Ref (Array (IO Bool)) ← IO.mkRef #[]

/-- Registers a predicate that forces the sequential path while it returns `true` (called from
`builtin_initialize`, e.g. by the layered `TraceRecorder`). -/
def registerSequentialGuard (guard : IO Bool) : IO Unit := guardsRef.modify (·.push guard)

/-- The hardware thread count (`std::thread::hardware_concurrency`, at least 1). -/
def hardwareThreads : Nat := max 1 (System.Platform.Internal.getHardwareConcurrency ()).toNat

/-- The default cap: `ELK_LEAN_THREADS` when it is a number, else `min(hardware threads, 8)`. -/
def defaultThreads : IO Nat := do
  match (← IO.getEnv "ELK_LEAN_THREADS").bind (·.trimAscii.toString.toNat?) with
  | some n => return max n 1
  | none => return min hardwareThreads defaultMaxThreads

/-- Sets the thread cap (`0` = `defaultThreads`), reads `ELK_LEAN_PAR_MIN_WORK` and forgets the
task manager probe. -/
def configure (threads : Nat) : IO Unit := do
  let n ← if threads == 0 then defaultThreads else pure threads
  threadsRef.set n
  -- probe again: the C API may start the task manager after an earlier call
  taskManagerRef.set none
  if let some w := (← IO.getEnv "ELK_LEAN_PAR_MIN_WORK").bind (·.trimAscii.toString.toNat?) then
    minWorkRef.set w

/-- The configured thread cap (`0` when not configured). -/
def threads : IO Nat := threadsRef.get

/-- Runs `act` with the thread cap `n` (`0` keeps the configured cap) and restores the cap afterwards
(per-call setting of the C API / Node-API addon, whose calls are serialised). -/
def withThreads {α : Type} (n : Nat) (act : IO α) : IO α := do
  if n == 0 then return ← act
  let previous ← threadsRef.get
  threadsRef.set n
  try act finally threadsRef.set previous

/-- Minimum sub-tree size for a task. -/
def minWork : IO Nat := minWorkRef.get

/-- Whether `Task`s run on other threads: one dedicated task compares thread ids (cached). -/
def taskManagerAvailable : IO Bool := do
  if let some b ← taskManagerRef.get then return b
  let tid ← IO.getTID
  let t ← IO.asTask (prio := .dedicated) IO.getTID
  let b := match ← IO.wait t with
    | .ok other => other != tid
    | .error _ => false
  taskManagerRef.set (some b)
  return b

/-- Whether a registered guard, the `ELK_TRACE_*` flags or the debug environment of the random
generators (`CROSSMIN_RANDOM_TRACE`, `ELK_RANDOM_TRACE`) force the sequential path. -/
def sequentialForced : IO Bool := do
  if Elk.Core.Util.ElkTrace.global.anyEnabled then return true
  if (← IO.getEnv "CROSSMIN_RANDOM_TRACE").isSome || (← IO.getEnv "ELK_RANDOM_TRACE").isSome then
    return true
  for g in ← guardsRef.get do
    if ← g then return true
  return false

/-- Helper slots free right now (`cap - 1 - busy`). -/
def freeHelpers : IO Nat := do
  let cap ← threadsRef.get
  if cap ≤ 1 then return 0
  return (cap - 1) - (← busyRef.get)

/-- Takes up to `want` helper slots atomically (`ST.Ref.modifyGet` holds the reference while it
updates); returns how many were taken. -/
def acquireHelpers (want : Nat) : IO Nat := do
  let cap ← threadsRef.get
  if cap ≤ 1 || want == 0 then return 0
  busyRef.modifyGet fun busy =>
    let free := (cap - 1) - busy
    let n := min want free
    (n, busy + n)

/-- Returns one helper slot (at the end of every helper task). -/
def releaseHelper : IO Unit := busyRef.modify (· - 1)

/-- Helper tasks still running (e.g. abandoned after an earlier sibling failed). -/
def helpersRunning : IO Nat := busyRef.get

/-- Counters of the parallel sibling layout (diagnostics, `elk` prints them with `ELK_LEAN_PAR_STATS`). -/
structure Stats where
  /-- Segments laid out in parallel. -/
  parallelSegments : Nat := 0
  /-- Chunks of those segments (tasks + the calling thread's). -/
  chunks : Nat := 0
  /-- Segments that fell back to the sequential loop (a write outside the domains). -/
  fallbacks : Nat := 0
  /-- Segments that ended with a sibling's exception. -/
  failures : Nat := 0
  deriving Inhabited

builtin_initialize statsRef : IO.Ref Stats ← IO.mkRef {}

/-- Updates the counters atomically. -/
def bumpStats (f : Stats → Stats) : IO Unit := statsRef.modify f

/-- The counters. -/
def stats : IO Stats := statsRef.get

end Elk.Core.Parallel
