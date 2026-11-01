import Elk.Core.Parallel.SubtreeFork
import Elk.Core.Util.ProgressMonitor
/-!
# Parallel sibling layout (elk-lean addition, agent PAR)

`RecursiveGraphLayoutEngine.layoutRecursively` lays out the children of a node one after another
(`for child in children: layoutRecursively child; applyConfiguredNodeScaling child`), like ELK Java.
`layoutSiblings?` runs that loop on Lean `Task`s when the result cannot depend on the order and
returns `none` otherwise (the caller then runs its own sequential loop, unchanged):

1. *Cheap rejections*: fewer than two children with children, a non-null progress monitor (its
   sub-monitors and logs are ordered), thread cap ≤ 1, no free helper slot, no task manager, a
   sequential guard (trace recorder, debug output), fewer than two sub-trees of at least
   `Settings.minWork` elements.
2. *Units and segments*: every child is a unit. `computeOwnership` gives the domains and the
   eligibility test; a unit that fails it (a hierarchy-crossing edge leaves its sub-tree) is a
   barrier: it runs alone, in order, on the merged arena. The runs of eligible units between barriers
   are the segments. A segment with at least two heavy units is split into contiguous chunks of about
   equal work, one per helper slot taken plus one for the calling thread.
3. *Fork*: every chunk gets the arena value as it is before the segment and runs its units in order
   (`runChunk`); the calling thread runs the first chunk itself.
4. *Join in order*: chunk by chunk, `checkChunk`/`mergeChunk` verify that the chunk changed nothing
   outside its domains and copy its domains into the merged arena (created elements renumbered).
   The first unit that threw — in sibling order — ends the loop with its exception, exactly as the
   sequential loop does: earlier chunks have been merged and checked, later chunks are cancelled and
   not waited for (they may not even terminate; in the sequential run they would never have
   started). A write outside the domains makes the whole segment run sequentially on the original
   arena (`fallback`).

Determinism argument and audit: `docs/parallel-layout.md`.
-/
namespace Elk.Core.Parallel

open Elk.Graph Elk.Core.Util

/-- What a chunk reports: the units' results (in order), the first exception (index within the
chunk) and the arena after its units. -/
structure ChunkOutcome (α : Type) where
  results : Array α
  failure : Option (Nat × IO.Error)
  graph : ElkGraph

/-- Runs `units[i:]` in order; stops at the first exception. -/
private partial def runUnits {α : Type} (unit : NodeId → ElkM α) (units : Array NodeId) (i : Nat)
    (acc : Array α) : ElkM (Array α × Option (Nat × IO.Error)) := do
  if h : i < units.size then
    match ← (try (.ok <$> unit units[i]) catch e => pure (.error e) : ElkM (Except IO.Error α)) with
    | .ok r => runUnits unit units (i + 1) (acc.push r)
    | .error e => return (acc, some (i, e))
  else return (acc, none)

/-- Runs the units of one chunk in order on the arena `g`. -/
def runChunk {α : Type} (unit : NodeId → ElkM α) (units : Array NodeId) (g : ElkGraph) : IO (ChunkOutcome α) := do
  let ((results, failure), graph) ← (runUnits unit units 0 (Array.mkEmpty units.size)).run g
  return { results, failure, graph }

/-- Splits `work` (per unit, in order) into `parts` contiguous ranges of about equal sum; returns
the start index of every range (the first is `0`); never an empty range. -/
def balancedCuts (work : Array Nat) (parts : Nat) : Array Nat := Id.run do
  let total := work.foldl (· + ·) 0
  let parts := max 1 (min parts work.size)
  let mut cuts : Array Nat := #[0]
  let mut acc := 0
  for h : i in [0:work.size] do
    -- a cut before unit `i` once the prefix reaches the next share, keeping one unit per later range
    if i > 0 && cuts.size < parts && acc * parts ≥ total * cuts.size && work.size - i ≥ parts - cuts.size then
      cuts := cuts.push i
    acc := acc + work[i]
  -- ranges still missing (all work at the end): cut the tail one unit per range
  while cuts.size < parts do
    cuts := cuts.push (work.size - (parts - cuts.size))
  return cuts

/-- How a segment ended. -/
private inductive SegmentEnd (α : Type) where
  | merged (graph : ElkGraph) (results : Array α)
  | failed (error : IO.Error)
  | fallback

/-- Waits for the chunk tasks in order, checks and merges them (see the module doc). -/
private def joinChunks {α : Type} (orig : ElkGraph) (own : Ownership) (chunkOfUnit : Array Nat)
    (first : ChunkOutcome α) (tasks : Array (Task (Except IO.Error (ChunkOutcome α))))
    (remapResult : Remap → α → α) : IO (SegmentEnd α) := do
  let cancelFrom (k : Nat) : IO Unit := do
    for h : j in [k:tasks.size] do IO.cancel tasks[j]
  let inChunk (c : Nat) (u : Nat) : Bool := chunkOfUnit[u]? == some c
  if let some (_, e) := first.failure then
    cancelFrom 0
    return .failed e
  if !checkChunk orig first.graph own (inChunk 0) then
    cancelFrom 0
    return .fallback
  let mut merged := first.graph
  let mut results := first.results
  for h : t in [0:tasks.size] do
    let outcome ← match ← IO.wait tasks[t] with
      | .ok o => pure o
      | .error e => cancelFrom (t + 1); return .failed e
    if let some (_, e) := outcome.failure then
      cancelFrom (t + 1)
      return .failed e
    match mergeChunk orig outcome.graph merged own (inChunk (t + 1)) with
    | some (m, r) =>
      merged := m
      results := results ++ (if r.isId then outcome.results else outcome.results.map (remapResult r))
    | none =>
      cancelFrom (t + 1)
      return .fallback
  return .merged merged results

/-- Forks the chunks of one segment, joins them and installs the merged arena. `units` are the
segment's units (global unit indices `first + i`), `cuts` the chunk starts. -/
private def runSegmentParallel {α : Type} (unit : NodeId → ElkM α) (remapResult : Remap → α → α)
    (units : Array NodeId) (unitBase : Nat) (cuts : Array Nat) (own : Ownership) (unitCount : Nat) :
    ElkM (Option (Array α)) := do
  let orig ← get
  let chunk (c : Nat) : Array NodeId :=
    units.extract (cuts[c]?.getD units.size) (cuts[c + 1]?.getD units.size)
  -- unit (global index) → chunk
  let mut chunkOfUnit : Array Nat := Array.replicate unitCount cuts.size
  for h : c in [0:cuts.size] do
    for i in [cuts[c]:(cuts[c + 1]?.getD units.size)] do
      chunkOfUnit := chunkOfUnit.set! (unitBase + i) c
  let mut tasks : Array (Task (Except IO.Error (ChunkOutcome α))) := #[]
  for c in [1:cuts.size] do
    let us := chunk c
    tasks := tasks.push (← IO.asTask (do try runChunk unit us orig finally releaseHelper))
  let first ← runChunk unit (chunk 0) orig
  match ← joinChunks orig own chunkOfUnit first tasks remapResult with
  | .merged g results =>
    bumpStats fun s => { s with parallelSegments := s.parallelSegments + 1, chunks := s.chunks + cuts.size }
    set g
    return some results
  | .failed e =>
    bumpStats fun s => { s with failures := s.failures + 1 }
    throw e
  | .fallback =>
    bumpStats fun s => { s with fallbacks := s.fallbacks + 1 }
    return none

/-- Runs units in order on the current arena (barriers, light segments, fallbacks). -/
private def runSequential {α : Type} (unit : NodeId → ElkM α) (units : Array NodeId) : ElkM (Array α) := do
  let mut out : Array α := Array.mkEmpty units.size
  for u in units do out := out.push (← unit u)
  return out

/-- The parallel sibling loop (see the module doc). `unit child` must be the loop body for one child
(lay it out, scale it) and `remapResult` renumber created elements referenced by a unit result.
Returns `none` when the loop should run sequentially (nothing has been changed then). -/
def layoutSiblings? {α : Type} (children : Array NodeId) (monitor : ProgressMonitor)
    (unit : NodeId → ElkM α) (remapResult : Remap → α → α) : ElkM (Option (Array α)) := do
  if children.size < 2 || monitor.state.isSome then return none
  if (← threads) ≤ 1 then return none
  let compound := (← get).nodes
  let nCompound : Nat := children.foldl (init := 0) fun n c =>
    if ((compound[c.idx]?).map (!·.children.isEmpty)).getD false then n + 1 else n
  if nCompound < 2 then return none
  if (← freeHelpers) == 0 then return none
  if ← sequentialForced then return none
  if !(← taskManagerAvailable) then return none
  let minW ← minWork
  let g ← get
  let work := children.map (subtreeWork g ·)
  let heavy (w : Nat) : Bool := w ≥ max minW 1
  if (work.filter heavy).size < 2 then return none
  let own := computeOwnership g children
  -- fewer than two heavy eligible units: the plain loop (nothing to win)
  let nHeavyClosed := (List.range children.size).foldl (init := 0) fun n k =>
    if (own.closed[k]?.getD false) && heavy (work[k]?.getD 0) then n + 1 else n
  if nHeavyClosed < 2 then return none
  -- segments: maximal runs of eligible units; barriers in between
  let mut out : Array α := Array.mkEmpty children.size
  let mut i := 0
  while i < children.size do
    if !(own.closed[i]?.getD false) then
      out := out.push (← unit children[i]!)
      i := i + 1
      continue
    let mut j := i
    while j < children.size && (own.closed[j]?.getD false) do j := j + 1
    let segUnits := children.extract i j
    let segWork := work.extract i j
    let nHeavy := (segWork.filter heavy).size
    let mut done := false
    if nHeavy ≥ 2 then
      let helpers ← acquireHelpers (nHeavy - 1)
      if helpers > 0 then
        -- the owner tables of the arena as it is now (barriers or earlier segments may have
        -- changed it); the segment stays eligible
        let cur ← get
        let own' := if i == 0 then own else computeOwnership cur children
        if (List.range (j - i)).all (fun k => own'.closed[i + k]?.getD false) then
          let cuts := balancedCuts segWork (helpers + 1)
          -- give back the slots the cuts do not use
          for _ in [cuts.size:helpers + 1] do releaseHelper
          match ← runSegmentParallel unit remapResult segUnits i cuts own' children.size with
          | some rs => out := out ++ rs; done := true
          | none => pure ()
        else
          for _ in [0:helpers] do releaseHelper
    if !done then out := out ++ (← runSequential unit segUnits)
    i := j
  return some out

end Elk.Core.Parallel
