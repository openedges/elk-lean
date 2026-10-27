import Elk.Core.Exceptions
import Elk.Core.Util.Java
/-!
# Progress monitors (`org.eclipse.elk.core.util.{IElkProgressMonitor, BasicProgressMonitor, NullElkProgressMonitor, LoggedGraph, LoggedGraphType, IElkCancelIndicator}`)

`ProgressMonitor` is a handle: either the null monitor (`NullElkProgressMonitor`,
no state) or a reference to a mutable `MonitorState` (`BasicProgressMonitor`).
Sub tasks keep a reference to their parent state so that work is propagated
upwards.

Deviations from the Rust port:

* work propagation to the parent uses the *parent's* `currentChildWork`, like
  the Java original (the Rust port reads the child's own field, so it never
  propagates);
* `subMonitors` is always empty (as in Rust): parents do not keep their
  children, which would create an `IO.Ref` cycle;
* log persistence to the file system (debug folders) is not ported, the flag is
  only stored;
* work amounts use single precision rounding (`Float.toF32`) like `f32`.
-/
namespace Elk.Core.Util

/-- `IElkProgressMonitor.UNKNOWN_WORK`. -/
def UNKNOWN_WORK : Float := -1.0

/-- `LoggedGraph.Type`. -/
inductive LoggedGraphType where
  | elk
  | json
  | dot
  | svg
  deriving BEq, Repr, Inhabited

/-- `LoggedGraph`: a graph recorded in a monitor's log (tag and format only). -/
structure LoggedGraph where
  tag : String
  graphType : LoggedGraphType
  deriving BEq, Repr, Inhabited

/-- `IElkCancelIndicator`. -/
structure CancelIndicator where
  isCanceled : IO Bool

/-- `BasicProgressMonitor.INFINITE_HIERARCHY_LEVELS`. -/
def INFINITE_HIERARCHY_LEVELS : Int := -1

/-- Mutable state of a `BasicProgressMonitor`. -/
structure MonitorState where
  nextChildIndex : Nat := 0
  childIndex : Nat := 0
  maxLevels : Int := INFINITE_HIERARCHY_LEVELS
  taskName : Option String := none
  closed : Bool := false
  totalWork : Float := 0.0
  completedWork : Float := 0.0
  currentChildWork : Float := -1.0
  recordLogs : Bool := false
  persistLogs : Bool := false
  logMessages : Array String := #[]
  logGraphs : Array LoggedGraph := #[]
  recordExecutionTime : Bool := false
  startNanos : Option Nat := none
  totalTime : Float := 0.0
  canceled : Bool := false

/-- `IElkProgressMonitor`: `state = none` is the null monitor. -/
structure ProgressMonitor where
  state : Option (IO.Ref MonitorState)
  /-- `getParentMonitor()`: the handle of the parent (children point to parents only). -/
  parent : Option ProgressMonitor := none

namespace ProgressMonitor

/-- `NullElkProgressMonitor`. -/
def null : ProgressMonitor := ⟨none, none⟩

/-- `new BasicProgressMonitor().withMaxHierarchyLevels(levels)`; a negative
number means unlimited levels (the Java/Rust default). -/
def basic (maxHierarchyLevels : Int := INFINITE_HIERARCHY_LEVELS) : IO ProgressMonitor := do
  let r ← IO.mkRef
    ({ maxLevels := if maxHierarchyLevels < 0 then INFINITE_HIERARCHY_LEVELS else maxHierarchyLevels } : MonitorState)
  return ⟨some r, none⟩

/-- Applies `f` to the state of a basic monitor (no-op for the null monitor). -/
private def modifyState (m : ProgressMonitor) (f : MonitorState → MonitorState) : IO Unit := do
  match m.state with
  | none => pure ()
  | some r => r.modify f

/-- Reads the state of a basic monitor. -/
private def getState (m : ProgressMonitor) : IO (Option MonitorState) := do
  match m.state with
  | none => pure none
  | some r => return some (← r.get)

/-- `withMaxHierarchyLevels(levels)`. -/
def withMaxHierarchyLevels (m : ProgressMonitor) (levels : Int) : IO ProgressMonitor := do
  modifyState m fun s => { s with maxLevels := if levels < 0 then INFINITE_HIERARCHY_LEVELS else levels }
  pure m

/-- `withLogging(enabled)`: disabling clears recorded logs. -/
def withLogging (m : ProgressMonitor) (enabled : Bool := true) : IO ProgressMonitor := do
  modifyState m fun s =>
    if enabled then { s with recordLogs := true }
    else { s with recordLogs := false, logMessages := #[], logGraphs := #[] }
  pure m

/-- `withLogPersistence(enabled)`: only stores the flag (no file output). -/
def withLogPersistence (m : ProgressMonitor) (enabled : Bool := true) : IO ProgressMonitor := do
  modifyState m fun s => { s with persistLogs := enabled }
  pure m

/-- `withExecutionTimeMeasurement(enabled)`. -/
def withExecutionTimeMeasurement (m : ProgressMonitor) (enabled : Bool := true) : IO ProgressMonitor := do
  modifyState m fun s => { s with recordExecutionTime := enabled }
  pure m

/-- `BasicProgressMonitor.internalWorked`: records work and propagates it to the parent. -/
private partial def internalWorked (m : ProgressMonitor) (work : Float) : IO Unit := do
  let some r := m.state | return
  let s ← r.get
  if s.totalWork > 0.0 && s.completedWork < s.totalWork then
    r.modify fun s => { s with completedWork := Float.toF32 (s.completedWork + work) }
    match m.parent with
    | some p =>
      let some pr := p.state | return
      let ps ← pr.get
      if ps.currentChildWork > 0.0 && s.maxLevels != 0 then
        internalWorked p (Float.toF32 (work / s.totalWork * ps.currentChildWork))
    | none => pure ()

/-- `begin(name, totalWork)`: returns `false` if the task was already started.
Throws `IllegalStateException` if the task is already done. -/
def begin (m : ProgressMonitor) (name : String) (totalWork : Float) : IO Bool := do
  match m.state with
  | none => pure false
  | some r =>
    let s ← r.get
    if s.closed then Elk.Core.throwIllegalState "The task is already done."
    if s.taskName.isSome then return false
    let now ← if s.recordExecutionTime then some <$> IO.monoNanosNow else pure none
    r.modify fun s => { s with taskName := some name, totalWork := totalWork, startNanos := now }
    return true

/-- `worked(work)`: only positive amounts of work are recorded, and only while open. -/
def worked (m : ProgressMonitor) (work : Float) : IO Unit := do
  match m.state with
  | none => pure ()
  | some r =>
    let s ← r.get
    if work > 0.0 && !s.closed then internalWorked m work

/-- `done()`: completes the remaining work and records the execution time.
Throws `IllegalStateException` if the task has not begun. -/
def done (m : ProgressMonitor) : IO Unit := do
  match m.state with
  | none => pure ()
  | some r =>
    let s ← r.get
    if s.taskName.isNone then Elk.Core.throwIllegalState "The task has not begun yet."
    if s.closed then return
    if s.recordExecutionTime then
      if let some start := s.startNanos then
        let now ← IO.monoNanosNow
        r.modify fun s => { s with totalTime := (now - start).toFloat / 1.0e9 }
    if s.completedWork < s.totalWork then
      internalWorked m (s.totalWork - s.completedWork)
    r.modify fun s => { s with closed := true }

/-- `isRunning()`. -/
def isRunning (m : ProgressMonitor) : IO Bool := do
  return (← getState m).any fun s => s.taskName.isSome && !s.closed

/-- Whether the task has been completed with `done`. -/
def isClosed (m : ProgressMonitor) : IO Bool := do
  return (← getState m).any (·.closed)

/-- `getTaskName()`. -/
def taskName (m : ProgressMonitor) : IO (Option String) := do
  return (← getState m).bind (·.taskName)

/-- Total work given to `begin`. -/
def totalWork (m : ProgressMonitor) : IO Float := do
  return ((← getState m).map (·.totalWork)).getD 0.0

/-- Work completed so far. -/
def completedWork (m : ProgressMonitor) : IO Float := do
  return ((← getState m).map (·.completedWork)).getD 0.0

/-- `subTask(work)`: a child monitor consuming `work` units of this monitor.
A closed monitor yields the null monitor. -/
def subTask (m : ProgressMonitor) (work : Float) : IO ProgressMonitor := do
  match m.state with
  | none => pure null
  | some r =>
    let s ← r.get
    if s.closed then return null
    let newLevels := if s.maxLevels > 0 then s.maxLevels - 1 else s.maxLevels
    let sub ← IO.mkRef
      ({ childIndex := s.nextChildIndex, maxLevels := newLevels,
         recordLogs := s.recordLogs, persistLogs := s.persistLogs,
         recordExecutionTime := s.recordExecutionTime } : MonitorState)
    r.modify fun s => { s with nextChildIndex := s.nextChildIndex + 1, currentChildWork := work }
    return ⟨some sub, some m⟩

/-- `getSubMonitors()`: always empty (see module doc). -/
def subMonitors (_ : ProgressMonitor) : IO (Array ProgressMonitor) := pure #[]

/-- `getParentMonitor()`. -/
def parentMonitor (m : ProgressMonitor) : IO (Option ProgressMonitor) := do
  return m.parent

/-- `isCanceled()`: false unless `cancel` was called. -/
def isCanceled (m : ProgressMonitor) : IO Bool := do
  return (← getState m).any (·.canceled)

/-- Requests cancellation (extension; Java subclasses override `isCanceled`). -/
def cancel (m : ProgressMonitor) : IO Unit := modifyState m fun s => { s with canceled := true }

/-- The monitor as an `IElkCancelIndicator`. -/
def asCancelIndicator (m : ProgressMonitor) : CancelIndicator := ⟨isCanceled m⟩

/-- `isLoggingEnabled()`. -/
def isLoggingEnabled (m : ProgressMonitor) : IO Bool := do
  return (← getState m).any (·.recordLogs)

/-- `isLogPersistenceEnabled()`. -/
def isLogPersistenceEnabled (m : ProgressMonitor) : IO Bool := do
  return (← getState m).any (·.persistLogs)

/-- `log(message)`: recorded only if logging is enabled. -/
def log (m : ProgressMonitor) (message : String) : IO Unit :=
  modifyState m fun s => if s.recordLogs then { s with logMessages := s.logMessages.push message } else s

/-- `getLogs()`. -/
def logs (m : ProgressMonitor) : IO (Array String) := do
  return ((← getState m).map (·.logMessages)).getD #[]

/-- `logGraph(graph, tag, type)`: records the tag (empty tags become `Unnamed`). -/
def logGraph (m : ProgressMonitor) (tag : String) (graphType : LoggedGraphType := .elk) : IO Unit :=
  modifyState m fun s =>
    if s.recordLogs then
      { s with logGraphs := s.logGraphs.push ⟨if tag.isEmpty then "Unnamed" else tag, graphType⟩ }
    else s

/-- `getLoggedGraphs()`. -/
def loggedGraphs (m : ProgressMonitor) : IO (Array LoggedGraph) := do
  return ((← getState m).map (·.logGraphs)).getD #[]

/-- `isExecutionTimeMeasured()`. -/
def isExecutionTimeMeasured (m : ProgressMonitor) : IO Bool := do
  return (← getState m).any (·.recordExecutionTime)

/-- `getExecutionTime()` in seconds. -/
def executionTime (m : ProgressMonitor) : IO Float := do
  return ((← getState m).map (·.totalTime)).getD 0.0

end ProgressMonitor

end Elk.Core.Util
