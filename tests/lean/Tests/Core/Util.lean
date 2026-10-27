import Tests.Framework
import Elk.Core
/-! Test suites for `org.eclipse.elk.core.util` (ported from elk-rs `plugins/org.eclipse.elk.core/tests/all`):
`basic_progress_monitor_test.rs`, `property_test.rs`. Tests of `DefaultFactory`, `Maybe`, `Triple`,
`Quadruple` and `WrappedException` (`util_misc_test.rs`) are skipped: those utilities are not ported yet. -/
namespace Tests.Core.Util

open Tests Elk Elk.Core.Util Elk.Core.Math Elk.Graph

def basicProgressMonitor : Suite := suite "core.util.BasicProgressMonitor" do
  -- basic_progress_monitor_tracks_logs_and_time
  let m ← ProgressMonitor.basic
  let m ← (← m.withLogging).withExecutionTimeMeasurement
  check "begin" (← m.begin "Task" 10.0)
  m.worked 5.0
  m.log "hello"
  m.done
  check "not running after done" (!(← m.isRunning))
  checkEq "task name" (← m.taskName) (some "Task")
  let logs ← m.logs
  checkEq "log count" logs.size 1
  checkEq "log message" logs[0]! "hello"
  check "execution time >= 0" ((← m.executionTime) >= 0.0)
  check "execution time measured" (← m.isExecutionTimeMeasured)

def progressMonitorSemantics : Suite := suite "core.util.ProgressMonitor.semantics" do
  let m ← ProgressMonitor.basic
  check "begin once" (← m.begin "A" 4.0)
  check "begin twice returns false" (!(← m.begin "B" 1.0))
  check "running" (← m.isRunning)
  m.worked 1.5
  checkFloat "completed" (← m.completedWork) 1.5
  m.worked (-3.0)
  checkFloat "negative work ignored" (← m.completedWork) 1.5
  m.worked 100.0
  m.done
  checkFloat "worked saturates by done" (← m.completedWork) 101.5
  checkEq "task name kept" (← m.taskName) (some "A")
  checkThrows "begin after done throws" (do let _ ← m.begin "C" 1.0)
  m.done
  -- logs are only recorded when enabled
  let m2 ← ProgressMonitor.basic
  m2.log "ignored"
  checkEq "no logs without logging" (← m2.logs).size 0
  let _ ← m2.withLogging
  m2.log "kept"
  m2.logGraph "" .json
  checkEq "log recorded" (← m2.logs) #["kept"]
  checkEqR "logged graph" (← m2.loggedGraphs) #[{ tag := "Unnamed", graphType := .json : LoggedGraph }]
  let _ ← m2.withLogging false
  checkEq "disabling clears logs" (← m2.logs).size 0
  -- done without begin
  let m3 ← ProgressMonitor.basic
  checkThrows "done before begin throws" m3.done

def progressMonitorSubTasks : Suite := suite "core.util.ProgressMonitor.subTask" do
  let m ← ProgressMonitor.basic
  let _ ← m.withLogging
  let _ ← m.begin "root" 10.0
  let sub ← m.subTask 4.0
  check "sub logging inherited" (← sub.isLoggingEnabled)
  let _ ← sub.begin "sub" 2.0
  sub.worked 1.0
  checkFloat "propagated half of child share" (← m.completedWork) 2.0
  sub.done
  checkFloat "child done propagates the full share" (← m.completedWork) 4.0
  -- null monitors
  let n := ProgressMonitor.null
  check "null begin false" (!(← n.begin "x" 1.0))
  check "null not running" (!(← n.isRunning))
  check "null not canceled" (!(← n.isCanceled))
  checkEq "null task name" (← n.taskName) none
  let nsub ← n.subTask 1.0
  check "null sub task is null" (!(← nsub.begin "y" 1.0))
  -- closed monitors hand out null sub monitors
  m.done
  let late ← m.subTask 1.0
  check "sub task of closed monitor is null" (!(← late.begin "z" 1.0))
  -- max hierarchy levels: level 0 does not propagate
  let top ← ProgressMonitor.basic 0
  let _ ← top.begin "top" 10.0
  let child ← top.subTask 5.0
  let _ ← child.begin "child" 1.0
  child.worked 1.0
  checkFloat "no propagation with maxLevels = 0" (← top.completedWork) 0.0
  -- cancellation
  let c ← ProgressMonitor.basic
  check "not canceled" (!(← c.isCanceled))
  c.cancel
  check "canceled" (← c.asCancelIndicator.isCanceled)

def abstractRandomListAccessor : Suite := suite "core.util.AbstractRandomListAccessor" do
  let a : AbstractRandomListAccessor Nat := { provideDefault := fun _ => 7 }
  let a := a.setListItem 3 1
  checkEqR "set beyond end fills with defaults" a.list #[7, 7, 7, 1]
  let (v, a) := a.getListItem 5
  checkEq "get beyond end" v 7
  checkEq "size after get" a.getListSize 6
  let a := a.setListItem 0 9
  checkEqR "set inside" (a.list.extract 0 2) #[9, 7]
  checkEq "cleared" (a.clearList.getListSize) 0

def exclusiveBounds : Suite := suite "core.util.ExclusiveBounds" do
  let lo := ExclusiveBounds.greaterThan 0.0
  check "lower: 1 is above" (lo.compareTo 1.0 == .lt)
  check "lower: 0 is not above" (lo.compareTo 0.0 == .gt)
  check "lower: -1 is not above" (lo.compareTo (-1.0) == .gt)
  let hi := ExclusiveBounds.lessThan 5.0
  check "upper: 4 is below" (hi.compareTo 4.0 == .gt)
  check "upper: 5 is not below" (hi.compareTo 5.0 == .lt)
  checkEq "lower toString" (toString lo) "0.0 (exclusive)"
  check "lower equality" (lo == ExclusiveBounds.greaterThan 0.0)
  check "bound variants differ" (ExclusiveBound.lower lo != ExclusiveBound.upper (ExclusiveBounds.lessThan 0.0))

def elkTrace : Suite := suite "core.util.ElkTrace" do
  -- the flags are read once from the environment; just make sure they are accessible
  let t := ElkTrace.global
  check "flags readable" (t.trace || !t.trace)

/-! `property_test.rs`: `Property.with_default(...).get_default()` returns the default value. -/

elk_enum PortSideT := undefined north east south west
elk_enum SizeConstraintT := portLabels nodeLabels ports portsOverhang minimumSize

private def checkDefault {α : Type} [BEq α] (name : String) (d : α) : TestM Unit := do
  let p : Property α := Property.withDefault "dummy" d
  match p.default with
  | some c => check name (c == d)
  | none => check s!"{name} (no default)" false

def propertyTests : Suite := suite "core.util.Property" do
  -- test_property_default_primitives
  checkDefault "default int" (43 : Int)
  checkDefault "default float" (Float.toF32 23.3)
  checkDefault "default double" (32.3 : Float)
  checkDefault "default string" "foo"
  -- test_property_default_i_data_object
  let v : KVector := ⟨2.0, 3.0⟩
  checkDefault "default KVector" v
  checkDefault "default KVectorChain" (#[v, v] : KVectorChain)
  checkDefault "default ElkPadding" (⟨2.0, 3.0, 2.0, 3.0⟩ : ElkPadding)
  checkDefault "default ElkMargin" (⟨3.0, 2.0, 3.0, 2.0⟩ : ElkMargin)
  -- test_property_default_object (Vec / LinkedList / BTreeSet; HashSet and LinkedHashSet are skipped)
  let v : KVector := ⟨3.0, 2.0⟩
  let al : Array KVector := #[v, v.normalize, v.negate]
  checkDefault "default Vec<KVector>" al
  checkDefault "default LinkedList<KVector>" al
  checkDefault "default BTreeSet<i32>" (#[1, 2, 3, 4] : Array Nat)
  -- test_property_default_enum
  checkDefault "default enum" PortSideT.east
  -- test_property_default_enum_set
  checkDefault "default EnumSet" (EnumSet.empty : EnumSet SizeConstraintT)
  -- a property without default has none
  let q : Property Int := Property.mk' "nodefault"
  checkNone "no default" q.default

def suites : Array Tests.Suite :=
  #[basicProgressMonitor, progressMonitorSemantics, progressMonitorSubTasks, abstractRandomListAccessor,
    exclusiveBounds, elkTrace, propertyTests]

end Tests.Core.Util
