import Elk.Core
/-!
# Minimal test framework for `lake test`

Suites are plain values; `Tests.Main` runs them all and exits non-zero on any
failure. Float comparisons use an absolute tolerance.
-/
namespace Tests

structure State where
  passed : Nat := 0
  failed : Nat := 0
  failures : Array String := #[]
  current : String := ""

abbrev TestM := StateRefT State IO

structure Suite where
  name : String
  run : TestM Unit

def report (name : String) (ok : Bool) (detail : String := "") : TestM Unit := do
  let cur := (← get).current
  if ok then
    modify fun s => { s with passed := s.passed + 1 }
  else
    let msg := s!"{cur} / {name}{if detail.isEmpty then "" else s!": {detail}"}"
    IO.println s!"FAIL {msg}"
    modify fun s => { s with failed := s.failed + 1, failures := s.failures.push msg }

def check (name : String) (cond : Bool) : TestM Unit := report name cond

def checkEq {α : Type} [BEq α] [ToString α] (name : String) (actual expected : α) : TestM Unit :=
  report name (actual == expected) s!"expected {expected}, got {actual}"

def checkEqR {α : Type} [BEq α] [Repr α] (name : String) (actual expected : α) : TestM Unit :=
  report name (actual == expected) s!"expected {repr expected}, got {repr actual}"

def checkFloat (name : String) (actual expected : Float) (eps : Float := 1e-9) : TestM Unit :=
  let ok := if expected.isNaN then actual.isNaN else (actual - expected).abs <= eps
  report name ok s!"expected {Elk.Core.Util.Float.toShortest expected}, got {Elk.Core.Util.Float.toShortest actual}"

def checkSome {α : Type} (name : String) (v : Option α) : TestM Unit := report name v.isSome "expected some"

def checkNone {α : Type} (name : String) (v : Option α) : TestM Unit := report name v.isNone "expected none"

/-- Checks that an `IO` action throws (any `IO.Error`). -/
def checkThrows (name : String) (action : IO Unit) : TestM Unit := do
  let threw ← (do action; pure false) <|> pure true
  report name threw "expected an exception"

def suite (name : String) (body : TestM Unit) : Suite := ⟨name, body⟩

def runSuites (suites : Array Suite) : IO UInt32 := do
  let mut st : State := {}
  for s in suites do
    st := { st with current := s.name }
    let r ← (do
        try
          s.run
        catch e =>
          report "(suite crashed)" false (toString e)) |>.run st
    st := r.2
  IO.println s!"{st.passed} passed, {st.failed} failed"
  return if st.failed == 0 then 0 else 1

end Tests
