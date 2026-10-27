import Elk.Api

/-- Test driver (`lake test`). Test suites are registered here as they are ported. -/
def main : IO UInt32 := do
  let mut failures := 0
  let check (name : String) (ok : Bool) : IO Unit := do
    if ok then IO.println s!"ok   {name}" else IO.println s!"FAIL {name}"
  check "ffi.float.toShortest" (Elk.Core.Util.Float.toShortest 12.0 == "12.0")
  if Elk.Core.Util.Float.toShortest 12.0 != "12.0" then failures := failures + 1
  IO.println s!"{if failures == 0 then "all tests passed" else s!"{failures} failures"}"
  return (if failures == 0 then 0 else 1)
