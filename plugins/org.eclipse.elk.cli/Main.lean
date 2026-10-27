import Elk.Api

/-- `elk` command line interface (filled in Phase 2). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--version"] | ["-V"] =>
    IO.println s!"elk-lean {Elk.Api.version} (ELK {Elk.Api.elkVersion})"
    return 0
  | ["--ffi-smoke"] =>
    -- temporary: verifies the C helper library is linked
    IO.println s!"{Elk.Core.Util.Float.toShortest 12.0} {Elk.Core.Util.Float.toShortest 0.1} {Elk.Core.Util.Float.toShortest 1e21} {Elk.Core.Util.Float.toShortest 1.5e-7} {Elk.Core.Util.Float.toShortest 1234.5} {Elk.Core.Util.Float.toShortest (-0.0)} {Elk.Core.Util.Float.toShortest 123456789012345680.0} {Elk.Core.Util.strtodUnchecked "0.1"}"
    return 0
  | _ =>
    IO.eprintln "usage: elk --version | --ffi-smoke   (layout commands arrive in Phase 2)"
    return 2
