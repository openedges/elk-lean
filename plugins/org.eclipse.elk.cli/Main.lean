import Elk.Api

/-- `elk` command line interface (layout commands arrive in Phase 2). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--version"] | ["-V"] =>
    IO.println s!"elk-lean {Elk.Api.version} (ELK {Elk.Api.elkVersion})"
    return 0
  | _ =>
    IO.eprintln "usage: elk --version"
    return 2
