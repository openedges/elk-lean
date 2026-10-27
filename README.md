# elk-lean

Pure Lean 4 port of the [Eclipse Layout Kernel (ELK)](https://www.eclipse.org/elk/)
**0.12.0**, keeping Java-side feature/API parity (same JSON input and output,
same intermediate phase results) while compiling to native code, a Node.js
addon and WebAssembly.

Status: **Phase 0 (project setup) complete** — see [`PLAN.md`](PLAN.md) for the
porting plan and [`HISTORY.md`](HISTORY.md) for progress.

## Repository Layout

- `plugins/org.eclipse.elk.*/` — one Lake library per ELK plugin (`Elk.Graph`,
  `Elk.Core`, `Elk.Json`, `Elk.Alg.Layered`, ...), mirroring the Java/elk-rs
  structure file by file
- `plugins/org.eclipse.elk.cli/` — `elk` command line tool (`lake exe elk`)
- `plugins/org.eclipse.elk.{ffi,napi,wasm,js}/` — C entry points, Node.js addon,
  WebAssembly build and the elkjs-compatible npm package (Phase 8)
- `tests/` — Lean test driver (`lake test`) and parity reports
- `scripts/` — oracle build/run and parity comparison scripts
- `external/` — upstream references as submodules (`elk`, `elkjs`, `elk-models`,
  `elk-live`), pinned to the 0.12.0 release commits; never modified
- `.reference/` — local release build of the elk-rs oracle (git-ignored)

## Prerequisites

- [elan](https://github.com/leanprover/elan) with Lean `v4.35.0` (pinned in
  `lean-toolchain`; `elan` installs it on first use)
- A C compiler (`cc`) for the small helper shim in `plugins/org.eclipse.elk.core/c`
- For parity checks: the sibling checkout `../elk-rs` (0.12.1) built with
  `scripts/build_oracle.sh` (needs Rust 1.97.1 via `mise`), Python 3
- For the JS package (Phase 8): Node.js 24, emscripten

## Setup

```sh
git submodule update --init --recursive
lake build        # all libraries, the CLI and the test driver
lake test         # Lean unit/regression tests
.lake/build/bin/elk --version
```

## Validation

Every change must keep `lake build` free of errors and warnings and `lake test`
green. Layout equivalence against the elk-rs oracle (model parity and
phase-step traces) is described in [`TESTING.md`](TESTING.md).

## Documentation

| Document | Description |
|----------|-------------|
| `PLAN.md` | Porting plan: goals, reference pins, architecture decisions, phases, risks |
| `.rules` (`AGENTS.md`, `CLAUDE.md`) | Working rules, quality gates, current snapshot |
| `HISTORY.md` | Detailed progress log |
| `TESTING.md` | Validation guide |
| `VERSIONING.md` | Version and reference pinning policy |
| `CHANGELOG.md` | Release history |

## License

Eclipse Public License 2.0, with GPL-3.0-or-later as a secondary license when
the EPL-2.0 conditions are met (`EPL-2.0 OR GPL-3.0-or-later`), matching ELK
0.12.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
