# elk-lean

Pure Lean 4 port of the [Eclipse Layout Kernel (ELK)](https://www.eclipse.org/elk/)
**0.12.0**, keeping Java-side feature/API parity (same JSON input and output,
same intermediate phase results) while compiling to native code, a Node.js
addon and WebAssembly.

[![CI](https://github.com/openedges/elk-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/openedges/elk-lean/actions/workflows/ci.yml)
[![release](https://github.com/openedges/elk-lean/actions/workflows/release.yml/badge.svg)](https://github.com/openedges/elk-lean/actions/workflows/release.yml)
[![demo](https://github.com/openedges/elk-lean/actions/workflows/pages.yml/badge.svg)](https://openedges.github.io/elk-lean/)

Status: **port complete (Phases 0–6), packaging (Phase 8) and the browser demo (Phase 10)
done, Java parity and optimisation rounds closed; CI and releases on GitHub Actions (Phase 9),
first npm publish pending** — see
[`PLAN.md`](PLAN.md) for the porting plan, [`AGENTS.md`](AGENTS.md) for the current snapshot
and [`HISTORY.md`](HISTORY.md) for progress.

## Repository Layout

- `plugins/org.eclipse.elk.*/` — one Lake library per ELK plugin (`Elk.Graph`,
  `Elk.Core`, `Elk.Json`, `Elk.Alg.Layered`, ...), mirroring the Java/elk-rs
  structure file by file
- `plugins/org.eclipse.elk.cli/` — `elk` command line tool (`lake exe elk`)
- `plugins/org.eclipse.elk.{ffi,napi,wasm,js}/` — C entry points, Node.js addon,
  WebAssembly build and the elkjs-compatible npm package (Phase 8)
- `tests/` — Lean test driver (`lake test`) and parity reports
- `scripts/` — development setup, reference builds, parity and performance scripts
  (`scripts/README.md`)
- `external/` — upstream references as submodules (`elk`, `elkjs`, `elk-models`,
  `elk-live`), pinned to the 0.12.0 release commits; never modified
- `docs/` — design and analysis notes (build optimisation, GMP licensing, parallel layout,
  release dry run, random-graph robustness)
- `mise.toml`, `lean-toolchain` — pinned tool versions and `mise run` tasks (see Setup)
- `.reference/` — generated references, git-ignored and shared by git worktrees: the elk-rs
  oracle build, the ELK Java baseline and Maven cache, emsdk, the Lean sources, the PGO profile
  (`scripts/setup_dev.sh --only oracle|java-baseline|wasm-toolchain`)

## Prerequisites

Every tool version is pinned in a file: `lean-toolchain` (Lean `v4.35.0`, managed by
[elan](https://github.com/leanprover/elan)) and `mise.toml` (JDK, Maven, Node.js, Rust,
Python, managed by [mise](https://mise.jdx.dev)). A C compiler (`cc`) must be present.

| Tool | Version | Needed for |
|------|---------|-----------|
| Lean / Lake | v4.35.0 / 5.0 (`lean-toolchain`, elan) | build, tests |
| cc | any C11 compiler (Apple clang, clang, gcc) | the helper shim in `plugins/org.eclipse.elk.core/c` |
| Python | 3.14.6 (`mise.toml`; any 3.9+ works) | comparison scripts |
| Node.js | 24.22.1 (`mise.toml`) | npm package tests, WASM tests, browser demo |
| Rust | 1.97.1 (`mise.toml`) | elk-rs oracle: performance reference, secondary parity |
| JDK / Maven | temurin 21.0.13+9 / 3.9.16 (`mise.toml`) | ELK Java result baseline |
| emscripten | emsdk 6.0.13 (`.reference/emsdk`) | WASM build only |

## Setup

With mise:

```sh
mise trust && mise install      # the pinned tools above (Lean comes from elan)
mise run setup                  # elan + Lean toolchain, submodules, lake build, lake test
mise run check                  # state of every requirement, changes nothing
```

Without mise, or step by step (`scripts/setup_dev.sh` is idempotent; its header documents
every step and option):

```sh
export PATH=$HOME/.elan/bin:$PATH
sh scripts/setup_dev.sh                 # default steps: tools, elan, submodules, build, test
sh scripts/setup_dev.sh --no-mise       # tools looked up on PATH instead of mise
sh scripts/setup_dev.sh --check         # report only
```

The reference environments of the parity and performance gates are optional steps of the
same script; they live outside git, under `.reference/` and the sibling `../elk-rs`:

```sh
sh scripts/setup_dev.sh --only oracle           # ../elk-rs at the pinned commit + oracle build
sh scripts/setup_dev.sh --only java-baseline    # ELK Java 0.12.0 layouts of the corpus (long)
sh scripts/setup_dev.sh --only wasm-toolchain   # emsdk 6.0.13 + Lean sources (WASM, no-GMP runtime)
```

The same steps by hand:

```sh
git submodule update --init --recursive --depth 1
lake build        # all libraries, the CLI and the test driver
lake test         # Lean unit/regression tests
.lake/build/bin/elk --version
```

## Validation

Every change must keep `lake build` free of errors and warnings and `lake test`
green. Layout equivalence is measured against unmodified ELK Java 0.12.0 (final
results and layered phase-step traces, tolerance 0); elk-rs is the performance
reference and a secondary trace oracle. Procedures are in [`TESTING.md`](TESTING.md),
the current numbers in the snapshot section of [`AGENTS.md`](AGENTS.md).

## Documentation

| Document | Description |
|----------|-------------|
| `PLAN.md` | Porting plan: goals, reference pins, architecture decisions, phases, risks |
| `AGENTS.md` | Working rules, quality gates, current snapshot |
| `HISTORY.md` | Detailed progress log |
| `TESTING.md` | Validation guide |
| `VERSIONING.md` | Version and reference pinning policy |
| `CHANGELOG.md` | Release history |
| `PORTING.md` | Rust/Java to Lean porting conventions (types, monads, properties, enums, numeric semantics, sorting) |
| `docs/` | Design and analysis notes |
| `scripts/README.md`, `tests/README.md` | What each script and test directory is for |

## Install and use

- npm (Node.js addon with a WASM fallback, elkjs-compatible API): `npm install @openedges/elk-lean`
  (`plugins/org.eclipse.elk.js/README.md`).
- Lean: `require «elk-lean» from git "https://github.com/openedges/elk-lean" @ "v0.12.0"` in a
  lakefile (the package is indexed by [Reservoir](https://reservoir.lean-lang.org/)).
- Native CLI and C API: the `elk-lean-<version>-<platform>.tar.gz` bundles of the GitHub Releases
  (`bin/elk`, `lib/libelklean.a` + the GMP-free Lean runtime, `include/elk_lean.h`, `ldflags`).
- Browser demo (elk-live without a server): https://openedges.github.io/elk-lean/

## CI and releases

GitHub Actions (`.github/workflows/`): `ci.yml` on every push (Lean build and tests, GMP-free C API,
Node addon, npm tests on Linux x64 and macOS arm64; WASM; browser demo), `release.yml` on `v*` tags
(native bundles for four platforms, WASM, npm publish, GitHub Release), `pages.yml` for the demo,
`parity.yml` (manual, weekly) for the ELK Java / elk-rs parity and `perf.yml` (manual) for the
benchmark. Release steps: `VERSIONING.md` and `TESTING.md` § 3.

## License

Eclipse Public License 2.0, with GPL-3.0-or-later as a secondary license when
the EPL-2.0 conditions are met (`EPL-2.0 OR GPL-3.0-or-later`), matching ELK
0.12.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
