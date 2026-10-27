# Testing and Validation Guide

Single entry point for the elk-lean validation flow. Phase 0 defines the
procedures; the parity pipeline becomes operational in Phase 2 (see `PLAN.md`).

## 1. Environment

| Tool | Version | Purpose |
|------|---------|---------|
| Lean / Lake | v4.35.0 / 5.0 (`lean-toolchain`) | build, tests |
| cc (clang) | any C11 | `plugins/org.eclipse.elk.core/c/elk_core_ffi.c` |
| Rust | 1.97.1 (`../elk-rs/rust-toolchain.toml`, via `mise`) | building the elk-rs oracle |
| Python | 3.9+ | comparison scripts |
| Node.js | 24 | JS package tests (Phase 8) |
| emscripten | latest | WASM build (Phase 8) |

`~/.elan/bin` is not on the shell PATH by default in this environment:

```sh
export PATH=$HOME/.elan/bin:$PATH
```

### Oracle

elk-lean is verified against the **elk-rs 0.12.1** checkout in `../elk-rs`
(commit `eb586b6d`), which itself matches Java ELK 0.12.0 on all 1,998 corpus
models (plus three documented, intentional corrections). Build it once:

```sh
sh scripts/build_oracle.sh
# → .reference/elk-rs-target/release/model_parity_layout_runner, perf_benchmark
```

When a JDK and Maven become available, the Java baseline can be regenerated with
elk-rs's `scripts/java_model_parity_trace.sh` and compared three ways.

## 2. Verification Items

### A. Code quality

| Item | Command | Pass criteria |
|------|---------|---------------|
| Build | `lake build` | zero errors and warnings |
| Tests | `lake test` | zero failures |

### B. Layout equivalence (Phase 2 onwards)

| Item | Comparison | Tool |
|------|------------|------|
| Model parity | oracle layout JSON vs Lean layout JSON, semantic, abs tol 1e-6 | `scripts/compare_model_parity_layouts.py` |
| Phase-step trace | per-processor LGraph snapshots, positional, tol 1e-3; node/port storage order compared strictly (`--strict-order`, default in the run scripts) | `scripts/compare_phase_traces.py --batch --strict-order` |

```sh
# single model against the oracle
sh scripts/oracle_layout.sh input.json out/oracle.json out/oracle_trace
ELK_TRACE_DIR=out/lean_trace .lake/build/bin/elk layout input.json -o out/lean.json
python3 scripts/compare_model_parity_layouts.py out/oracle.json out/lean.json
python3 scripts/compare_phase_traces.py out/oracle_trace out/lean_trace

# whole corpus (script arrives in Phase 2)
sh scripts/run_model_parity.sh external/elk-models tests/model_parity   # .json + .elkt (converted with `elk convert`; PARITY_INCLUDE_ELKT=0 to skip)
sh scripts/run_phase_trace_parity.sh external/elk-models/<model>.elkt tests/tmp/trace_<model>   # one model: oracle vs elk-lean step traces
```

Inputs: the 550 `realworld/*.json` models are used directly; `.elkt` models are
converted to JSON by the `elk convert` command once the text format parser is
ported (Phase 6). Until then the oracle side converts them.

### C. Metadata equivalence

`elk algorithms|options|categories` output compared with the elk-rs
`known_layout_*` JSON (ids, names, descriptions, types, targets, defaults,
dependencies, supported features).

### D. Performance and memory

- 26 synthetic scenarios of elk-rs `perf_benchmark` reproduced with the same LCG
  graph generator; record machine model, chip, cores, RAM and OS version with
  every measurement.
- Memory: 1,000 repeated layouts of the same input must not grow RSS; run tests
  with `LEAN_ABORT_ON_PANIC=1` to turn Lean panics into aborts.

## 3. Release checklist
1. `lake build` and `lake test` clean.
2. Model parity and phase-step trace reports regenerated and recorded in
   `HISTORY.md` and the `AGENTS.md` snapshot.
3. Metadata parity clean.
4. Performance within 5% of the recorded baseline.
5. `CHANGELOG.md` updated, tag `vX.Y.Z` (see `VERSIONING.md`).
