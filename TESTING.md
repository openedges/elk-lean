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

# whole corpus
sh scripts/run_model_parity.sh external/elk-models tests/model_parity   # .json + .elkt (converted with `elk convert`; PARITY_INCLUDE_ELKT=0 to skip)
sh scripts/run_trace_parity.sh external/elk-models tests/tmp/trace_corpus   # every model: oracle vs elk-lean step traces (strict order)
sh scripts/run_phase_trace_parity.sh external/elk-models/<model>.elkt tests/tmp/trace_<model>   # one model
sh scripts/compare_bytes.sh tests/model_parity   # byte identity of every model against the oracle files of that run
```

Inputs: the 550 `realworld/*.json` models are used directly; the 898 `.elkt` models are
converted to JSON with `elk convert`. The 550 `.elkg` files are XMI copies of the realworld
graphs; elk-rs does not read them either, so they are not compared. In trace mode the oracle
runner forces the root algorithm to layered (`force_layered_algorithm`); `elk batch --trace-dir`
and `elk layout --force-algorithm` do the same. Expected result: every compared model matches
and is byte-identical (`compare_bytes.sh`; the tolerance-based comparisons hide 1-ulp drifts), one
ticket model fails identically on both sides.

### C. Metadata equivalence

`elk algorithms|options|categories` output compared with the elk-rs
`known_layout_*` JSON (ids, names, descriptions, types, targets, defaults,
dependencies, supported features).

### D. Performance and memory

- `elk bench` runs the 26 synthetic scenarios of elk-rs `perf_benchmark` (same LCG graphs, same
  CSV; `--dump-dir` writes the inputs for parity checks). Full comparison and gate:
  ```sh
  sh scripts/run_perf_benchmark.sh 20 3 tests/perf   # oracle rust_api/rust_native + lean_api, report.md
  ```
  `tests/perf/report.md` lists per-scenario times, the lean/rust ratio and the 5% regression
  gate against `tests/perf/baseline_lean_api.csv` (refresh the baseline after an accepted
  optimisation). Numbers are machine specific; the report records the machine.
- Profiling (macOS): `sh scripts/perf/profile_bench.sh <scenario>`, then
  `scripts/perf/sample_inclusive.py` / `sample_callers.py`; `scripts/perf/scan_generated_c.sh`
  checks the generated C for known traps (see `PLAN.md` 7.1).
- Memory: repeated layouts must not grow RSS, e.g.
  ```sh
  /usr/bin/time -l .lake/build/bin/elk bench --scenarios layered_medium,force_medium --iterations 50 --warmup 0 --output /dev/null
  /usr/bin/time -l .lake/build/bin/elk bench --scenarios layered_medium,force_medium --iterations 500 --warmup 0 --output /dev/null
  ```
  (same maximum resident set size). Corpus runs must not print `PANIC`.

### E. Embedding API (Phase 8)

- `sh scripts/build_ffi.sh --check`: builds `.lake/build/ffi/libelklean.a` (C API
  `plugins/org.eclipse.elk.ffi/include/elk_lean.h`) and a native smoke test whose layout must equal
  `elk layout --sort-keys`, plus the metadata and error paths.

## 3. Release checklist
1. `lake build` and `lake test` clean.
2. Model parity and phase-step trace reports regenerated and recorded in
   `HISTORY.md` and the `AGENTS.md` snapshot.
3. Metadata parity clean.
4. Performance within 5% of the recorded baseline (`scripts/run_perf_benchmark.sh`), memory check
   clean, FFI smoke test (`scripts/build_ffi.sh --check`) passing.
5. `CHANGELOG.md` updated, tag `vX.Y.Z` (see `VERSIONING.md`).
