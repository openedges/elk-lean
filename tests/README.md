# tests

- `lean/` — Lean test driver (`lake test`, executable `elktest`): `Tests/Main.lean` lists the suites,
  one module per plugin or topic (`Tests/<Plugin>/*.lean`, `Tests/<Algorithm>.lean`);
  `lake test -- --suite <prefix>` runs a subset. Snapshot (2026-11-02): 17,326 passed, 0 failed,
  1 skipped (BK oracle replay, needs `ELK_BK_ORACLE_TRACES`).
- `fixtures/` — tracked inputs and expected values of the suites: reduced random-parity cases of the
  Java parity rounds (`cov`, `ext`, `gs`, `hmo`, `ledge`, `lm`, `lnode`, `p3java`, `promotion`,
  `rj3`, `robustness`, `spv`, `opt_java_status.tsv`), algorithm fixtures (`disco`, `force`,
  `force_enum`, `mrtree`, `radial`, `rectpacking`, `spore`, `topdownpacking`, `vertiflex`), core /
  JSON / option / section / node-size cases (`core`, `json`, `options`, `sections`, `nodemicro`,
  `perf`), the JDK `TimSort` and Rust `driftsort` differential cases (`timsort/`, `rustsort/`) and
  the `java.util.HashSet` order replays (`spv/hashset_ops*.txt`).
- `ffi/` — `smoke.c`, the native smoke test of the C API (`scripts/build_ffi.sh --check`).
- `runtime/` — `BignumDiff.lean`, the big-number differential test of the GMP-free Lean runtime
  (`scripts/build_runtime_nogmp.sh --check`, `docs/gmp-licensing.md`).
- `model_parity/` — whole-corpus parity against the elk-rs oracle (`scripts/run_model_parity.sh`;
  `report.md` and `diff_details.tsv` tracked, inputs/outputs git-ignored).
- `perf/` — synthetic benchmark report and 5% regression baseline (`report.md`,
  `baseline_lean_api.csv`), `corpus/` (corpus benchmark) and `release/` (release build, own
  baselines); see `perf/README.md`.
- `random_parity/` — `report.md` of `scripts/run_random_java_parity.sh` (random-graph ELK Java
  parity, sets s/v/d/o/p/c/h/w/x).
- `tmp/` — scratch space for ad-hoc parity, trace and setup runs (git-ignored; `scripts/setup_dev.sh`
  writes its logs here).
