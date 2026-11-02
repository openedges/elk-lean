# Testing and Validation Guide

Single entry point for the elk-lean validation flow. Phase 0 defines the
procedures; the parity pipeline becomes operational in Phase 2 (see `PLAN.md`).

## 1. Environment

| Tool | Version | Purpose |
|------|---------|---------|
| Lean / Lake | v4.35.0 / 5.0 (`lean-toolchain`) | build, tests |
| cc (clang) | any C11 | `plugins/org.eclipse.elk.core/c/elk_core_ffi.c` |
| Rust | 1.97.1 (`mise.toml`; `../elk-rs/rust-toolchain.toml` pins the same) | building the elk-rs oracle |
| Python | 3.14.6 (`mise.toml`; any 3.9+ works, emsdk needs 3.10+) | comparison scripts |
| Node.js | 24.22.1 (`mise.toml`) | JS package tests, WASM tests, browser demo |
| emscripten | emsdk 6.0.13 (`.reference/emsdk`, `scripts/build_wasm.sh`) | WASM build |
| JDK / Maven | temurin 21.0.13+9 / 3.9.16 (`mise.toml`) | ELK Java result baseline (`scripts/run_java_baseline.sh`) |

`~/.elan/bin` is not on the shell PATH by default in this environment (`mise.toml` adds it through
its `[env]` section when mise is activated):

```sh
export PATH=$HOME/.elan/bin:$PATH
```

The environment is declared in `mise.toml` (JDK, Maven, Node.js, Rust, Python: `mise trust && mise
install`) and `lean-toolchain` (Lean, through elan). `scripts/setup_dev.sh` (`mise run setup`)
installs elan and the toolchain, initialises the submodules, runs `lake build` with the 0-warning
gate and `lake test`; `--check` (`mise run check`) reports the state of every requirement, including
the optional references below, without changing anything; `--only oracle`, `--only java-baseline`
and `--only wasm-toolchain` prepare those references (README "Setup").

### References

**Result reference: ELK Java 0.12.0**, unmodified Maven Central artifacts driven by
`scripts/java/` (`ElkJavaBaseline`, with `ElkPhaseTraceExporter` from elk-rs for the layered
phase-step traces). JDK and Maven come from `mise` (installed on first use):

```sh
mise install java@temurin-21.0.13+9.0.LTS maven@3.9.16
sh scripts/run_java_baseline.sh external/elk-models .reference/java-baseline/corpus            # layouts
sh scripts/run_java_baseline.sh external/elk-models .reference/java-baseline/corpus_reverse --reverse true
sh scripts/run_java_baseline.sh external/elk-models out --include a,b --trace true           # + layered traces
```

`.json` models are laid out as they are; `.elkt`/`.elkg` models are loaded through EMF, get
`RANDOM_SEED` 1 and are exported to JSON by ELK itself, and that JSON is what both ELK Java and
elk-lean lay out. `--reverse` / `--shuffle SEED` run the models in another order: ELK iterates a
few `HashMap`/`HashSet`s keyed by objects without their own `hashCode` (self-loop port sides,
partition members), so for those models its result depends on the identity hash codes handed out
earlier in the JVM, i.e. on the run. `ELK_JAVA_PATCHES=<dir>` compiles patched ELK sources into an
overlay (unsigned jar copies) when the effect of a patch has to be isolated.

**Performance reference (and secondary trace oracle): elk-rs 0.12.1** in `../elk-rs`
(commit `eb586b6d`). Build it once:

```sh
sh scripts/build_oracle.sh
# → .reference/elk-rs-target/release/model_parity_layout_runner, perf_benchmark
```

## 2. Verification Items

### A. Code quality

| Item | Command | Pass criteria |
|------|---------|---------------|
| Build | `lake build` | zero errors and warnings |
| Tests | `lake test` | zero failures |

### B. Layout equivalence (Phase 2 onwards)

| Item | Comparison | Tool |
|------|------------|------|
| **Java result parity** | ELK Java layout JSON vs Lean layout JSON, values compared exactly (abs tol 0; formatting differs by design: Gson `12.0`, elk-lean `12`) and at 1e-6 | `scripts/run_java_parity.sh <java_baseline_dir> <out>` |
| **Java phase-step trace** | ELK Java LGraph after every layered processor vs Lean, tolerance 0, strict node/port order | `scripts/run_java_trace_parity.sh <models> <out>` |
| **Java random-graph parity** | `gen_nodesize_graphs.py` graphs (seeds × 600, as generated "s" and sanitised for Java's node size validation "v"; with `--sets s,v,d,o,p,c,h,w,x` also explicit defaults "d", algorithm option graphs "o", layered crossing minimisation variants "p", DisCo layout nodes "c", hierarchical model order graphs "h", layered wrapping/comment/hypernode/label graphs "w" and external-port graphs "x"): outcome (ok / exception / timeout / stack overflow) on both sides, layouts at tol 0 and 1e-6, exception class + text equality, mismatch classification (`classify_random_parity.py`) | `scripts/run_random_java_parity.sh <out> [--seeds 1-10] [--with-oracle]` → `<out>/report.md`, `details.tsv`, `classification.md`; tracked summary `tests/random_parity/report.md` |
| elk-rs model parity | elk-rs layout JSON vs Lean, semantic, abs tol 1e-6 (`compare_bytes.sh` reports byte identity, which is informational only: elk-rs snaps values within 1e-6 to integers and reads long mantissas with two roundings, elk-lean follows ELK Java) | `scripts/run_model_parity.sh`, `scripts/compare_bytes.sh` |
| elk-rs phase-step trace | per-processor LGraph snapshots, tol 1e-3, strict storage order (`--strict-order`) | `scripts/run_trace_parity.sh` |

```sh
# single model against the oracle
sh scripts/oracle_layout.sh input.json out/oracle.json out/oracle_trace
ELK_TRACE_DIR=out/lean_trace .lake/build/bin/elk layout input.json -o out/lean.json
python3 scripts/compare_model_parity_layouts.py out/oracle.json out/lean.json
python3 scripts/compare_phase_traces.py out/oracle_trace out/lean_trace
# Trace step files are named after the Java processor class (`step_NNN_<Class>.json`). The five processors whose
# elk-rs name differs (Bfs/Dfs/Scc…CycleBreaker, ScConnectivityCycleBreaker, HypernodeProcessor) are matched through
# `_PROCESSOR_ALIASES` in scripts/compare_phase_traces.py.

# ELK Java (result reference)
sh scripts/run_java_parity.sh .reference/java-baseline/corpus tests/tmp/java_parity   # report_exact.md (tol 0), report.md (1e-6)
sh scripts/run_java_trace_parity.sh external/elk-models tests/tmp/java_trace          # generates Java traces, compares every step
sh scripts/run_random_java_parity.sh tests/tmp/random_parity --seeds 1-10 --sets s,v,d,o,p,c,h,w,x   # random graphs (all tracked set kinds), regenerates tests/random_parity/report.md

# ELK Text loader parity: `elk convert` vs ELK Java's JSON export of the same .elkt (898 models; exit 1 on a difference)
sh scripts/run_elkt_loader_parity.sh external/elk-models .reference/java-baseline/corpus tests/tmp/elkt_loader
# ELK Text end to end: `elk layout --defaults X.elkt` vs ELK Java loading the .elkt with elk-live's default sizes
# (`--live-defaults true`; what the elk-live server lays out). The corpus parity above cannot see the Lean text
# loader: there, both sides lay out Java's JSON export.
sh scripts/run_elkt_layout_parity.sh external/elk-models tests/tmp/elkt_layout            # all .elkt
sh scripts/run_elkt_layout_parity.sh external/elk-models tests/tmp/elkt_layout_examples --include examples/

# elk-rs (secondary), whole corpus
sh scripts/run_model_parity.sh external/elk-models tests/model_parity   # .json + .elkt (converted with `elk convert`; PARITY_INCLUDE_ELKT=0 to skip)
sh scripts/run_trace_parity.sh external/elk-models tests/tmp/trace_corpus   # every model: oracle vs elk-lean step traces (strict order)
sh scripts/run_phase_trace_parity.sh external/elk-models/<model>.elkt tests/tmp/trace_<model>   # one model
sh scripts/compare_bytes.sh tests/model_parity   # byte identity of every model against the oracle files of that run
```

`run_model_parity.sh` reuses `<out>/oracle.tsv` + `<out>/oracle/` when both exist and regenerates
the oracle layouts otherwise (`PARITY_REFRESH_ORACLE=1` forces it). The manifests and reports under
`tests/model_parity/` are tracked, the layouts are not, so in a fresh git worktree run the whole
corpus into a new directory (e.g. `tests/tmp/model_parity`) and read `compare errors` in the report,
not only the "no diffs" tail. In a worktree pass the Java baseline directory as an absolute path.

Inputs: the 550 `realworld/*.json` models are used directly; the 898 `.elkt` models are
converted to JSON with `elk convert`. The 550 `.elkg` files are XMI copies of the realworld
graphs; elk-rs does not read them either, so they are not compared. In trace mode the oracle
runner forces the root algorithm to layered (`force_layered_algorithm`); `elk batch --trace-dir`
and `elk layout --force-algorithm` do the same. Expected result: every compared model matches
within 1e-6 and every trace step matches strictly; one ticket model fails identically on both
sides. Exact (tolerance 0) agreement is checked against ELK Java, not against elk-rs.

Random-graph Java parity (`scripts/run_random_java_parity.sh`, driver `scripts/random_java_parity.py`):
seed `k` writes `gen/s<k>` = `gen_nodesize_graphs.py <dir> <count> k` (the generator's seed
semantics, so seed `k` reproduces agent HX's set `k`) and `gen/v<k>` = the same graphs through
`scripts/sanitize_for_java.py` (ports without a side get one from their id's CRC32; port label
placements with more than one of `ALWAYS_SAME_SIDE`/`ALWAYS_OTHER_SAME_SIDE`/`SPACE_EFFICIENT` lose
`SPACE_EFFICIENT`, and the deprecated `SPACE_EFFICIENT_PORT_LABELS` size option is dropped where it
would bring it back — Java rejects about 80% of the "s" graphs in its node size calculator, which
elk-lean and elk-rs do not validate). ELK Java runs one JVM per set (`ElkJavaBaseline`, prebuilt
classes from `.reference/java-baseline/`, compiled through `run_java_baseline.sh` when missing or with
`RANDOM_PARITY_JAVA_REBUILD=1`); a watchdog kills a JVM whose manifest makes no progress for
`--java-timeout` seconds (default 60), records that model as `timeout` and restarts on the rest; a
per-set alarm (`--java-set-timeout`, 1800 s) records everything left as `timeout`. elk-lean runs
`elk layout --pretty --sort-keys` once per input (`--jobs` 3, `--timeout` 15 s; `Stack overflow
detected` = overflow; `elk batch` cannot be used because a stack overflow aborts the whole process).
`--with-oracle` adds elk-rs per input (`rs_vs_lean`: elk-rs equals elk-lean within 1e-6, i.e. the
difference is inherited from elk-rs). Stages already present in `<out>` are reused (`--force` reruns,
`--stages lean,report` after deleting `<out>/lean` re-evaluates a new binary against the same Java
results). Default seeds 1–10: all 10 seeds (12,000 inputs) take about 4 minutes on an 8-core Mac
(Java ≈ 3 min with two JVMs next to the Lean processes; the report and classification add a few minutes) plus about 15 minutes for `--with-oracle`
(elk-rs hangs on about 140 inputs until the time limit). `match_class` in `details.tsv`: `exact`,
`tol1e-6`, `drift:<category>`, `error_equal` (class + text), `error_wrapped` (equal after the
pre-RJ2 API wrapper), `error_class_equal`, `error_differs`, `<x>_both`, `outcome:<lean>/<java>`.
`classify_random_parity.py` attributes every difference to the deepest layout unit (one algorithm
invocation, layered `INCLUDE_CHILDREN` graphs merged into their root) whose own results differ and
groups the mismatches by that origin's algorithm and difference kinds (flags `NML`, `DEF`, `SEC`, `LNODE`, `LEDGE`, `LPOS`, `POS`), with option feature lifts. Set kind `d` (`--sets s,v,d`, experiment) = `v` plus ELK Java's algorithm specific option defaults written explicitly (`sanitize_for_java.py --explicit-defaults`); first results and hypotheses: `docs/robustness-random-graphs.md` section 8. Set kind `o` (`--sets o`, `scripts/gen_option_graphs.py`) = flat graphs of the non-layered algorithms with random values of their own options (force model, stress dimension, radial compactor/sorter/wedge/translation, mrtree weighting/routing/search order, rectangle packing strategies, VertiFlex strategy, SPOrE processing order); it covers the option parsers and strategy branches that the `s`/`v` graphs never select. Set kind `p` (`--sets p`, `scripts/gen_p3_graphs.py`, agent P3J) = the layered roots of `v<k>` with random crossing minimisation and layering options (strategy LAYER_SWEEP/MEDIAN_LAYER_SWEEP/INTERACTIVE/NONE, greedy switch type and threshold, model order strategy/influences/`portModelOrder`, `forceNodeModelOrder`, thoroughness, random seed, semi-interactive, port sorting, node promotion, interactive reference point; positions and sections with bend points for interactive runs), seed `k` (about 180 graphs per seed; generation is marked done by `gen/.p<k>.done`). Set kind `c` (`--sets c`, `scripts/gen_disco_graphs.py`, agent DIS) = DisCo layout nodes (the root, or a compound child of a `fixed` root with extensions in both directions) with random components and DisCo options (component layout algorithm, aspect ratio, spacing, padding, edge thickness, `polyomino.*`); results in `docs/robustness-random-graphs.md` section 17. Set kind `h` (`--sets h`, `scripts/gen_hierarchical_mo_graphs.py`, agents GS/HMO) = hierarchical (`INCLUDE_CHILDREN`) layered graphs of two or three levels with model order options (cycle breaking, layering, node promotion, `considerModelOrder.*`) on the root and/or compound children, `NO_LAYOUT` nodes (also compound ones, with and without `ALGORITHM`), `noModelOrder`, cycle breaking group ids, layer constraints, self loops and hierarchy-crossing edges; graph k of a seed does not depend on `--count` (the 600 graphs of seed k are the first 600 of agent GS's 2,000), about 62 % of the inputs end in an exception on both sides (edge "could not be found", model order layerer requirements, ...) whose text is compared; seeds 1–10 (6,000 inputs) take about 1 minute of Java and 70 seconds of Lean; results in `docs/robustness-random-graphs.md` sections 19 and 20 (about 4–7 % of the layouts depend on the JVM run context in ELK Java itself, mostly the self-loop processing order; check a suspected case with fresh JVMs and `-XX:+UnlockExperimentalVMOptions -XX:hashCode=N`). Set kind `w` (`--sets w`, `scripts/gen_wrapping_graphs.py`, agent COV) = layered graphs with the features no other set reaches: graph wrapping (`wrapping.strategy` SINGLE_EDGE/MULTI_EDGE, cutting ARD/MSD/MANUAL, MSD freedom, correction factor, additional edge spacing, multi-edge improvements, distance penalty, validify strategy; aspect ratios including `0`, negative and huge values; path-like graphs), comment boxes (attached to a node or to a port on each side, to two nodes, chained, unattached), hypernodes, edge labels (inline, HEAD/CENTER/TAIL, side selection, center label placement strategy, several labels per edge, labels on self loops), node and port label placements, spline routing (CONSERVATIVE/SLOPPY, sloppy layer spacing factor), BK fixed alignments and edge straightening, `mergeEdges`/`mergeHierarchyEdges` (a compound child with `INCLUDE_CHILDREN` in some graphs), thoroughness, edge thickness, and in about 3.5 % of the graphs one of the `OBJECT` options without `IDataObject` class that ELK Java's JSON importer rejects (`wrapping.cutting.cuts`, `wrapping.validify.forbiddenIndices`, `labels.labelManager`, `cmEnforcedGroupOrders`: `IllegalStateException: IDataType class expected for layout option …`, so manual cuts and label managers cannot be set from JSON); graph k of a seed does not depend on `--count`; seeds 1–10 × 600 take about 50 s of Java and 30 s of Lean; `STRETCH_WIDTH` layering is left out because it does not terminate on many of these graphs in Java and Lean alike; results in `docs/robustness-random-graphs.md` section 21 (the remaining differences depend on the JVM run context: the identity-hash order of `PortSide` keys in `SelfHyperLoop`'s `ArrayListMultimap` and of `LEdge` keys in `EndLabelSorter`'s `HashMap`; probe a suspected case by laying it out after different predecessors in one JVM). Set kind `x` (`--sets x`, `scripts/gen_external_port_graphs.py`, agent EXT) = layered graphs that mix the external-port features: compound nodes of two or three levels whose ports sit on all four sides, `portConstraints` FREE/FIXED_SIDE/FIXED_ORDER/FIXED_RATIO/FIXED_POS/UNDEFINED on parents and children, explicit `port.side`/`port.index`/`port.borderOffset`/`port.anchor`, port labels with `portLabels.placement` and `portLabels.treatAsGroup`, `portAlignment.*`, `spacing.portPort`, `spacing.portsSurrounding`, `padding`, node size constraints and options, hierarchy handling INCLUDE_CHILDREN/SEPARATE_CHILDREN/INHERIT mixed across levels with cross-hierarchy edges (inner node → parent port → outside node, edges spanning two or three levels, edges from/to the external ports, between two external ports, a few hyperedges; listed in the lowest common ancestor, the root or the source's parent), inside self loops (`insideSelfLoops.activate`/`.yo`), interactive layouts with preset node and external port positions, all directions, ORTHOGONAL/POLYLINE/SPLINES routing, `allowNonFlowPortsToSwitchSides`, `feedbackEdges`, `mergeHierarchyEdges`, `hierarchicalSweepiness` (also outside [-1, 1]), `considerModelOrder.*`, post compaction, and compound children laid out by force/mrtree/rectpacking under a layered parent; degenerate values on purpose (zero-size ports and nodes, ports outside their node, negative offsets/indexes); about 4 % of the graphs keep the combinations Java rejects (invalid port label placements, unsided ports under a non-layered algorithm, hyperedges). Graph k of a seed does not depend on `--count`; seeds 1–10 × 600 take about 1 minute of Java and 1 minute of Lean; about 35 % of the inputs end in an exception on both sides. Results in `docs/robustness-random-graphs.md` section 22: the remaining layout differences depend on the JVM run context (self-loop side order, as in set `w`) or follow non-finite values in ELK Java (`FIXED_RATIO` external ports of a compound node of width or height `0`: Java divides by `0`; elk-lean keeps the position, see §22).
The default `--sets s,v` stays fast; the tracked report `tests/random_parity/report.md` is published from the full run `--sets s,v,d,o,p,c,h,w,x`. elk-lean reports a stack overflow that ELK Java would hit in a recursion that cannot end (for example mrtree `NodePlacer.secondWalk` on a node that is its own right sibling, or the Coffman–Graham / longest path layering DFS on a cycle that a model order cycle breaker left) as `java.lang.StackOverflowError`; the driver counts that as `overflow` like Java's own.

Differential inputs for the node size / port label cell system (ports with and without labels,
every size constraint/option combination, port label placements, hierarchy, several algorithms):
`python3 scripts/gen_nodesize_graphs.py <dir> 600 7`, then lay the graphs out with the binary under
review and with a reference binary and `cmp` the `--pretty --sort-keys` outputs (use a per-graph
time limit: with seed 7, `g0054.json` makes both elk-lean and the elk-rs oracle loop, see
`HISTORY.md`).

Sorting algorithms (exact ports whose comparison order matters for inconsistent or throwing
comparators):

| Item | Reference | Tool |
|------|-----------|------|
| `Elk.Core.Util.JavaSort` (`javaSortBy`, OpenJDK 21 `java.util.TimSort`) | JDK 21 `Collections.sort`: 13,767 cases (sizes 0..5,000, 13 comparator kinds incl. random/asymmetric/constant, throwing at the k-th call and on an "undefined" element), identical outcome (sorted / `IllegalArgumentException` / comparator exception), comparator call sequence and permutation | `sh scripts/run_timsort_diff.sh [out_dir]` (javac + `lake test -- --suite core.util.JavaSort.full`); 627-case subset in `lake test` (`tests/fixtures/timsort/cases.jsonl`, regenerate with `--fixture`) |
| `Elk.Core.Util.RustSort` (`rustSortBy`, Rust 1.97.1 driftsort) | Rust 1.97.1 `slice::sort_by` (10,984 cases, see `HISTORY.md` C1) | fixture subset in `lake test` (`tests/fixtures/rustsort/cases.json`) |

`ELK_TIMSORT_BENCH=1 lake test -- --suite core.util.JavaSort.bench` prints `javaSortBy` vs
`stableSort` timings on 1k / 100k `Float` keys. `lake test -- --suite <prefix>` runs only the
suites whose name starts with `<prefix>`.

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
- Corpus benchmark (every model of a parity manifest, `--mode models` on both sides):
  ```sh
  sh scripts/run_corpus_benchmark.sh 3 1 tests/perf/corpus   # needs tests/tmp/model_parity/inputs.tsv from run_model_parity.sh
  ```
  `tests/perf/corpus/report.md` gives the totals, the per-model ratio distribution and the slowest
  models (`compare_perf.py --corpus`); the 5% gate applies to the total only, because sub-millisecond
  models are too noisy per model. Run it on a quiet machine: under load the small models' ratios
  swing by 2x between runs.
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
- GMP-free runtime (release artefacts, `docs/gmp-licensing.md`): `sh scripts/build_runtime_nogmp.sh
  --check --relink elk` (big-number differential test GMP vs Lean's own implementation, relinked CLI
  in `.lake/build/runtime-nogmp/bin/elk`), `ELK_NO_GMP=1 sh scripts/build_ffi.sh --check`,
  `ELK_NO_GMP=1 sh scripts/build_napi.sh`; the relinked CLI must give byte-identical corpus layouts
  and `nm <artefact> | grep -c __gmp` must print 0 for the CLI, the smoke binary and the addon.
- Parallel layout (`docs/parallel-layout.md`): the CLI lays out independent sibling sub-graphs on
  Lean tasks by default. The sequential mode (`ELK_LEAN_THREADS=1`), the default and the forced mode
  (`ELK_LEAN_PAR_MIN_WORK=0`, every eligible sibling on a task) must give byte-identical layouts and
  error texts: run `scripts/run_java_parity.sh` once per mode into separate directories and compare
  the md5 of their `*.json` files; `ELK_LEAN_PAR_STATS=1` prints the number of parallel segments,
  fallbacks and failures. `lake test -- --suite parallel` runs the unit tests (ownership, merge,
  differential, failure order).

## 3. Release checklist
1. `lake build` and `lake test` clean.
2. ELK Java result parity (exact) and Java phase-step trace parity regenerated, the models whose
   Java result is context-dependent listed, elk-rs parity/byte identity regenerated; all recorded
   in `HISTORY.md` and the `AGENTS.md` snapshot.
3. Metadata parity clean.
4. Performance within 5% of the recorded baseline (`scripts/run_perf_benchmark.sh`), memory check
   clean, FFI smoke test (`scripts/build_ffi.sh --check`) passing in both runtime modes, release
   artefacts built with `ELK_NO_GMP=1` and free of `__gmp` symbols (section 2.E).
5. `CHANGELOG.md` updated, tag `vX.Y.Z` (see `VERSIONING.md`).
