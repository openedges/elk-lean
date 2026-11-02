# Changelog

All notable changes to elk-lean are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/); versions are aligned
with the ELK release they port (see `VERSIONING.md`).

## [Unreleased]

(nothing yet)

## [0.12.0] - unreleased

First release: a pure Lean 4 port of the Eclipse Layout Kernel 0.12.0 (reference ELK / elkjs
0.12.0, performance and secondary parity oracle elk-rs 0.12.1 at `eb586b6d`). Not yet tagged or
published; the numbers below are the `AGENTS.md` snapshot of 2026-11-02.

### Delivered
- **ELK port**: all layered phases (P1 cycle breaking to P5 edge routing, 59 intermediate
  processors, components, compound graphs, wrapping, self loops) and the other algorithms: force,
  stress, mrtree, radial, rectpacking, spore (overlap removal and compaction), disco,
  topdownpacking, vertiflex. Option metadata (`known_layout_algorithms/options/categories`)
  follows elk-rs; source layout mirrors the Java plugin structure (one Lean file per Java class).
- **CLI** (`elk`): `layout`, `convert` (`.elkt` parser, `.elkt`/`.elkg` to JSON),
  `algorithms|options|categories`, `bench` (the 26 elk-rs `perf_benchmark` scenarios, same CSV),
  `--trace-dir` layered phase traces (step files named after the Java processor classes), `--version`.
- **C API** (`plugins/org.eclipse.elk.ffi/include/elk_lean.h`, `scripts/build_ffi.sh`): JSON in /
  JSON out layout, metadata queries, error reporting, thread registration; native smoke test.
- **Node.js addon** (`plugins/org.eclipse.elk.napi`, Node-API C, worker_threads capable) and the
  **elkjs-compatible npm package** `elk-lean` (`plugins/org.eclipse.elk.js`): native addon with a
  WASM fallback, elkjs API and typings, `workerUrl` worker support with a stack-enlarged
  `worker_threads` Worker for deeply nested or deeply recursive graphs (`workerStackSizeMb`, default
  64 MB), a `threads` option (constructor or per call). JS tests: 72/73 (1 skipped; including the
  three WASM modes, the deep-recursion cases and the thread caps). Addon vs CLI output: 1447/1448
  byte identical.
- **Release build** (`scripts/build_release.sh`): the native CLI and the addon (`build_napi.sh
  --release`) are linked with ThinLTO across the generated C and the GMP-free Lean runtime, with
  profile-guided optimisation from `scripts/build_pgo.sh` (profile under `.reference/pgo/`,
  regenerated, not in git): about 14% less wall time and 17% fewer instructions than the plain
  build on the 26 synthetic scenarios, 20% on the corpus, byte-identical output
  (`docs/build-optimization.md`). The WASM is linked with `-Oz` (6% smaller).
- **GMP-free native runtime**: distributed native artefacts (release CLI, C library bundle, addon)
  link a Lean runtime rebuilt without GMP (`ELK_NO_GMP=1`, `scripts/build_runtime_nogmp.sh`), so
  they contain no LGPL code; output is byte-identical to the toolchain runtime
  (`docs/gmp-licensing.md`).
- **WASM** (`plugins/org.eclipse.elk.wasm`, emscripten 6.0.13, `-sMEMORY64=2`, 4 GB maximum
  memory): Node CJS and browser ESM builds, about 19 MB `.wasm`; realworld corpus 550/550, about
  1.4x the native runtime; an instance that ran out of memory reports a clear error and the npm
  loaders replace it on the next call.
- **`.elkt` conversion API** `convertElkt` on every layer (Lean `Elk.Api.convertElkt`, C
  `elk_lean_convert_elkt(_flags)`, NAPI `convert_elkt`, WASM `backend.convert_elkt`, npm
  `elk.convertElkt(text, { defaults })` in all worker modes): byte-identical to `elk convert` on all
  898 `.elkt` models of elk-models, with the parser's line/column error messages. `elk options
  --choices` adds the enum literals to the option metadata.
- **Browser demo** `plugins/org.eclipse.elk.live`: a server-less replacement for elk-live (ElkGraph
  Web) on the elk-lean WASM Web Worker — Monaco editor with `.elkt` highlighting, parser error
  markers, option/value completion and hovers, sprotty graph view following elk-live's visual
  model, elk-live's four pages (landing `index.html`, `elkgraph.html`, `json.html` with JSON5
  input, `examples.html` with the category table of contents and `?e=` links; the ELK version menu
  is replaced by an engine badge), elk-live-compatible links, SVG/JSON export.
  Static `dist/` (about 26 MB, the WASM compresses to about 2 MB); tested in Chrome 156 (26 tests: 45/45
  examples equal the CLI, headless browser checks of all four pages).
- **Parallel layout** (`docs/parallel-layout.md`, an elk-lean extension): the recursive engine lays
  out independent sibling sub-graphs of a compound graph on Lean tasks and merges them back in
  sibling order, with byte-identical output, traces and error messages in every mode (checked on
  the Java corpus, the phase traces and all random sets with the sequential, default and forced
  settings). Default on for the CLI (`--threads N`, `ELK_LEAN_THREADS`; `elk bench` stays
  sequential) and the addon (`elk_lean_init_threads`, npm `threads`); the WASM build and the Lean
  library stay sequential. Hierarchical ptolemy models: 1.39x in total with 8 threads (large models
  about 2x); connected components of a single layered graph are not parallelised because they share
  one `Random`, as in Java.
- **Development environment**: `mise.toml` pins JDK temurin 21.0.13+9, Maven 3.9.16, Node 24.22.1,
  Rust 1.97.1 and Python 3.14.6 (Lean v4.35.0 comes from elan through `lean-toolchain`) and defines
  `mise run` tasks; `scripts/setup_dev.sh` (`mise run setup`) bootstraps a fresh machine idempotently
  (elan and toolchain, shallow pinned submodules, `lake build` with the 0-warning gate, `lake test`),
  prepares the references on request (`--only oracle|java-baseline|wasm-toolchain`) and reports the
  state of every requirement with `--check`.
- License: EPL-2.0 OR GPL-3.0-or-later, as ELK.

### Verification status
- `lake build`: 0 warnings, 0 errors. `lake test`: 17317 passed, 0 failed (1 skipped: BK oracle
  replay, needs `ELK_BK_ORACLE_TRACES`).
- **Random-input parity against ELK Java** (`scripts/run_random_java_parity.sh`, 12,000 generated
  graphs per run plus option-focused, crossing-minimisation, DisCo, hierarchical model-order and
  feature-coverage variant sets): where both succeed, 5,711 of 5,761 layouts (99.1%) are exact (DisCo set: 5,067 to
  5,073 of 5,104, varying with Java's own run; hierarchical model-order set: 2,175 of 2,271; the
  wrapping / comment box / hypernode / edge-label / spline / BK-alignment set: 5,481/5,652; the
  external-port set (compound-node ports, constraints, labels, cross-hierarchy edges, inside self
  loops): 3,577/3,885, with every Java exception text reproduced except hot-path NPEs whose message HotSpot omits
  (fast throw) and 6 context-dependent ones; the
  rest depend on Java's run context); every input Java rejects fails in elk-lean with Java's
  exception class and message (hot-path exceptions whose message HotSpot omits excepted). Like ELK Java's JSON path, the engine
  does not validate option ranges (out-of-range values reach the algorithm and behave as in Java),
  and object-typed options that Java cannot read from JSON (`labels.labelManager`, manual wrapping
  cuts, ...) are rejected with Java's `IllegalStateException`.
  The remaining differences come from Java's own run context (identity hash codes, `HashSet` and
  `HashMap` orders, thread races, heap-size-dependent errors) and are documented in
  `docs/robustness-random-graphs.md`. To reach this, elk-lean reproduces JDK 21 `TimSort`
  (`Elk.Core.Util.JavaSort`), `HashMap` iteration order (`JavaHashSet`), fdlibm / HotSpot
  `sin`, `cos`, `asin`, `atan2`, `acos`, `log`, and ELK's option defaults per read site.
- **Result parity against unmodified ELK Java 0.12.0** (corpus of 1,998 models, 1,997 compared; 1
  fails identically on both sides): 1,878 exact (tolerance 0). The other 119 depend on the Java
  execution context (see below); against Java with patch 0001 applied all of them match. A baseline
  regenerated on a second machine on 2026-11-02 gives 1,945 exact and 52 drifts, all in that class
  (12 change between Java's forward and reverse runs, 39 match Java with patch 0001, 1 is ticket 213).
- **Layered phase-step traces against ELK Java** (tolerance 0, strict order): 1,817/1,997 match in
  every step. The remaining 180 are caused on the Java side: 170 non-finite intermediate port
  coordinates, 7 self-loop edge orders, 3 partition port orders (details in `HISTORY.md`).
- **Parity against elk-rs** (secondary): model parity 1447/1447 (tolerance 1e-6), strict phase
  trace 1447/1447. Byte identity with elk-rs is 1060/1447; the rest differ only in `-0.0`,
  snapping or values below 4e-12 and are no longer a gate.
- **Performance** vs elk-rs `rust_api` over the 26 synthetic scenarios (sequential `elk bench`): geometric mean 0.71x
  (layered 0.82 to 0.99x, force 0.80 to 0.87x, stress 0.96 to 1.03x, mrtree 0.64 to 0.70x,
  rectpacking 0.57 to 0.65x, radial 0.15 to 0.69x, edge routing 0.84 to 0.96x, crossing
  minimisation 0.91 to 0.95x, hierarchy 0.86 to 0.96x; mrtree and radial follow Java's full
  algorithms and stay at about 0.7x and 0.2 to 0.7x); JSON parse, import, transfer and print
  take about 40% of mrtree_xlarge and 20% of radial_xlarge after the overlay transfer and the
  importer's member masks (the output buffer is sized from the laid-out graph, not 4x the input);
  over the 1,447 corpus models 0.88x in total and 0.83x per model (geometric mean; with 8 threads the
  corpus total is 0.85x of the sequential time and the hierarchical ptolemy models 0.71x; the slowest
  are small interactive models below 0.2 ms, ticket 213 and the model-order example, all below
  about 1.7x after the pure model-order comparators and the pure scanline compaction kernel). Repeated layouts keep RSS flat; the orthogonal router's dependency table is packed
  (24 B per dependency), so a node with 5,000 ports peaks at 648 MB instead of 1.2 GB. 5% regression gate baseline: `tests/perf/baseline_lean_api.csv`.

### Known differences
All remaining differences to unmodified ELK Java 0.12.0 are cases where Java's own result depends
on its run context, plus two deliberate choices; every deterministic difference found by the
corpus and by the random sets (including the feature-coverage set `w`) has been fixed, and the
modules no longer follow elk-rs where it deviated from Java (`docs/robustness-random-graphs.md`
§21 lists the resolution of each former note).
- **Java run context** (not reproducible: no two Java runs agree either): a few `HashMap`/`HashSet`s
  are keyed by objects without their own `hashCode` (self-loop port sides, partition members,
  parallel end-label groups, DisCo extension edges, radial next-level sets), so their order
  depends on identity hash codes handed out earlier in the JVM; exceptions thrown inside DisCo's
  parallel streams lose or wrap their message on worker threads; HotSpot omits the message of
  hot-path exceptions (fast throw); `StackOverflowError` depth and out-of-memory depend on the
  JVM's stack and heap; SPOrE uses `Math.random()` for nodes at the same centre. elk-lean uses the
  enumeration / insertion order, which equals Java with a one-line patch (patch 0001) and equals
  one of the observed Java results (corpus: 170 of 172 varying models; the 119 context-dependent
  corpus models are listed in `HISTORY.md`).
- **Deliberate choices**: Java's Gson writes `NaN` literals into the JSON where a layout produced
  non-finite coordinates; elk-lean writes `null` (same numbers otherwise). For
  `tickets/layered/213_componentsCompaction.elkt` unmodified Java emits NaN coordinates; elk-lean
  keeps a finite result. Inputs on which Java does not terminate (`WEDGE_COMPACTION`,
  `STRETCH_WIDTH` layering on some graphs) are not reproduced.
- **Unreachable code**: `LabelManagementProcessor` cannot be reached through JSON, elkjs or the
  CLI (Java's JSON importer rejects `labels.labelManager`, and so does elk-lean); it is covered by
  unit tests only.
- **topdownpacking** is registered by Java ELK but not by elk-rs/elkjs; elk-lean registers it as
  a Lean extension at rank 100, after the nine elk-rs algorithms (order layered, disco, force,
  mrtree, radial, rectpacking, spore, stress, vertiflex).
- 3 interactive models give different output with and without `--trace-dir`: tracing forces the
  layered algorithm (closed as intended behaviour, see `HISTORY.md`).
- Phase-trace step files are named after the Java processor classes; the elk-rs comparison maps
  the five differently named elk-rs processors through an alias table.

### Not yet available
- Packages are not published (all `package.json` carry `"private": true`). The browser demo's
  GitLab Pages job is a disabled draft (`.pages`); Firefox and Safari were not tested.
- Only macOS arm64 builds have been exercised. Linux (glibc x64/arm64, musl), Windows and
  CI builds are drafted in `.gitlab-ci.yml` but untested, including the GMP-free runtime build on
  Linux and the parallel layout's task manager in the addon. See `docs/release-dry-run-0.12.0.md`.

## Project scaffold (pre-release history)

### ELK Porting
- Project scaffold for the ELK 0.12.0 port (Phase 0): Lake package with one
  library per ELK plugin, C helper shim, CLI and test driver stubs, reference
  submodules pinned to ELK/elkjs 0.12.0, elk-rs 0.12.1 oracle build scripts.
