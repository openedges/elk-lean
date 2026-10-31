# Changelog

All notable changes to elk-lean are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/); versions are aligned
with the ELK release they port (see `VERSIONING.md`).

## [Unreleased]

(nothing yet)

## [0.12.0] - unreleased

First release: a pure Lean 4 port of the Eclipse Layout Kernel 0.12.0 (reference ELK / elkjs
0.12.0, performance and secondary parity oracle elk-rs 0.12.1 at `eb586b6d`). Not yet tagged or
published; the numbers below are the `AGENTS.md` snapshot of 2026-11-01.

### Delivered
- **ELK port**: all layered phases (P1 cycle breaking to P5 edge routing, 59 intermediate
  processors, components, compound graphs, wrapping, self loops) and the other algorithms: force,
  stress, mrtree, radial, rectpacking, spore (overlap removal and compaction), disco,
  topdownpacking, vertiflex. Option metadata (`known_layout_algorithms/options/categories`)
  follows elk-rs; source layout mirrors the Java plugin structure (one Lean file per Java class).
- **CLI** (`elk`): `layout`, `convert` (`.elkt` parser, `.elkt`/`.elkg` to JSON),
  `algorithms|options|categories`, `bench` (the 26 elk-rs `perf_benchmark` scenarios, same CSV),
  `--trace-dir` layered phase traces, `--version`.
- **C API** (`plugins/org.eclipse.elk.ffi/include/elk_lean.h`, `scripts/build_ffi.sh`): JSON in /
  JSON out layout, metadata queries, error reporting, thread registration; native smoke test.
- **Node.js addon** (`plugins/org.eclipse.elk.napi`, Node-API C, worker_threads capable) and the
  **elkjs-compatible npm package** `elk-lean` (`plugins/org.eclipse.elk.js`): native addon with a
  WASM fallback, elkjs API and typings, `workerUrl` worker support with a stack-enlarged
  `worker_threads` Worker for deeply nested or deeply recursive graphs (`workerStackSizeMb`, default
  64 MB). JS tests: 56/56 (including the three WASM modes and the deep-recursion cases). Addon vs
  CLI output: 1447/1448 byte identical.
- **GMP-free native runtime**: distributed native artefacts (release CLI, C library bundle, addon)
  link a Lean runtime rebuilt without GMP (`ELK_NO_GMP=1`, `scripts/build_runtime_nogmp.sh`), so
  they contain no LGPL code; output is byte-identical to the toolchain runtime
  (`docs/gmp-licensing.md`).
- **WASM** (`plugins/org.eclipse.elk.wasm`, emscripten 6.0.13, `-sMEMORY64=2`, 4 GB maximum
  memory): Node CJS and browser ESM builds, about 19 MB `.wasm`; realworld corpus 550/550, about
  1.4x the native runtime; an instance that ran out of memory reports a clear error and the npm
  loaders replace it on the next call.
- License: EPL-2.0 OR GPL-3.0-or-later, as ELK.

### Verification status
- `lake build`: 0 warnings, 0 errors. `lake test`: 17122 passed, 0 failed (1 skipped: BK oracle
  replay, needs `ELK_BK_ORACLE_TRACES`).
- **Random-input parity against ELK Java** (`scripts/run_random_java_parity.sh`, 12,000 generated
  graphs per run plus option-focused, crossing-minimisation, DisCo and hierarchical model-order
  variant sets): where both succeed, 5,711 of 5,761 layouts (99.1%) are exact (DisCo set: 5,067 to
  5,073 of 5,104, varying with Java's own run; hierarchical model-order set: 2,175 of 2,271, the
  rest depend on Java's run context); every input Java rejects fails in elk-lean with Java's
  exception class and message (hot-path exceptions whose message HotSpot omits excepted). Like ELK Java's JSON path, the engine
  does not validate option ranges (out-of-range values reach the algorithm and behave as in Java).
  The remaining differences come from Java's own run context (identity hash codes, `HashSet` and
  `HashMap` orders, thread races, heap-size-dependent errors) and are documented in
  `docs/robustness-random-graphs.md`. To reach this, elk-lean reproduces JDK 21 `TimSort`
  (`Elk.Core.Util.JavaSort`), `HashMap` iteration order (`JavaHashSet`), fdlibm / HotSpot
  `sin`, `cos`, `asin`, `atan2`, `acos`, `log`, and ELK's option defaults per read site.
- **Result parity against unmodified ELK Java 0.12.0** (corpus of 1,998 models, 1,997 compared; 1
  fails identically on both sides): 1,878 exact (tolerance 0). The other 119 depend on the Java
  execution context (see below); against Java with patch 0001 applied all of them match.
- **Layered phase-step traces against ELK Java** (tolerance 0, strict order): 1,817/1,997 match in
  every step. The remaining 180 are caused on the Java side: 170 non-finite intermediate port
  coordinates, 7 self-loop edge orders, 3 partition port orders (details in `HISTORY.md`).
- **Parity against elk-rs** (secondary): model parity 1447/1447 (tolerance 1e-6), strict phase
  trace 1447/1447. Byte identity with elk-rs is 1060/1447; the rest differ only in `-0.0`,
  snapping or values below 4e-12 and are no longer a gate.
- **Performance** vs elk-rs `rust_api` over the 26 synthetic scenarios: geometric mean 0.75x
  (layered 0.82 to 0.99x, force 0.80 to 0.87x, stress 0.96 to 1.03x, mrtree 0.64 to 0.70x,
  rectpacking 0.57 to 0.65x, radial 0.15 to 0.69x, edge routing 0.84 to 0.96x, crossing
  minimisation 0.91 to 0.95x, hierarchy 0.86 to 0.96x; mrtree and radial follow Java's full
  algorithms and stay at about 0.7x and 0.2 to 0.7x); JSON parse, import, transfer and print
  take about 40% of mrtree_xlarge and 20% of radial_xlarge after the overlay transfer;
  over the 1,447 corpus models 0.98x in total and 0.95x per model (geometric mean; the slowest
  are a 0.16 ms interactive model at 1.71x, ticket 213 at 1.64x and the model-order example at
  1.49x). Repeated layouts keep RSS flat; the orthogonal router's dependency table is packed
  (24 B per dependency), so a node with 5,000 ports peaks at 648 MB instead of 1.2 GB. 5% regression gate baseline: `tests/perf/baseline_lean_api.csv`.

### Known differences
- **119 context-dependent models**: ELK Java iterates a few `HashMap`/`HashSet`s keyed by objects
  without their own `hashCode` (self-loop port sides, partition members), so its result depends
  on identity hash codes handed out earlier in the JVM. elk-lean uses the enumeration order
  (patch 0001 for Java); of 172 models whose Java result varies between runs, 170 equal one of
  the observed Java results. Models listed in `HISTORY.md`.
- **ticket 213** (`tickets/layered/213_componentsCompaction.elkt`): unmodified Java emits NaN
  coordinates; elk-lean keeps a finite result on purpose.
- **topdownpacking** is registered by Java ELK but not by elk-rs/elkjs; elk-lean registers it as
  a Lean extension at rank 100, after the nine elk-rs algorithms (order layered, disco, force,
  mrtree, radial, rectpacking, spore, stress, vertiflex).
- **Behaviours inherited from elk-rs where it deviates from Java** (recorded as "oracle
  quirks" (오라클 특이점) rows in `HISTORY.md`): `NodePromotion` Nikolov strategies are no-ops (only the two
  model-order strategies are implemented); `BreakingPointInserter.applyCuts` index counting for
  the second and later cuts; vertiflex `considerNodeModelOrder` panics for nodes with exactly two
  children in elk-rs; enum options without a parser (`elk.force.model`, `elk.stress.dimension`,
  vertiflex `layoutStrategy`) ignore their JSON string value as in elk-rs; spore/overlap
  handlers iterate sets in insertion order where elk-rs is nondeterministic. The result
  reference remains ELK Java; wherever these differ from Java the Java comparison column of
  the corpus run is authoritative.
- 3 interactive models give different output with and without `--trace-dir`: tracing forces the
  layered algorithm (closed as intended behaviour, see `HISTORY.md`).

### Not yet available
- Packages are not published (all `package.json` carry `"private": true`).
- Only macOS arm64 builds have been exercised. Linux (glibc x64/arm64, musl), Windows and
  CI builds are drafted in `.gitlab-ci.yml` but untested, including the GMP-free runtime build on
  Linux. See `docs/release-dry-run-0.12.0.md`.

## Project scaffold (pre-release history)

### ELK Porting
- Project scaffold for the ELK 0.12.0 port (Phase 0): Lake package with one
  library per ELK plugin, C helper shim, CLI and test driver stubs, reference
  submodules pinned to ELK/elkjs 0.12.0, elk-rs 0.12.1 oracle build scripts.
