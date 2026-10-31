# scripts

| Script | Purpose |
|--------|---------|
| `build_oracle.sh` | Release build of the elk-rs oracle into `.reference/elk-rs-target` |
| `oracle_layout.sh` | Lay out one JSON model with the oracle (optional phase trace dir) |
| `compare_model_parity_layouts.py` | Semantic layout JSON comparison (copied from elk-rs) |
| `compare_phase_traces.py` | Per-processor trace comparison (copied from elk-rs) |
| `run_model_parity.sh` | Whole-corpus parity run: oracle vs `elk batch`, merged manifest, report |
| `make_json_manifest.py` | Input manifest from the corpus `.json` models |
| `merge_parity_manifests.py` | Joins the oracle and elk-lean batch manifests for the comparison script |
| `run_random_java_parity.sh` | Random-graph ELK Java parity: generate (`gen_nodesize_graphs.py`) + sanitise (`sanitize_for_java.py`), ELK Java per set with a watchdog, elk-lean (and `--with-oracle` elk-rs) per input with a time limit, outcome/error/layout comparison (`random_java_parity.py`), mismatch classification (`classify_random_parity.py`) → `<out>/report.md`, `details.tsv`, `tests/random_parity/report.md` |
| `gen_option_graphs.py` | Random flat graphs of the non-layered algorithms with random values of their own options ("o" sets of `run_random_java_parity.sh --sets o`: force model, stress dimension, radial compactor/sorter/wedge/translation, mrtree weighting/routing/search order, rectangle packing strategies, VertiFlex strategy, SPOrE processing order) |
| `sanitize_for_java.py` | Copies `gen_nodesize_graphs.py` graphs so that ELK Java's node size calculator validation accepts them ("v" sets; see its docstring for the three changes) |
| `gen_disco_graphs.py` | Random DisCo layout nodes ("c" sets of `run_random_java_parity.sh --sets c`): random components at given positions (labels, ports, edges with sections, the odd self loop and hyperedge), DisCo at the root or on a compound child of a `fixed` root with extensions in both directions, the component layout algorithm (none, `fixed`, `box`, `layered`, `random`, `rectpacking`), `aspectRatio`, spacing, padding, edge thickness, `polyomino.*` |
| `random_java_parity.py` | Driver of `run_random_java_parity.sh` (stages gen, java, lean, rs, report) |
| `classify_random_parity.py` | Groups the random-graph mismatches by origin layout unit (algorithm, difference kinds) and option features with lift |
| `gen_hashset_ops.py` + `java/HashSetOrder.java` | Random `HashSet` operation sequences (tree bins included) replayed on `java.util.HashSet`, printing every iteration order: the differential check of `Elk.Core.Util.JavaHashSet` (fixture `tests/fixtures/spv/hashset_ops*.txt`, suite `spv.javaHashSet`) |
| `java/AsinDump.java` | `Math.asin` bit patterns of the reference JVM for `Elk.Core.Util.javaAsin` (`ELK_ASIN_CASES=<dump> lake test -- --suite spv.javaAsin`) |
| `build_wasm.sh` | WebAssembly build (emscripten) into `plugins/org.eclipse.elk.wasm/dist/`; see that plugin's README |
| `build_runtime_nogmp.sh` | Native Lean runtime rebuilt without GMP (`libleanrt_nogmp.a`), `--check` big-number differential test, `--relink elk` GMP-free CLI; used by `build_ffi.sh`/`build_napi.sh` with `ELK_NO_GMP=1` (see `docs/gmp-licensing.md`) |

Environment knobs: `ELK_RS_DIR` (default `../elk-rs`), `ORACLE_TARGET_DIR`,
`ORACLE_RUNNER`.
