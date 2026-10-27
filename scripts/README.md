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
| `build_wasm.sh` | WebAssembly build (emscripten) into `plugins/org.eclipse.elk.wasm/dist/`; see that plugin's README |

Environment knobs: `ELK_RS_DIR` (default `../elk-rs`), `ORACLE_TARGET_DIR`,
`ORACLE_RUNNER`.
