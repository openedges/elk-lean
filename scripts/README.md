# scripts

| Script | Purpose |
|--------|---------|
| `build_oracle.sh` | Release build of the elk-rs oracle into `.reference/elk-rs-target` |
| `oracle_layout.sh` | Lay out one JSON model with the oracle (optional phase trace dir) |
| `compare_model_parity_layouts.py` | Semantic layout JSON comparison (copied from elk-rs) |
| `compare_phase_traces.py` | Per-processor trace comparison (copied from elk-rs) |
| `run_model_parity.sh` | Whole-corpus parity run (arrives in Phase 2) |

Environment knobs: `ELK_RS_DIR` (default `../elk-rs`), `ORACLE_TARGET_DIR`,
`ORACLE_RUNNER`.
