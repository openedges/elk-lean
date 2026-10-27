# perf fixtures

`*.input.json`: elk-rs `perf_benchmark.rs` synthetic scenario inputs (`generate_*_json`), produced
by an independent Python transcription of the Rust generators. `elk bench --dump-dir` must
reproduce them byte for byte.

`*.oracle.json`: the oracle layout (`model_parity_layout_runner`, elk-rs `eb586b6d`, pretty,
sorted keys) of each input. `elk layout --pretty --sort-keys` must reproduce them byte for byte.
