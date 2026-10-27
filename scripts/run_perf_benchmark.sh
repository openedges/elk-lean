#!/bin/sh
# Synthetic performance benchmark: elk-rs oracle `perf_benchmark` (rust_api, rust_native) vs
# `elk bench` (lean_api) on the same 26 LCG scenarios, then `compare_perf.py` writes the report.
#   sh scripts/run_perf_benchmark.sh [iterations=20] [warmup=3] [out_dir=tests/perf]
# Env: ORACLE_PERF_BENCH (oracle binary), ELK_LEAN_BIN (elk binary), PERF_SCENARIOS (comma list,
# lean side only), PERF_SKIP_ORACLE=1 (reuse existing rust_*.csv), PERF_BASELINE (lean_api CSV for
# the 5% regression gate; default <out_dir>/baseline_lean_api.csv when present).
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
# `.reference/` lives in the main checkout; git worktrees find it through the common git dir
REF="$HERE/.reference"
if [ ! -d "$REF" ]; then
  COMMON=$(git -C "$HERE" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)
  if [ -n "$COMMON" ]; then REF="$(dirname "$COMMON")/.reference"; fi
fi
IT=${1:-20}
WU=${2:-3}
OUT=${3:-"$HERE/tests/perf"}
BENCH=${ORACLE_PERF_BENCH:-"$REF/elk-rs-target/release/perf_benchmark"}
LEAN=${ELK_LEAN_BIN:-"$HERE/.lake/build/bin/elk"}
mkdir -p "$OUT"
if [ "${PERF_SKIP_ORACLE:-0}" != "1" ]; then
  "$BENCH" --engine rust_api --mode synthetic --iterations "$IT" --warmup "$WU" --output "$OUT/rust_api.csv"
  "$BENCH" --engine rust_native --mode synthetic --iterations "$IT" --warmup "$WU" --output "$OUT/rust_native.csv"
fi
if [ -n "${PERF_SCENARIOS:-}" ]; then
  "$LEAN" bench --mode synthetic --iterations "$IT" --warmup "$WU" --scenarios "$PERF_SCENARIOS" --output "$OUT/lean_api.csv"
else
  "$LEAN" bench --mode synthetic --iterations "$IT" --warmup "$WU" --output "$OUT/lean_api.csv"
fi
BASE=${PERF_BASELINE:-"$OUT/baseline_lean_api.csv"}
if [ -f "$BASE" ]; then
  python3 "$HERE/scripts/compare_perf.py" "$OUT" "$OUT/report.md" --baseline "$BASE"
else
  python3 "$HERE/scripts/compare_perf.py" "$OUT" "$OUT/report.md"
fi
