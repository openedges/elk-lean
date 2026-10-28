#!/bin/sh
# Corpus performance benchmark: elk-rs oracle `perf_benchmark --mode models` (rust_api) vs
# `elk bench --mode models` (lean_api) on every model of a parity manifest (status `ok`), then
# `compare_perf.py --corpus` writes totals, the per-model ratio distribution and the slowest models.
#   sh scripts/run_corpus_benchmark.sh [iterations=3] [warmup=1] [out_dir=tests/perf/corpus] [manifest]
# The manifest defaults to tests/tmp/model_parity/inputs.tsv, which `scripts/run_model_parity.sh
# external/elk-models tests/tmp/model_parity` writes (its input_json column must point at existing
# files: the .elkt models are converted into that directory).
# Env: ORACLE_PERF_BENCH, ELK_LEAN_BIN, PERF_SKIP_ORACLE=1 (reuse rust_api.csv), PERF_LIMIT (model
# count, default all), PERF_BASELINE (lean_api CSV for the 5% gate on the total; default
# <out_dir>/baseline_lean_api.csv when present).
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
REF="$HERE/.reference"
if [ ! -d "$REF" ]; then
  COMMON=$(git -C "$HERE" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)
  if [ -n "$COMMON" ]; then REF="$(dirname "$COMMON")/.reference"; fi
fi
IT=${1:-3}
WU=${2:-1}
OUT=${3:-"$HERE/tests/perf/corpus"}
MANIFEST=${4:-"$HERE/tests/tmp/model_parity/inputs.tsv"}
LIMIT=${PERF_LIMIT:-1000000}
BENCH=${ORACLE_PERF_BENCH:-"$REF/elk-rs-target/release/perf_benchmark"}
LEAN=${ELK_LEAN_BIN:-"$HERE/.lake/build/bin/elk"}
if [ ! -f "$MANIFEST" ]; then
  echo "manifest not found: $MANIFEST (run scripts/run_model_parity.sh first)" >&2
  exit 2
fi
mkdir -p "$OUT"
if [ "${PERF_SKIP_ORACLE:-0}" != "1" ]; then
  "$BENCH" --engine rust_api --mode models --manifest "$MANIFEST" --limit "$LIMIT" \
    --iterations "$IT" --warmup "$WU" --output "$OUT/rust_api.csv" 2> "$OUT/rust_api.log"
  tail -1 "$OUT/rust_api.log"
fi
"$LEAN" bench --mode models --manifest "$MANIFEST" --limit "$LIMIT" \
  --iterations "$IT" --warmup "$WU" --output "$OUT/lean_api.csv" 2> "$OUT/lean_api.log"
tail -1 "$OUT/lean_api.log"
BASE=${PERF_BASELINE:-"$OUT/baseline_lean_api.csv"}
if [ -f "$BASE" ]; then
  python3 "$HERE/scripts/compare_perf.py" "$OUT" "$OUT/report.md" --corpus --baseline "$BASE"
else
  python3 "$HERE/scripts/compare_perf.py" "$OUT" "$OUT/report.md" --corpus
fi
