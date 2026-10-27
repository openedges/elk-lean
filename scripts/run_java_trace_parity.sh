#!/bin/sh
# Phase-step trace parity against ELK Java 0.12.0 (layered: the LGraph after every processor).
#   sh scripts/run_java_trace_parity.sh <models_dir> <out_dir> [--include a,b] [--limit N]
# 1. ELK Java (scripts/run_java_baseline.sh --trace true) lays out every model with the root
#    algorithm forced to layered and records its traces under <out_dir>/java/trace/;
# 2. elk-lean lays out exactly Java's inputs (elk batch --trace-dir, which forces layered too);
# 3. scripts/compare_phase_traces.py compares every step with tolerance TRACE_TOL (default 0) and
#    strict node/port order.
# Set JAVA_TRACE_REUSE=1 to keep an existing <out_dir>/java.
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
MODELS=$1
OUT=$2
shift 2
LEAN=${ELK_LEAN_BIN:-"$HERE/.lake/build/bin/elk"}
TOL=${TRACE_TOL:-0}
mkdir -p "$OUT"
if [ "${JAVA_TRACE_REUSE:-0}" != "1" ] || [ ! -f "$OUT/java/java_manifest.tsv" ]; then
  rm -rf "$OUT/java"
  echo "== ELK Java =="
  sh "$HERE/scripts/run_java_baseline.sh" "$MODELS" "$OUT/java" --trace true "$@" 2>&1 | tail -1
fi
rm -rf "$OUT/lean_trace" "$OUT/lean"
mkdir -p "$OUT/lean_trace"
echo "== elk-lean =="
"$LEAN" batch --input-manifest "$OUT/java/java_manifest.tsv" --output-manifest "$OUT/lean.tsv" \
  --layout-dir "$OUT/lean" --trace-dir "$OUT/lean_trace" > "$OUT/lean.log" 2>&1 || true
tail -1 "$OUT/lean.log"
echo "== traces (tolerance $TOL) =="
python3 "$HERE/scripts/compare_phase_traces.py" --strict-order --tolerance "$TOL" --batch --json --report-missing \
  "$OUT/java/trace" "$OUT/lean_trace" > "$OUT/trace_report.json" || true
python3 "$HERE/scripts/summarize_trace_report.py" "$OUT/trace_report.json" "$OUT/lean.tsv" "$OUT/trace_summary.md"
sed -n '1,30p' "$OUT/trace_summary.md"
