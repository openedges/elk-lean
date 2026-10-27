#!/bin/sh
# Corpus phase-step trace parity: elk-rs oracle traces vs elk-lean traces, one directory per model.
#   sh scripts/run_trace_parity.sh <models_dir> <out_dir> [--limit N] [--filter SUBSTR]
# Outputs: <out_dir>/inputs.tsv, oracle_trace/<model>/step_*.json, lean_trace/<model>/…,
#          oracle.tsv, lean.tsv, trace_report.json, trace_summary.md (first divergent processor per
#          model and a histogram of divergent processors).
set -eu
# Node/port storage order is compared strictly (`--strict-order`); set TRACE_COMPARE_LOOSE=1 for the
# geometric normalisation of the Java-vs-Rust comparison.
HERE=$(cd "$(dirname "$0")/.." && pwd)
MODELS=$1
OUT=$2
shift 2
RUNNER=${ORACLE_RUNNER:-"$HERE/.reference/elk-rs-target/release/model_parity_layout_runner"}
LEAN=${ELK_LEAN_BIN:-"$HERE/.lake/build/bin/elk"}
mkdir -p "$OUT"
ELKT_ARGS=""
if [ "${PARITY_INCLUDE_ELKT:-1}" = "1" ]; then ELKT_ARGS="--include-elkt --elk-bin $LEAN --elkt-cache $OUT/elkt_json"; fi
python3 "$HERE/scripts/make_json_manifest.py" "$MODELS" "$OUT/inputs.tsv" $ELKT_ARGS "$@"
rm -rf "$OUT/oracle_trace" "$OUT/lean_trace"
mkdir -p "$OUT/oracle_trace" "$OUT/lean_trace"
echo "== oracle (elk-rs) =="
"$RUNNER" --input-manifest "$OUT/inputs.tsv" --output-manifest "$OUT/oracle.tsv" \
  --rust-layout-dir "$OUT/oracle" --pretty-print true --trace-dir "$OUT/oracle_trace" > "$OUT/oracle.log" 2>&1 || true
tail -1 "$OUT/oracle.log"
echo "== elk-lean =="
"$LEAN" batch --input-manifest "$OUT/inputs.tsv" --output-manifest "$OUT/lean.tsv" \
  --layout-dir "$OUT/lean" --trace-dir "$OUT/lean_trace" --pretty > "$OUT/lean.log" 2>&1 || true
tail -1 "$OUT/lean.log"
echo "== traces =="
python3 "$HERE/scripts/compare_phase_traces.py" ${TRACE_COMPARE_LOOSE:---strict-order} --batch --json --report-missing "$OUT/oracle_trace" "$OUT/lean_trace" > "$OUT/trace_report.json" || true
python3 "$HERE/scripts/summarize_trace_report.py" "$OUT/trace_report.json" "$OUT/lean.tsv" "$OUT/trace_summary.md"
cat "$OUT/trace_summary.md"
