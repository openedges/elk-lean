#!/bin/sh
# Phase-step trace parity for one model: elk-rs oracle traces vs elk-lean traces.
#   sh scripts/run_phase_trace_parity.sh <model.json|model.elkt> <out_dir> [compare options…]
# Writes <out_dir>/oracle_trace/step_NNN_*.json, <out_dir>/lean_trace/…, the two layouts and
# runs compare_phase_traces.py (first divergence step, tolerance 0.001).
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
MODEL=$1
OUT=$2
shift 2
LEAN=${ELK_LEAN_BIN:-"$HERE/.lake/build/bin/elk"}
mkdir -p "$OUT"
INPUT=$MODEL
case "$MODEL" in
  *.elkt) INPUT="$OUT/input.json"; "$LEAN" convert "$MODEL" -o "$INPUT" ;;
esac
rm -rf "$OUT/oracle_trace" "$OUT/lean_trace"
sh "$HERE/scripts/oracle_layout.sh" "$INPUT" "$OUT/oracle.json" "$OUT/oracle_trace" > "$OUT/oracle.log" 2>&1 || echo "oracle failed: $(tail -1 "$OUT/oracle.log")"
ELK_TRACE_DIR="$OUT/lean_trace" "$LEAN" layout "$INPUT" --pretty --sort-keys -o "$OUT/lean.json" > "$OUT/lean.log" 2>&1 || echo "elk-lean failed: $(tail -1 "$OUT/lean.log")"
# the oracle runner nests the steps under <trace_dir>/<model file name>/
ORACLE_TRACE="$OUT/oracle_trace/$(basename "$INPUT")"
echo "oracle steps: $(ls "$ORACLE_TRACE" 2>/dev/null | wc -l | tr -d ' '), lean steps: $(ls "$OUT/lean_trace" 2>/dev/null | wc -l | tr -d ' ')"
UNPORTED=$(ls "$OUT/lean_trace" 2>/dev/null | grep '_Unported_' | sed 's/^step_[0-9]*_Unported_//; s/\.json$//' | sort -u | tr '\n' ' ')
[ -n "$UNPORTED" ] && echo "note: unported stand-ins in the elk-lean run: $UNPORTED"
python3 "$HERE/scripts/compare_phase_traces.py" "$ORACLE_TRACE" "$OUT/lean_trace" "$@" || true
