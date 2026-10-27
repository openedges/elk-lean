#!/bin/sh
# Whole-corpus model parity: elk-rs oracle vs elk-lean on the `.json` models.
#   sh scripts/run_model_parity.sh <models_dir> <out_dir> [--limit N] [--filter SUBSTR]
# Outputs: <out_dir>/inputs.tsv, oracle/, oracle.tsv, lean/, lean.tsv, merged.tsv,
#          report.md, diff_details.tsv
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
MODELS=$1
OUT=$2
shift 2
RUNNER=${ORACLE_RUNNER:-"$HERE/.reference/elk-rs-target/release/model_parity_layout_runner"}
LEAN=${ELK_LEAN_BIN:-"$HERE/.lake/build/bin/elk"}
mkdir -p "$OUT"
python3 "$HERE/scripts/make_json_manifest.py" "$MODELS" "$OUT/inputs.tsv" "$@"
if [ ! -f "$OUT/oracle.tsv" ] || [ "${PARITY_REFRESH_ORACLE:-0}" = "1" ]; then
  echo "== oracle (elk-rs) =="
  "$RUNNER" --input-manifest "$OUT/inputs.tsv" --output-manifest "$OUT/oracle.tsv" \
    --rust-layout-dir "$OUT/oracle" --pretty-print true > "$OUT/oracle.log" 2>&1 || true
  tail -1 "$OUT/oracle.log"
fi
echo "== elk-lean =="
"$LEAN" batch --input-manifest "$OUT/inputs.tsv" --output-manifest "$OUT/lean.tsv" \
  --layout-dir "$OUT/lean" --pretty > "$OUT/lean.log" 2>&1 || true
tail -1 "$OUT/lean.log"
python3 "$HERE/scripts/merge_parity_manifests.py" "$OUT/oracle.tsv" "$OUT/lean.tsv" "$OUT/merged.tsv"
python3 "$HERE/scripts/compare_model_parity_layouts.py" --manifest "$OUT/merged.tsv" \
  --report "$OUT/report.md" --details "$OUT/diff_details.tsv" ${PARITY_ABS_TOL:+--abs-tol $PARITY_ABS_TOL} || true
sed -n '1,25p' "$OUT/report.md"
