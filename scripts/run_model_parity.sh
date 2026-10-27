#!/bin/sh
# Whole-corpus model parity: elk-rs oracle vs elk-lean on the `.json` and `.elkt` models
# (`.elkt` converted with `elk convert` into <out_dir>/elkt_json; set PARITY_INCLUDE_ELKT=0 to skip).
#   sh scripts/run_model_parity.sh <models_dir> <out_dir> [--limit N] [--filter SUBSTR]
# Outputs: <out_dir>/inputs.tsv, oracle/, oracle.tsv, lean/, lean.tsv, merged.tsv,
#          report.md, diff_details.tsv
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
# `.reference/` lives in the main checkout; git worktrees find it through the common git dir
REF="$HERE/.reference"
if [ ! -d "$REF" ]; then
  COMMON=$(git -C "$HERE" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)
  if [ -n "$COMMON" ]; then REF="$(dirname "$COMMON")/.reference"; fi
fi
MODELS=$1
OUT=$2
shift 2
RUNNER=${ORACLE_RUNNER:-"$REF/elk-rs-target/release/model_parity_layout_runner"}
LEAN=${ELK_LEAN_BIN:-"$HERE/.lake/build/bin/elk"}
mkdir -p "$OUT"
ELKT_ARGS=""
if [ "${PARITY_INCLUDE_ELKT:-1}" = "1" ]; then ELKT_ARGS="--include-elkt --elk-bin $LEAN --elkt-cache $OUT/elkt_json"; fi
python3 "$HERE/scripts/make_json_manifest.py" "$MODELS" "$OUT/inputs.tsv" $ELKT_ARGS "$@"
# the oracle layouts are regenerated when the manifest or the layout directory is missing (a git
# worktree may carry a tracked oracle.tsv without the ignored oracle/ directory)
if [ ! -f "$OUT/oracle.tsv" ] || [ ! -d "$OUT/oracle" ] || [ "${PARITY_REFRESH_ORACLE:-0}" = "1" ]; then
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
