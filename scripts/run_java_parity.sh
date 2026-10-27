#!/bin/sh
# Result parity against ELK Java 0.12.0 (the result baseline; elk-rs is the performance baseline).
#   sh scripts/run_java_parity.sh <java_baseline_dir> <out_dir>
# <java_baseline_dir> comes from scripts/run_java_baseline.sh (java_manifest.tsv, inputs/, layouts/).
# elk-lean lays out exactly the inputs Java laid out (for .elkt/.elkg: ELK's own JSON export), then:
#   report_exact.md / details_exact.tsv  numeric values compared exactly (abs tol 0)
#   report.md / details.tsv              abs tol 1e-6 (the elk-rs contract, for orientation)
# Number formatting differs by design (Gson `12.0`, serde-style `12`), so values are compared, not bytes.
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
JB=$1
OUT=$2
LEAN=${ELK_LEAN_BIN:-"$HERE/.lake/build/bin/elk"}
mkdir -p "$OUT"
"$LEAN" batch --input-manifest "$JB/java_manifest.tsv" --output-manifest "$OUT/merged.tsv" \
  --layout-dir "$OUT/lean" > "$OUT/lean.log" 2>&1 || true
tail -1 "$OUT/lean.log"
python3 "$HERE/scripts/compare_model_parity_layouts.py" --manifest "$OUT/merged.tsv" \
  --report "$OUT/report_exact.md" --details "$OUT/details_exact.tsv" --abs-tol 0 --max-diffs-per-model 50 || true
python3 "$HERE/scripts/compare_model_parity_layouts.py" --manifest "$OUT/merged.tsv" \
  --report "$OUT/report.md" --details "$OUT/details.tsv" || true
echo "== exact =="; sed -n '3,12p' "$OUT/report_exact.md"
echo "== abs tol 1e-6 =="; sed -n '3,12p' "$OUT/report.md"
