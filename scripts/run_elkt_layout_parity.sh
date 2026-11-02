#!/bin/sh
# ELK Text end-to-end parity: `elk layout --defaults <model.elkt>` (Lean text loader, elk-live default
# sizes, Lean layout) against ELK Java loading the same `.elkt` through EMF with the same defaults
# (`ElkJavaBaseline --live-defaults true`: the EMF graph itself is laid out, as the elk-live server does).
# Geometry is compared at tolerance 0 (options are the loader parity's job); the generated ids of
# duplicate identifiers are normalised away.
#   sh scripts/run_elkt_layout_parity.sh <models_dir> <out_dir> [--include a,b] [--limit N]
# Set JAVA_REUSE=1 to keep an existing <out_dir>/java. Exit 1 when a model drifts.
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
MODELS=$(cd "$1" && pwd)
OUT=$2
shift 2
LEAN=${ELK_LEAN_BIN:-"$HERE/.lake/build/bin/elk"}
mkdir -p "$OUT"
if [ "${JAVA_REUSE:-0}" != "1" ] || [ ! -f "$OUT/java/java_manifest.tsv" ]; then
  rm -rf "$OUT/java"
  echo "== ELK Java (elk-live defaults) =="
  sh "$HERE/scripts/run_java_baseline.sh" "$MODELS" "$OUT/java" --include .elkt --live-defaults true "$@" 2>&1 | tail -1
fi
rm -rf "$OUT/lean" "$OUT/normalized"
mkdir -p "$OUT/lean"
echo "== elk-lean (elk layout --defaults) =="
tail -n +2 "$OUT/java/java_manifest.tsv" | cut -f1 | grep -E '\.elkt$' | while IFS= read -r rel; do
  mkdir -p "$OUT/lean/$(dirname "$rel")"
  if ! "$LEAN" layout --defaults "$MODELS/$rel" -o "$OUT/lean/$rel.json" 2> "$OUT/lean/$rel.err"; then
    rm -f "$OUT/lean/$rel.json"
  else
    rm -f "$OUT/lean/$rel.err"
  fi
done
python3 "$HERE/scripts/elkt_layout_manifest.py" "$OUT/java/java_manifest.tsv" "$OUT/lean" "$OUT"
python3 "$HERE/scripts/compare_model_parity_layouts.py" --manifest "$OUT/merged.tsv" \
  --report "$OUT/report.md" --details "$OUT/details.tsv" --abs-tol 0 --max-diffs-per-model 50 || true
sed -n '3,12p' "$OUT/report.md"
grep -qE '^- drift rows: 0$' "$OUT/report.md"
