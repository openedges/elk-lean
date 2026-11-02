#!/bin/sh
# ELK Text loader parity: converts every `.elkt` model of a Java baseline manifest with `elk convert`
# (Lean `.elkt` loader + JSON exporter) and compares the result semantically with ELK Java's own JSON
# export of the same model (`inputs/<model>.elkt.json` of scripts/run_java_baseline.sh, i.e. the graph
# as the Java text loader read it). This is the check the corpus parity cannot do: there, both sides
# lay out Java's export, so the Lean text loader is never compared with Java's.
#   sh scripts/run_elkt_loader_parity.sh <models_dir> <java_baseline_dir> <out_dir>
# Writes <out_dir>/lean/<model>.json, report.md, details.tsv; exit 1 when a model differs.
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
MODELS=$(cd "$1" && pwd)
JB=$2
OUT=$3
LEAN=${ELK_LEAN_BIN:-"$HERE/.lake/build/bin/elk"}
mkdir -p "$OUT/lean"
n=0; failed=0
tail -n +2 "$JB/java_manifest.tsv" | cut -f1 | grep -E '\.elkt$' | while IFS= read -r rel; do
  mkdir -p "$OUT/lean/$(dirname "$rel")"
  if ! "$LEAN" convert "$MODELS/$rel" -o "$OUT/lean/$rel.json" 2> "$OUT/lean/$rel.err"; then
    printf '%s\n' "$rel" >> "$OUT/convert_failures.txt"
  else
    rm -f "$OUT/lean/$rel.err"
  fi
done
if [ -f "$OUT/convert_failures.txt" ]; then
  echo "elk convert failed for $(wc -l < "$OUT/convert_failures.txt" | tr -d ' ') models (see $OUT/convert_failures.txt)"
fi
python3 "$HERE/scripts/compare_elkt_conversion.py" --java-manifest "$JB/java_manifest.tsv" --lean-dir "$OUT/lean" \
  --report "$OUT/report.md" --details "$OUT/details.tsv"
