#!/bin/sh
# Byte-for-byte comparison of `elk layout --pretty --sort-keys` with the oracle outputs of a model
# parity run (the oracle runner writes pretty JSON with sorted keys).
#   sh scripts/compare_bytes.sh <model_parity_out_dir> [report.tsv]
# Uses <dir>/merged.tsv (input_json, java_layout_json = oracle output, statuses). Prints counts and
# writes the differing models to the report (default <dir>/bytes_report.tsv).
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
DIR=$1
REPORT=${2:-"$DIR/bytes_report.tsv"}
LEAN=${ELK_LEAN_BIN:-"$HERE/.lake/build/bin/elk"}
TMP=$(mktemp -d)
: > "$REPORT"
same=0; diff=0; skip=0
# empty tab-separated fields would collapse in `read`, so awk picks the columns first
awk -F'\t' 'NR > 1 { print $1 "|" $2 "|" $3 "|" $4 "|" $7 }' "$DIR/merged.tsv" | while IFS='|' read -r rel inp jl js rs; do
  if [ "$js" != "ok" ] || [ "$rs" != "ok" ]; then echo skip; continue; fi
  if "$LEAN" layout "$inp" --pretty --sort-keys -o "$TMP/out.json" 2>/dev/null && cmp -s "$TMP/out.json" "$jl"; then
    echo same
  else
    echo diff
    printf '%s\t%s\t%s\n' "$rel" "$inp" "$jl" >> "$REPORT"
  fi
done | sort | uniq -c
rm -rf "$TMP"
echo "differing models: $REPORT"
