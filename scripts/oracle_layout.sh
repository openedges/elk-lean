#!/bin/sh
# Lay out one ELK JSON file with the elk-rs oracle.
#   sh scripts/oracle_layout.sh <input.json> <output.json> [trace_dir]
# The oracle runner consumes a Java-style manifest, so a one-row manifest is
# synthesized in a temporary directory.
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
RUNNER=${ORACLE_RUNNER:-"$HERE/.reference/elk-rs-target/release/model_parity_layout_runner"}
IN=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
OUT=$2
TRACE=${3:-}
[ -x "$RUNNER" ] || { echo "oracle runner not found: $RUNNER (run scripts/build_oracle.sh)" >&2; exit 1; }
TMP=$(mktemp -d "${TMPDIR:-/tmp}/elk-oracle.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
printf 'model_rel_path\tinput_json\tjava_layout_json\tjava_status\tjava_error\n' > "$TMP/manifest.tsv"
printf '%s\t%s\t\tok\t\n' "$(basename "$1")" "$IN" >> "$TMP/manifest.tsv"
ARGS="--input-manifest $TMP/manifest.tsv --output-manifest $TMP/out.tsv --rust-layout-dir $TMP/layout --pretty-print true"
if [ -n "$TRACE" ]; then
  mkdir -p "$TRACE"
  ARGS="$ARGS --trace-dir $TRACE"
fi
"$RUNNER" $ARGS >/dev/null
STATUS=$(tail -1 "$TMP/out.tsv" | cut -f7)
if [ "$STATUS" != "ok" ]; then
  echo "oracle failed: $(tail -1 "$TMP/out.tsv" | cut -f8)" >&2
  exit 1
fi
mkdir -p "$(dirname "$OUT")"
cp "$(tail -1 "$TMP/out.tsv" | cut -f6)" "$OUT"
echo "$OUT"
