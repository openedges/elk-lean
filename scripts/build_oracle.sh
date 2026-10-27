#!/bin/sh
# Build the elk-rs oracle (release) out of tree.
# Requires ../elk-rs at the pinned commit (see VERSIONING.md) and Rust via mise.
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
ELK_RS=${ELK_RS_DIR:-"$HERE/../elk-rs"}
TARGET=${ORACLE_TARGET_DIR:-"$HERE/.reference/elk-rs-target"}
EXPECTED=eb586b6d91ee0b55cda591546cec8f04cc7f2422
ACTUAL=$(git -C "$ELK_RS" rev-parse HEAD)
if [ "$ACTUAL" != "$EXPECTED" ]; then
  echo "warning: ../elk-rs is at $ACTUAL, expected $EXPECTED (VERSIONING.md)" >&2
fi
mise trust "$ELK_RS/mise.toml" >/dev/null 2>&1 || true
cd "$ELK_RS"
CARGO_TARGET_DIR="$TARGET" mise exec -- cargo build --release --workspace --bins
echo "oracle binaries: $TARGET/release/{model_parity_layout_runner,perf_benchmark}"
