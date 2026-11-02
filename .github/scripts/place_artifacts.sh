#!/bin/sh
# Puts the artifacts of release.yml where scripts/publish_npm.sh expects them:
#   artifacts/addon-<triple>/elk-lean.<triple>.node -> plugins/org.eclipse.elk.js/npm/<triple>/
#   artifacts/wasm/{wasm,wasm-node}                 -> plugins/org.eclipse.elk.js/dist/
# usage: sh .github/scripts/place_artifacts.sh <artifacts dir>   (run from the repository root)
set -eu
A=${1:?artifacts directory}
js="plugins/org.eclipse.elk.js"
mkdir -p "$js/dist"
cp -R "$A/wasm/wasm" "$A/wasm/wasm-node" "$js/dist/"
for f in "$A"/addon-*/*.node; do
  triple=$(basename "$f" .node)
  triple="${triple#elk-lean.}"
  [ -d "$js/npm/$triple" ] || { echo "no platform package for $f" >&2; exit 1; }
  cp "$f" "$js/npm/$triple/"
  cp LICENSE "$js/npm/$triple/LICENSE"
  cp NOTICE "$js/npm/$triple/NOTICE"
done
ls -l "$js"/npm/*/*.node "$js/dist/wasm" "$js/dist/wasm-node"
