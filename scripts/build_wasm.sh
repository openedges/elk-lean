#!/bin/sh
# Builds elk-lean for WebAssembly with emscripten (PLAN.md 8, org.eclipse.elk.wasm):
#   plugins/org.eclipse.elk.wasm/dist/wasm-node/elk_lean.cjs + elk_lean.wasm      Node.js (CommonJS, sync init)
#   plugins/org.eclipse.elk.wasm/dist/wasm/elk_lean.mjs + elk_lean_core.{mjs,wasm} browser ES module
#   plugins/org.eclipse.elk.wasm/dist/BUILD_INFO.json                              versions, flags, sizes
# Intermediate files: plugins/org.eclipse.elk.wasm/build/ (incremental; delete it for a clean build).
#
# Requirements (both gitignored under the main checkout's .reference/, shared by worktrees):
#   emsdk $EMSDK_VERSION   git clone https://github.com/emscripten-core/emsdk.git .reference/emsdk
#                          cd .reference/emsdk && ./emsdk install $EMSDK_VERSION && ./emsdk activate $EMSDK_VERSION
#                          (emsdk itself needs python >= 3.10: EMSDK_PYTHON=/path/to/python3)
#   Lean sources           git clone --depth 1 --branch v<toolchain> https://github.com/leanprover/lean4 .reference/lean4-v<toolchain>
# Overrides: EMSDK_DIR, LEAN_SRC_DIR, JOBS.
# usage: sh scripts/build_wasm.sh [--verify-stdlib]
#   --verify-stdlib  (macOS) also check that the regenerated Init/Std C compiles to the release objects
set -eu
EMSDK_VERSION=6.0.13
HERE=$(cd "$(dirname "$0")/.." && pwd)
cd "$HERE"
export PATH="$HOME/.elan/bin:$PATH"
# `.reference/` lives in the main checkout; git worktrees find it through the common git dir
REF="$HERE/.reference"
if [ ! -d "$REF" ]; then
  COMMON=$(git -C "$HERE" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)
  if [ -n "$COMMON" ]; then REF="$(dirname "$COMMON")/.reference"; fi
fi
LEAN_V=$(lean --short-version)
EMSDK=${EMSDK_DIR:-"$REF/emsdk"}
LEAN_SRC=${LEAN_SRC_DIR:-"$REF/lean4-v$LEAN_V"}
JOBS=${JOBS:-$( (sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 4) | awk '{n=$1-2; print (n<1?1:n)}')}
if [ ! -x "$EMSDK/upstream/emscripten/emcc" ]; then
  echo "error: emsdk not found at $EMSDK (see the header of $0)" >&2; exit 1
fi
if [ ! -f "$LEAN_SRC/src/runtime/object.cpp" ]; then
  echo "error: Lean $LEAN_V sources not found at $LEAN_SRC (see the header of $0)" >&2; exit 1
fi
if [ -f "$EMSDK/.emscripten" ] && ! grep -q "$EMSDK_VERSION" "$EMSDK/upstream/emscripten/emscripten-version.txt" 2>/dev/null; then
  echo "warning: emsdk at $EMSDK is not $EMSDK_VERSION ($(cat "$EMSDK/upstream/emscripten/emscripten-version.txt" 2>/dev/null))" >&2
fi
# Lean C of every Elk module (Elk.Ffi's own C comes from the ElkFfi library facet)
lake build elk ElkFfi:static >/dev/null
python3 plugins/org.eclipse.elk.wasm/tools/build.py --root "$HERE" --lean "$(command -v lean)" \
  --lean-src "$LEAN_SRC" --emsdk "$EMSDK" --jobs "$JOBS"
if [ "${1:-}" = "--verify-stdlib" ]; then
  python3 plugins/org.eclipse.elk.wasm/tools/verify_stdlib_c.py --lean "$(command -v lean)" \
    --stdlib-c plugins/org.eclipse.elk.wasm/build/stdlib-c --work plugins/org.eclipse.elk.wasm/build/verify --jobs "$JOBS"
fi
