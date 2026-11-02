#!/bin/sh
# Builds the elk-lean Node.js native addon (plugins/org.eclipse.elk.napi/src/elk_napi.c):
#   plugins/org.eclipse.elk.js/dist/elk-lean.<triple>.node
# It links .lake/build/ffi/libelklean.a and the Lean runtime libraries (.lake/build/ffi/ldflags),
# both produced by scripts/build_ffi.sh (run first, a no-op when up to date).
#
# usage: sh scripts/build_napi.sh [--skip-ffi] [--release] [--copy-to-npm]
#   --skip-ffi     reuse the existing libelklean.a instead of running scripts/build_ffi.sh
#   --release      (macOS) link the release objects of scripts/build_release.sh instead of libelklean.a:
#                  ThinLTO across the Elk C, the C API glue and the no-GMP Lean runtime, PGO when the
#                  release build had a profile; compiled and linked with the toolchain clang + ld64.lld
#                  (docs/build-optimization.md). Run scripts/build_release.sh first; implies the no-GMP
#                  runtime, scripts/build_ffi.sh is not run.
#   --copy-to-npm  also copy the addon, LICENSE and NOTICE into plugins/org.eclipse.elk.js/npm/<triple>/
#                  (the published platform package: requires the no-GMP runtime, ELK_NO_GMP=1)
# env:
#   NODE              node binary whose headers are used (default: `node` on PATH, then `mise which node`)
#   NODE_INCLUDE_DIR  directory holding node_api.h (default: <node prefix>/include/node)
#   CC                C compiler (default: cc)
#   ELK_NO_GMP=1      passed on to scripts/build_ffi.sh: link the Lean runtime rebuilt without GMP
#                     (docs/gmp-licensing.md); with --skip-ffi the runtime recorded by the last
#                     build_ffi.sh run (.lake/build/ffi/runtime) is used, and must then be `nogmp`
#
# Platforms:
#   macOS:  cc -bundle -undefined dynamic_lookup (napi_* resolve against the node binary at load time);
#           only napi_register_module_v1 / node_api_module_get_api_version_v1 are exported.
#   Linux:  cc -shared -fPIC -Wl,-Bsymbolic -Wl,--exclude-libs,ALL -Wl,--version-script=<napi only>
#           -Bsymbolic/--exclude-libs keep the statically linked libuv (and gmp) of the Lean runtime from
#           binding to the libuv symbols that the node executable exports (not tested here).
#   Windows: not supported yet (needs node.lib / delay-load hook and a MSVC or mingw Lean toolchain).
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
cd "$HERE"
export PATH="$HOME/.elan/bin:$PATH"
CC=${CC:-cc}
SKIP_FFI=0
COPY_NPM=0
RELEASE=0
for arg in "$@"; do
  case "$arg" in
    --skip-ffi) SKIP_FFI=1 ;;
    --release) RELEASE=1; SKIP_FFI=1 ;;
    --copy-to-npm) COPY_NPM=1 ;;
    *) echo "unknown argument: $arg" >&2; exit 2 ;;
  esac
done

FFI="$HERE/.lake/build/ffi"
REL="$HERE/.lake/build/release"
if [ "$SKIP_FFI" = 0 ]; then
  sh scripts/build_ffi.sh
fi
if [ "$RELEASE" = 1 ]; then
  [ "$(uname -s)" = Darwin ] || { echo "--release is only implemented for macOS" >&2; exit 1; }
  [ -f "$REL/ffi_objects.txt" ] || { echo "missing $REL/ffi_objects.txt (run scripts/build_release.sh)" >&2; exit 1; }
  RUNTIME=nogmp
else
  [ -f "$FFI/libelklean.a" ] || { echo "missing $FFI/libelklean.a (run scripts/build_ffi.sh)" >&2; exit 1; }
  RUNTIME=$(cat "$FFI/runtime" 2>/dev/null || echo gmp)
fi
if [ "${ELK_NO_GMP:-0}" = 1 ] && [ "$RUNTIME" != nogmp ]; then
  echo "ELK_NO_GMP=1 but $FFI was built with the GMP runtime (rerun ELK_NO_GMP=1 sh scripts/build_ffi.sh)" >&2
  exit 1
fi

# node headers
if [ -z "${NODE_INCLUDE_DIR:-}" ]; then
  if [ -z "${NODE:-}" ]; then
    if command -v node >/dev/null 2>&1; then
      NODE=$(command -v node)
    elif command -v mise >/dev/null 2>&1; then
      NODE=$(mise which node 2>/dev/null || true)
    fi
  fi
  if [ -z "${NODE:-}" ] || [ ! -x "$NODE" ]; then
    echo "node not found: set NODE=/path/to/node or NODE_INCLUDE_DIR=<dir with node_api.h>" >&2
    exit 1
  fi
  NODE_EXEC=$("$NODE" -p 'process.execPath' 2>/dev/null) || {
    echo "cannot run $NODE: set NODE=/path/to/node or NODE_INCLUDE_DIR=<dir with node_api.h>" >&2
    exit 1
  }
  NODE_PREFIX=$(cd "$(dirname "$NODE_EXEC")/.." && pwd)
  NODE_INCLUDE_DIR="$NODE_PREFIX/include/node"
fi
[ -f "$NODE_INCLUDE_DIR/node_api.h" ] || { echo "node_api.h not found in $NODE_INCLUDE_DIR" >&2; exit 1; }

# platform triple (same names as the elk-rs / napi-rs platform packages)
OS=$(uname -s)
ARCH=$(uname -m)
case "$ARCH" in
  arm64|aarch64) ARCH=arm64 ;;
  x86_64|amd64) ARCH=x64 ;;
esac
case "$OS" in
  Darwin) TRIPLE="darwin-$ARCH" ;;
  Linux)
    if ldd --version 2>&1 | grep -qi musl; then TRIPLE="linux-$ARCH-musl"; else TRIPLE="linux-$ARCH-gnu"; fi ;;
  *) echo "unsupported platform: $OS $ARCH" >&2; exit 1 ;;
esac

OUT_DIR="$HERE/plugins/org.eclipse.elk.js/dist"
OBJ_DIR="$HERE/.lake/build/napi"
mkdir -p "$OUT_DIR" "$OBJ_DIR"
OUT="$OUT_DIR/elk-lean.$TRIPLE.node"
CFLAGS="-O2 -DNDEBUG -fPIC -std=c11 -Wall -Wextra -Werror -I $NODE_INCLUDE_DIR -I plugins/org.eclipse.elk.ffi/include"
if [ "$RELEASE" = 1 ]; then
  LP=$(lean --print-prefix)
  CC="$LP/bin/clang"
  CFLAGS="$CFLAGS -isysroot $(xcrun --show-sdk-path) -isystem $LP/include/clang -flto=thin"
fi
# shellcheck disable=SC2086
$CC $CFLAGS -c plugins/org.eclipse.elk.napi/src/elk_napi.c -o "$OBJ_DIR/elk_napi.o"
if [ "$RELEASE" = 1 ]; then
  # the release objects, Lake's C shim and the toolchain libraries, linked like the release CLI
  # (Lake's --sysroot/-L/lld setup) with the LTO runtime of scripts/build_release.sh
  {
    cat "$REL/ffi_objects.txt"
    echo "$HERE/.lake/build/lib/libelkcoreffi.a"
    printf '%s\n' "--sysroot" "$LP" "-L$LP/lib" "-L$LP/lib/libc" "-L$LP/lib/lean" -fuse-ld=lld \
      -flto=thin "-Wl,--thinlto-jobs=${JOBS:-3}" "-Wl,-cache_path_lto,$REL/lto-cache" \
      -lInit -lStd "$REL/runtime/lib/libleanrt_nogmp.a" -luv -lc++ -Wl,-dead_strip
  } > "$OBJ_DIR/release.rsp"
  LDFLAGS="@$OBJ_DIR/release.rsp"
else
  LDFLAGS="$FFI/libelklean.a $(cat "$FFI/ldflags")"
fi
# before stripping: the GMP symbols linked into the addon are local ones
check_no_gmp() {
  if [ "$RUNTIME" = nogmp ] && nm "$OUT" 2>/dev/null | grep -q '__gmp'; then
    echo "error: $OUT contains GMP symbols" >&2; exit 1
  fi
}
case "$OS" in
  Darwin)
    # shellcheck disable=SC2086
    $CC -bundle -undefined dynamic_lookup \
      -Wl,-exported_symbol,_napi_register_module_v1 \
      -Wl,-exported_symbol,_node_api_module_get_api_version_v1 \
      "$OBJ_DIR/elk_napi.o" $LDFLAGS -o "$OUT"
    check_no_gmp
    strip -x "$OUT"
    ;;
  Linux)
    printf '{ global: napi_register_module_v1; node_api_module_get_api_version_v1; local: *; };\n' > "$OBJ_DIR/exports.map"
    # the link driver scripts/build_ffi.sh recorded for its ldflags (`c++` for the no-GMP runtime:
    # libstdc++ and libgcc static, so the addon depends on glibc only)
    LD=$(cat "$FFI/ld" 2>/dev/null || echo "$CC")
    # shellcheck disable=SC2086
    $LD -shared -fPIC -Wl,-Bsymbolic -Wl,--exclude-libs,ALL -Wl,--version-script="$OBJ_DIR/exports.map" \
      "$OBJ_DIR/elk_napi.o" $LDFLAGS -o "$OUT"
    check_no_gmp
    strip --strip-unneeded "$OUT"
    ;;
esac
echo "built $OUT ($(wc -c < "$OUT" | tr -d ' ') bytes, Lean runtime: $RUNTIME$([ "$RELEASE" = 1 ] && echo ", release objects"), node headers: $NODE_INCLUDE_DIR)"
if [ "$COPY_NPM" = 1 ]; then
  if [ "$RUNTIME" != nogmp ]; then
    echo "--copy-to-npm: the addon links GMP (LGPL v3); build the npm addon with ELK_NO_GMP=1 (docs/gmp-licensing.md)" >&2
    exit 1
  fi
  NPM_DIR="$HERE/plugins/org.eclipse.elk.js/npm/$TRIPLE"
  [ -d "$NPM_DIR" ] || { echo "no platform package template $NPM_DIR" >&2; exit 1; }
  cp "$OUT" "$NPM_DIR/"
  cp "$HERE/LICENSE" "$NPM_DIR/LICENSE"
  cp "$HERE/plugins/org.eclipse.elk.js/NOTICE" "$NPM_DIR/NOTICE"
  echo "copied the addon, LICENSE and NOTICE to $NPM_DIR/"
fi
