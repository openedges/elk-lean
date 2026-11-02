#!/bin/sh
# Builds the Lean runtime of the toolchain release (libleanrt.a) again from its sources for the
# native host, without GMP (Lean's own mpn bignums, `LEAN_USE_GMP` undefined), so that elk-lean
# artefacts can be linked without LGPL code (docs/gmp-licensing.md):
#   .lake/build/runtime-nogmp/lib/libleanrt_nogmp.a
#   .lake/build/runtime-nogmp/BUILD_INFO.txt         toolchain, sources, flags
# Everything else matches the release `leanrt` target (src/runtime/CMakeLists.txt,
# src/CMakeLists.txt of the toolchain tag): LEAN_MULTI_THREAD, Lean's mimalloc small-object
# allocator (LEAN_MIMALLOC from the toolchain's lean/config.h, mimalloc.cpp built with the
# MIMALLOC_OPTS of add_mimalloc_variant, MI_SECURE=0), -O3 -DNDEBUG -DLEAN_EXPORTING,
# -ffp-contract=off, hidden visibility, the TLS model of the platform (macOS local-exec like
# leanrt, Linux initial-exec like Lean's own Linux build: the archive also links into the NAPI
# addon, a shared object); additionally -fPIC. On Linux the runtime is built with the system C++
# compiler (g++, libstdc++ linked statically by scripts/build_ffi.sh and --relink), not the
# toolchain's libc++, whose headers the toolchain does not ship.
#
# libInit.a / libStd.a / libuv.a of the toolchain are reused unchanged: lean.h (shared by the Lean C
# and the runtime) has no LEAN_USE_GMP-dependent code, compiled Lean code only reaches big numbers
# through the out-of-line lean_nat_big_* / lean_int_big_* runtime functions, and the toolchain
# Init/Std objects contain no GMP references (see docs/gmp-licensing.md for the check).
#
# Requirements (sources are pinned to the toolchain release; cloned on demand into $DEPS):
#   Lean sources   .reference/lean4-v<toolchain> of the main checkout (as scripts/build_wasm.sh),
#                  must be at the commit of `lean --githash`
#   mimalloc       tag of the toolchain's src/CMakeLists.txt FetchContent (v3.4.5 for v4.35.0),
#                  whose include/mimalloc.h must equal the toolchain's include/lean/mimalloc.h
#   libuv headers  version of the toolchain's lib/libuv.a (uv_version_string, 1.52.1 for v4.35.0)
#   openssl.cpp only needs OPENSSL_VERSION_NUMBER, taken from the toolchain's libcrypto.a
#   (a generated stub <openssl/*.h>; no OpenSSL code is compiled or linked).
# Overrides: LEAN_SRC_DIR, MIMALLOC_SRC_DIR, LIBUV_SRC_DIR, DEPS (clone cache), CXX, JOBS, AR,
#   RT_OUT (output directory instead of .lake/build/runtime-nogmp), RT_EXTRA_CXXFLAGS (appended to
#   the compile flags of every runtime object, e.g. -flto=thin for scripts/build_release.sh),
#   RT_STAMP_EXTRA (extra text for the rebuild stamp, e.g. the hash of a PGO profile).
#
# usage: sh scripts/build_runtime_nogmp.sh [--relink EXE]...
#   --relink EXE  also relink the Lake executable EXE (elk, elktest; `lake build EXE` first) from
#                 its own link response file (.lake/build/bin/EXE.rsp) with -lleanrt -lgmp replaced
#                 by libleanrt_nogmp.a, into .lake/build/runtime-nogmp/bin/EXE; for A/B checks the
#                 unchanged response file is relinked the same way into bin/EXE-gmp.
#   --check       differential test of the big-number paths: tests/runtime/BignumDiff.lean is
#                 compiled with `lean -c`, linked against both runtimes and run; outputs must be
#                 byte-identical.
# The C library (scripts/build_ffi.sh) and the NAPI addon (scripts/build_napi.sh) select this
# runtime with ELK_NO_GMP=1.
set -eu
RELINK=""
CHECK=0
while [ $# -gt 0 ]; do
  case "$1" in
    --relink) [ $# -ge 2 ] || { echo "--relink needs an executable name" >&2; exit 2; }; RELINK="$RELINK $2"; shift 2 ;;
    --check) CHECK=1; shift ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
HERE=$(cd "$(dirname "$0")/.." && pwd)
cd "$HERE"
export PATH="$HOME/.elan/bin:$PATH"
REF="$HERE/.reference"
if [ ! -d "$REF" ]; then
  COMMON=$(git -C "$HERE" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)
  if [ -n "$COMMON" ]; then REF="$(dirname "$COMMON")/.reference"; fi
fi
LEAN_V=$(lean --short-version)
LEAN_PREFIX=$(lean --print-prefix)
LEAN_GITHASH=$(lean --githash)
LEAN_SRC=${LEAN_SRC_DIR:-"$REF/lean4-v$LEAN_V"}
DEPS=${DEPS:-"$HERE/.lake/runtime-nogmp-deps"}
JOBS=${JOBS:-3}
OUT=${RT_OUT:-"$HERE/.lake/build/runtime-nogmp"}
if [ -z "${CXX:-}" ]; then
  if [ "$(uname -s)" = Darwin ]; then
    # the toolchain's own clang (as for the Lean C), with the SDK's libc++ headers and the
    # toolchain's clang builtin headers (<prefix>/include/clang) as resource directory; in the
    # synthetic benchmark about 2-4 % faster than Apple clang (docs/gmp-licensing.md)
    mkdir -p "$OUT/clang-resource"
    ln -sfn "$LEAN_PREFIX/include/clang" "$OUT/clang-resource/include"
    CXX="$LEAN_PREFIX/bin/clang -x c++ -isysroot $(xcrun --show-sdk-path) -resource-dir $OUT/clang-resource"
  else
    CXX=c++
  fi
fi
RT="$LEAN_SRC/src/runtime"

[ -f "$RT/object.cpp" ] || { echo "error: Lean $LEAN_V sources not found at $LEAN_SRC (see scripts/build_wasm.sh)" >&2; exit 1; }
if [ -f "$LEAN_SRC/.git/HEAD" ]; then
  SRC_HEAD=$(cat "$LEAN_SRC/.git/HEAD")
  case "$SRC_HEAD" in
    *[!0-9a-f]*) ;;  # a branch ref: not checked
    *) [ "$SRC_HEAD" = "$LEAN_GITHASH" ] || { echo "error: $LEAN_SRC is at $SRC_HEAD, toolchain is $LEAN_GITHASH" >&2; exit 1; } ;;
  esac
fi
# the header the Lean C was compiled against must be the header of these sources
cmp -s "$LEAN_SRC/src/include/lean/lean.h" "$LEAN_PREFIX/include/lean/lean.h" \
  || { echo "error: lean.h of $LEAN_SRC differs from the toolchain's" >&2; exit 1; }

# --- pinned dependency sources -------------------------------------------------------------
MI_TAG=$(awk '/FetchContent_Declare\(/{getline n; if (n ~ /^ *mimalloc *$/) p=1; next} p && /GIT_TAG/{print $2; exit}' "$LEAN_SRC/CMakeLists.txt")
[ -n "$MI_TAG" ] || { echo "error: no mimalloc GIT_TAG in $LEAN_SRC/CMakeLists.txt" >&2; exit 1; }
UV_VER=$(strings -a "$LEAN_PREFIX/lib/libuv.a" | grep -E '^1\.[0-9]+\.[0-9]+$' | head -1)
[ -n "$UV_VER" ] || { echo "error: cannot read the libuv version of $LEAN_PREFIX/lib/libuv.a" >&2; exit 1; }
SSL_VER=$(strings -a "$LEAN_PREFIX/lib/libcrypto.a" | sed -n 's/^OpenSSL \([0-9]*\)\.\([0-9]*\)\.\([0-9]*\) .*/\1 \2 \3/p' | head -1)
[ -n "$SSL_VER" ] || { echo "error: cannot read the OpenSSL version of $LEAN_PREFIX/lib/libcrypto.a" >&2; exit 1; }
MI_SRC=${MIMALLOC_SRC_DIR:-"$DEPS/mimalloc-$MI_TAG"}
UV_SRC=${LIBUV_SRC_DIR:-"$DEPS/libuv-v$UV_VER"}
mkdir -p "$DEPS"
[ -f "$MI_SRC/src/static.c" ] || git clone -q --depth 1 --branch "$MI_TAG" https://github.com/microsoft/mimalloc "$MI_SRC"
[ -f "$UV_SRC/include/uv.h" ] || git clone -q --depth 1 --branch "v$UV_VER" https://github.com/libuv/libuv "$UV_SRC"
cmp -s "$MI_SRC/include/mimalloc.h" "$LEAN_PREFIX/include/lean/mimalloc.h" \
  || { echo "error: $MI_SRC/include/mimalloc.h differs from the toolchain's lean/mimalloc.h" >&2; exit 1; }

# --- generated headers ------------------------------------------------------------------------
GEN="$OUT/include"
mkdir -p "$GEN/openssl" "$OUT/obj"
printf '// generated by scripts/build_runtime_nogmp.sh (src/githash.h.in)\n#define LEAN_GITHASH "%s"\n' "$LEAN_GITHASH" > "$GEN/githash.h.tmp"
# shellcheck disable=SC2086
set -- $SSL_VER
SSL_NUM=$(printf '0x%x%02x00%02x0L' "$1" "$2" "$3")
printf '#pragma once\n// stub: openssl.cpp only reads the version of the toolchain OpenSSL (%s.%s.%s)\n#define OPENSSL_VERSION_NUMBER %s\n' "$1" "$2" "$3" "$SSL_NUM" > "$GEN/openssl/opensslv.h.tmp"
for f in githash.h openssl/opensslv.h; do
  if cmp -s "$GEN/$f.tmp" "$GEN/$f"; then rm "$GEN/$f.tmp"; else mv "$GEN/$f.tmp" "$GEN/$f"; fi
done
for f in err.h ssl.h; do [ -f "$GEN/openssl/$f" ] || printf '#pragma once\n' > "$GEN/openssl/$f"; done

# --- flags (release `leanrt`, minus -D LEAN_USE_GMP) ------------------------------------------
case "$(uname -s)" in
  # macOS: local-exec like the toolchain's leanrt (a bundle may still use it: Mach-O TLV)
  Darwin) PLAT_FLAGS=""; TLS_MODEL="-ftls-model=local-exec" ;;
  # Linux: local-exec cannot enter a shared object (the Node.js addon: ld rejects R_X86_64_TPOFF32
  # with -shared); initial-exec is what src/CMakeLists.txt sets for Lean's own Linux build, and the
  # linker relaxes it to local-exec inside an executable (the CLI)
  *) PLAT_FLAGS="-pthread"; TLS_MODEL="-ftls-model=initial-exec" ;;
esac
# CMAKE_CXX_FLAGS + CMAKE_CXX_FLAGS_RELEASE of src/CMakeLists.txt; `leanrt` adds the TLS model
CXXFLAGS="-Wall -Wextra -std=c++20 -D LEAN_MULTI_THREAD -ffp-contract=off -DLEAN_BUILD_TYPE=\"Release\" -DLEAN_EXPORTING -D__CLANG__ -fPIC -fvisibility=hidden -fvisibility-inlines-hidden $PLAT_FLAGS -O3 -DNDEBUG $TLS_MODEL ${RT_EXTRA_CXXFLAGS:-}"
INCLUDES="-I $LEAN_SRC/src -I $GEN -I $LEAN_PREFIX/include -I $UV_SRC/include"
# add_mimalloc_variant(mimalloc_local-exec OBJECT ${LEAN_MI_SECURE} ...)
MI_FLAGS="-I $MI_SRC/include -I $MI_SRC/src -DMI_SHARED_LIB -DMI_SHARED_LIB_EXPORT -O3 -DNDEBUG -DMI_WIN_NOREDIRECT -DMI_MAX_ALIGN_SIZE=8 -Wno-unused-function -Wno-deprecated -DMI_SECURE=0 $TLS_MODEL"

# RUNTIME_OBJS of src/runtime/CMakeLists.txt, plus mimalloc.cpp; the stamp covers compiler, flags and
# the generated headers (a change rebuilds everything), sources are compared by mtime
SOURCES=$(awk '/set\(/{p=0} /^ *RUNTIME_OBJS *$/{p=1; next} p && /^\)/{p=0} p{print $1}' "$RT/CMakeLists.txt")
[ -n "$SOURCES" ] || { echo "error: RUNTIME_OBJS not found in $RT/CMakeLists.txt" >&2; exit 1; }
STAMP=$(printf '%s\n' "$CXX" "$($CXX --version | head -1)" "$(cat "$GEN/githash.h" "$GEN/openssl/opensslv.h")" "$CXXFLAGS" "$INCLUDES" "$MI_FLAGS" "${RT_STAMP_EXTRA:-}" | shasum -a 256 | cut -c1-16)
if [ "$(cat "$OUT/obj/stamp" 2>/dev/null || true)" != "$STAMP" ]; then
  rm -rf "$OUT/obj"; mkdir -p "$OUT/obj"; echo "$STAMP" > "$OUT/obj/stamp"
fi
: > "$OUT/jobs.txt"
OBJS=""
for f in $SOURCES mimalloc.cpp; do
  o="$OUT/obj/$(echo "$f" | tr / _ | sed 's/\.cpp$/.o/')"
  OBJS="$OBJS $o"
  if [ ! -f "$o" ] || [ "$RT/$f" -nt "$o" ]; then
    if [ "$f" = mimalloc.cpp ]; then extra="$MI_FLAGS"; else extra=""; fi
    echo "$CXX -c $RT/$f -o $o.tmp $CXXFLAGS $extra $INCLUDES && mv $o.tmp $o" >> "$OUT/jobs.txt"
  fi
done
N=$(wc -l < "$OUT/jobs.txt" | tr -d ' ')
echo "Lean runtime without GMP: $(echo $OBJS | wc -w | tr -d ' ') objects, $N to (re)build (mimalloc $MI_TAG, libuv $UV_VER headers)"
if [ "$N" -gt 0 ]; then
  # one shell per compile; warnings are shown (the release build is not warning free either)
  tr '\n' '\0' < "$OUT/jobs.txt" | xargs -0 -P "$JOBS" -n 1 sh -c
fi
mkdir -p "$OUT/lib"
LIB="$OUT/lib/libleanrt_nogmp.a"
rm -f "$LIB"
# shellcheck disable=SC2086
"${AR:-ar}" rcs "$LIB" $OBJS
if nm "$LIB" 2>/dev/null | grep -q '__gmp'; then echo "error: $LIB references GMP" >&2; exit 1; fi
cat > "$OUT/BUILD_INFO.txt" <<EOF
lean: $(lean --version) ($LEAN_GITHASH)
lean sources: $LEAN_SRC
mimalloc: $MI_SRC ($MI_TAG)
libuv headers: $UV_SRC ($UV_VER), library: $LEAN_PREFIX/lib/libuv.a
openssl: stub opensslv.h ($SSL_NUM)
compiler: $($CXX --version | head -1)
cxxflags: $CXXFLAGS
mimalloc flags: $MI_FLAGS
includes: $INCLUDES
sources: $(echo $SOURCES) mimalloc.cpp
EOF
echo "built $LIB ($(wc -c < "$LIB" | tr -d ' ') bytes, no __gmp symbols)"

# --- relink Lake executables ------------------------------------------------------------------
# Lake links with `<linker> -o BIN @BIN.rsp` (Lake.compileExe), the response file holding the
# objects and the toolchain ldflags; the linker is the toolchain clang (-fuse-ld=lld in the file),
# run with MACOSX_DEPLOYMENT_TARGET=99.0 like Lake (BIN-gmp equals Lake's BIN except for the output
# name, which enters LC_UUID and the ad-hoc code signature).
for exe in $RELINK; do
  RSP="$HERE/.lake/build/bin/$exe.rsp"
  [ -f "$RSP" ] || { echo "error: $RSP not found (run \`lake build $exe\` first)" >&2; exit 1; }
  grep -qx '"-lleanrt"' "$RSP" && grep -qx '"-lgmp"' "$RSP" \
    || { echo "error: $RSP does not link -lleanrt -lgmp" >&2; exit 1; }
  mkdir -p "$OUT/bin"
  if [ "$(uname -s)" = Darwin ]; then
    sed -e "s|^\"-lleanrt\"\$|\"$LIB\"|" -e '/^"-lgmp"$/d' "$RSP" > "$OUT/bin/$exe.rsp"
    cp "$RSP" "$OUT/bin/$exe-gmp.rsp"
    for v in "$exe" "$exe-gmp"; do
      MACOSX_DEPLOYMENT_TARGET=99.0 "$LEAN_PREFIX/bin/clang" -o "$OUT/bin/$v" "@$OUT/bin/$v.rsp"
    done
    echo "relinked $OUT/bin/$exe (no GMP) and $OUT/bin/$exe-gmp (toolchain runtime, same link)"
  else
    # Linux: Lake's response file is the toolchain's sysroot/lld link of its libc++-built leanrt; the
    # runtime here comes from the system C++ compiler, so the same objects (Lake's Lean C and the C
    # shim archive) are linked with it, libstdc++ and libgcc static (scripts/build_ffi.sh links the
    # C API the same way); the toolchain's static libuv is reused
    grep -E '\.(o|o\.export|a)"$' "$RSP" | tr -d '"' > "$OUT/bin/$exe.objects"
    # shellcheck disable=SC2086
    "${CXX_LD:-c++}" -o "$OUT/bin/$exe" "@$OUT/bin/$exe.objects" \
      -L"$LEAN_PREFIX/lib/lean" -L"$LEAN_PREFIX/lib" -Wl,--start-group -lInit -lStd "$LIB" -Wl,--end-group \
      -luv -lm -lpthread -ldl -static-libstdc++ -static-libgcc -Wl,--gc-sections
    echo "relinked $OUT/bin/$exe (no GMP; system C++ link, libstdc++ static)"
  fi
  if nm "$OUT/bin/$exe" 2>/dev/null | grep -q '__gmp'; then echo "error: $OUT/bin/$exe contains GMP" >&2; exit 1; fi
done

# --- big-number differential test -------------------------------------------------------------
if [ "$CHECK" = 1 ]; then
  T="$OUT/check"
  mkdir -p "$T"
  lean tests/runtime/BignumDiff.lean -c "$T/BignumDiff.c"
  leanc -c -O3 -DNDEBUG -o "$T/BignumDiff.o" "$T/BignumDiff.c"
  LINK="--sysroot $LEAN_PREFIX -L $LEAN_PREFIX/lib -L $LEAN_PREFIX/lib/libc -fuse-ld=lld -L $LEAN_PREFIX/lib/lean -lInit -lStd"
  case "$(uname -s)" in Darwin) TAIL="-lc++ -luv -Wl,-dead_strip" ;; *) TAIL="-luv -lstdc++ -lm -lpthread -ldl -Wl,--gc-sections" ;; esac
  # shellcheck disable=SC2086
  MACOSX_DEPLOYMENT_TARGET=99.0 "$LEAN_PREFIX/bin/clang" -o "$T/bignum-gmp" "$T/BignumDiff.o" $LINK -lleanrt -lgmp $TAIL
  # shellcheck disable=SC2086
  MACOSX_DEPLOYMENT_TARGET=99.0 "$LEAN_PREFIX/bin/clang" -o "$T/bignum-nogmp" "$T/BignumDiff.o" $LINK "$LIB" $TAIL
  if nm "$T/bignum-nogmp" 2>/dev/null | grep -q '__gmp'; then echo "error: $T/bignum-nogmp contains GMP" >&2; exit 1; fi
  nm "$T/bignum-gmp" 2>/dev/null | grep -q '__gmp' || { echo "error: $T/bignum-gmp does not use GMP" >&2; exit 1; }
  "$T/bignum-gmp" > "$T/gmp.txt"
  "$T/bignum-nogmp" > "$T/nogmp.txt"
  if cmp -s "$T/gmp.txt" "$T/nogmp.txt"; then
    echo "check: big-number differential test identical ($(wc -l < "$T/gmp.txt" | tr -d ' ') lines, $(wc -c < "$T/gmp.txt" | tr -d ' ') bytes)"
  else
    echo "check: MISMATCH between the GMP and the no-GMP runtime:"; diff "$T/gmp.txt" "$T/nogmp.txt" | head -20; exit 1
  fi
fi
