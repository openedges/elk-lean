#!/bin/sh
# Release build of the native CLI with link-time optimisation across the Lean C of every Elk module
# and the GMP-free Lean runtime, and profile-guided optimisation when a profile exists
# (docs/build-optimization.md):
#   .lake/build/release/bin/elk        the release CLI (no GMP, ThinLTO, PGO)
#   .lake/build/release/BUILD_INFO.txt toolchain, flags, profile
# Intermediate files: .lake/build/release/{obj,runtime,lto-cache} (incremental: objects are rebuilt
# when their C file is newer or the compiler/flags/profile change).
#
# The Lean C is Lake's own (`lake build elk`, .lake/build/ir/**.c) compiled again with exactly the
# flags Lake uses (`leanc --print-cflags`, -O3 -DNDEBUG, the package's -fPIC -DLEAN_EXPORTING; with
# no extra flag the objects are bit-identical to Lake's) plus -flto=thin; the runtime is
# scripts/build_runtime_nogmp.sh with -flto=thin (RT_OUT=.lake/build/release/runtime), so that
# lean_alloc_small_object_core / mi_free / lean_dec_ref_cold inline into the generated code. The
# link is Lake's own response file (.lake/build/bin/elk.rsp) with the objects replaced, -lleanrt
# -lgmp replaced by the LTO runtime, and the toolchain clang + ld64.lld doing the ThinLTO backend.
# Floating-point flags are untouched (-ffp-contract=off as in leanc); the layouts are byte-identical
# to the Lake build (checked by docs/build-optimization.md's identity gate, quick check: --check).
#
# usage: sh scripts/build_release.sh [--no-pgo] [--no-lto] [--pgo-generate PROFILE_RT.a] [--out DIR] [--check]
#   --no-pgo        ignore the profile even when present
#   --no-lto        plain objects (no -flto) with the plain no-GMP runtime
#   --pgo-generate  instrumented build for scripts/build_pgo.sh (links the given profile runtime);
#                   defaults --out to .lake/build/release-pgogen
#   --out DIR       output directory instead of .lake/build/release
#   --check         lay out a few corpus models and synthetic inputs with the Lake build and the
#                   release build and compare the bytes
# env:
#   ELK_PGO_PROFILE  profile (default: <main checkout>/.reference/pgo/elk-lean-<lean version>-<arch>.profdata,
#                    written by scripts/build_pgo.sh; used when the file exists)
#   ELK_NATIVE_CPU=1 add -mcpu=native (local builds only: distributed artefacts keep the default
#                    target CPU, apple-m1 on macOS arm64)
#   JOBS             parallel compiles and ThinLTO backend jobs (default 3)
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
cd "$HERE"
export PATH="$HOME/.elan/bin:$PATH"
REF="$HERE/.reference"
if [ ! -d "$REF" ]; then
  COMMON=$(git -C "$HERE" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)
  if [ -n "$COMMON" ]; then REF="$(dirname "$COMMON")/.reference"; fi
fi
PGO=1
LTO=1
GEN=""
OUT=""
CHECK=0
while [ $# -gt 0 ]; do
  case "$1" in
    --no-pgo) PGO=0; shift ;;
    --no-lto) LTO=0; shift ;;
    --pgo-generate) [ $# -ge 2 ] || { echo "--pgo-generate needs the profile runtime archive" >&2; exit 2; }; GEN=$2; PGO=0; shift 2 ;;
    --out) [ $# -ge 2 ] || { echo "--out needs a directory" >&2; exit 2; }; OUT=$2; shift 2 ;;
    --check) CHECK=1; shift ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
JOBS=${JOBS:-3}
LEAN_V=$(lean --short-version)
LEAN_PREFIX=$(lean --print-prefix)
CC="$LEAN_PREFIX/bin/clang"
case "$(uname -s)" in Darwin) SDK=$(xcrun --show-sdk-path) ;; *) SDK=/ ;; esac
if [ -z "$OUT" ]; then
  if [ -n "$GEN" ]; then OUT="$HERE/.lake/build/release-pgogen"; else OUT="$HERE/.lake/build/release"; fi
fi
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
ARCH=$(uname -m)
PROFILE=${ELK_PGO_PROFILE:-"$REF/pgo/elk-lean-$LEAN_V-$(uname -s | tr 'A-Z' 'a-z')-$ARCH.profdata"}
if [ "$PGO" = 1 ] && [ ! -f "$PROFILE" ]; then
  echo "note: no PGO profile at $PROFILE (scripts/build_pgo.sh), building without PGO" >&2
  PGO=0
fi

# --- Lean C and Lake's link line ----------------------------------------------------------------
lake build elk ElkFfi:static >/dev/null
RSP="$HERE/.lake/build/bin/elk.rsp"
grep -qx '"-lleanrt"' "$RSP" && grep -qx '"-lgmp"' "$RSP" \
  || { echo "error: $RSP does not link -lleanrt -lgmp" >&2; exit 1; }

# --- flags --------------------------------------------------------------------------------------
# what Lake passes to the toolchain clang for every module (Lake.compileO + leanc + lakefile)
BASE_CFLAGS="$(leanc --print-cflags) -Wno-unused-command-line-argument --sysroot $LEAN_PREFIX -nostdinc -isystem $LEAN_PREFIX/include/clang -O3 -DNDEBUG -fPIC -DLEAN_EXPORTING"
EXTRA=""
LDEXTRA=""
RT_EXTRA=""
if [ "$LTO" = 1 ]; then
  EXTRA="-flto=thin"
  RT_EXTRA="-flto=thin"
  mkdir -p "$OUT/lto-cache"
  case "$(uname -s)" in Darwin) CACHE="-Wl,-cache_path_lto,$OUT/lto-cache" ;; *) CACHE="-Wl,--thinlto-cache-dir=$OUT/lto-cache" ;; esac
  LDEXTRA="-flto=thin -Wl,--thinlto-jobs=$JOBS $CACHE"
fi
if [ "${ELK_NATIVE_CPU:-0}" = 1 ]; then EXTRA="$EXTRA -mcpu=native"; RT_EXTRA="$RT_EXTRA -mcpu=native"; fi
PROFILE_HASH=none
if [ -n "$GEN" ]; then
  [ -f "$GEN" ] || { echo "error: profile runtime $GEN not found" >&2; exit 1; }
  EXTRA="$EXTRA -fprofile-generate"
  RT_EXTRA="$RT_EXTRA -fprofile-generate"
  LDEXTRA="$LDEXTRA $GEN"
elif [ "$PGO" = 1 ]; then
  PROFILE_HASH=$(shasum -a 256 "$PROFILE" | cut -c1-16)
  # a profile of an older source tree is still valid: functions whose control flow changed are
  # compiled without profile (the warnings would only repeat that)
  PGO_FLAGS="-fprofile-use=$PROFILE -Wno-profile-instr-out-of-date -Wno-profile-instr-unprofiled -Wno-backend-plugin"
  EXTRA="$EXTRA $PGO_FLAGS"
  RT_EXTRA="$RT_EXTRA $PGO_FLAGS"
fi

# --- Lean runtime without GMP (LTO bitcode when LTO=1) ------------------------------------------
if [ "$LTO" = 1 ]; then RT_AR="$LEAN_PREFIX/bin/llvm-ar"; else RT_AR=ar; fi
RT_OUT="$OUT/runtime" RT_EXTRA_CXXFLAGS="$RT_EXTRA" RT_STAMP_EXTRA="$PROFILE_HASH" AR="$RT_AR" sh scripts/build_runtime_nogmp.sh > "$OUT/runtime.log" 2>&1 \
  || { tail -20 "$OUT/runtime.log"; exit 1; }
LIB="$OUT/runtime/lib/libleanrt_nogmp.a"

# --- compile ------------------------------------------------------------------------------------
OBJ="$OUT/obj"
STAMP=$(printf '%s\n' "$($CC --version | head -1)" "$BASE_CFLAGS" "$EXTRA" "$PROFILE_HASH" | shasum -a 256 | cut -c1-16)
if [ "$(cat "$OBJ/stamp" 2>/dev/null || true)" != "$STAMP" ]; then
  rm -rf "$OBJ"; mkdir -p "$OBJ"; echo "$STAMP" > "$OBJ/stamp"
fi
IR="$HERE/.lake/build/ir"
: > "$OBJ/jobs.txt"
# every module Lake compiled (Main, all Elk.* incl. Elk.Ffi for the NAPI addon): <M>.c -> obj/<M>.c.o
find "$IR/Elk" -name '*.c.o.export' | LC_ALL=C sort > "$OBJ/sources.txt"
echo "$IR/Main.c.o.export" >> "$OBJ/sources.txt"
N_OBJ=0
while IFS= read -r x; do
  src=${x%.o.export}
  o="$OBJ/${src#"$IR"/}.o"
  N_OBJ=$((N_OBJ + 1))
  if [ ! -f "$o" ] || [ "$src" -nt "$o" ]; then
    echo "mkdir -p '$(dirname "$o")' && '$CC' -c -o '$o.tmp' '$src' $BASE_CFLAGS $EXTRA && mv '$o.tmp' '$o'" >> "$OBJ/jobs.txt"
  fi
done < "$OBJ/sources.txt"
# the C API glue of the NAPI addon / C library (scripts/build_ffi.sh's flags, toolchain clang)
FFI_CFLAGS="-O3 -DNDEBUG -fPIC -std=c11 -isysroot $SDK -isystem $LEAN_PREFIX/include/clang -I $LEAN_PREFIX/include -I $HERE/plugins/org.eclipse.elk.ffi/include"
GLUE="$OBJ/elk_lean.o"
if [ ! -f "$GLUE" ] || [ "$HERE/plugins/org.eclipse.elk.ffi/c/elk_lean.c" -nt "$GLUE" ]; then
  echo "'$CC' -c -o '$GLUE.tmp' '$HERE/plugins/org.eclipse.elk.ffi/c/elk_lean.c' $FFI_CFLAGS $EXTRA && mv '$GLUE.tmp' '$GLUE'" >> "$OBJ/jobs.txt"
fi
# CLI link line: Lake's response file (one quoted argument per line) with the objects replaced
: > "$OUT/elk.rsp"
while IFS= read -r line; do
  arg=$(printf '%s' "$line" | sed 's/^"\(.*\)"$/\1/')
  case "$arg" in
    "$IR"/*.c.o.export) src=${arg%.o.export}; printf '"%s"\n' "$OBJ/${src#"$IR"/}.o" >> "$OUT/elk.rsp" ;;
    -lleanrt) printf '"%s"\n' "$LIB" >> "$OUT/elk.rsp" ;;
    -lgmp) ;;
    *) printf '%s\n' "$line" >> "$OUT/elk.rsp" ;;
  esac
done < "$RSP"
# objects of the NAPI addon (scripts/build_napi.sh --release): every Elk module + the glue
grep -v '/Main\.c\.o\.export$' "$OBJ/sources.txt" | sed -e "s|^$IR/|$OBJ/|" -e 's|\.o\.export$|.o|' > "$OUT/ffi_objects.txt"
echo "$GLUE" >> "$OUT/ffi_objects.txt"
for a in $LDEXTRA; do printf '"%s"\n' "$a" >> "$OUT/elk.rsp"; done
N=$(wc -l < "$OBJ/jobs.txt" | tr -d ' ')
echo "release build: $N_OBJ Lean C objects, $N to (re)build (LTO=$LTO, PGO=$PGO$([ -n "$GEN" ] && echo ", instrumented"))"
T0=$(date +%s)
if [ "$N" -gt 0 ]; then
  tr '\n' '\0' < "$OBJ/jobs.txt" | xargs -0 -P "$JOBS" -n 1 sh -c
fi
T1=$(date +%s)

# --- link ---------------------------------------------------------------------------------------
mkdir -p "$OUT/bin"
# as Lake (Lake.compileExe): `clang -o BIN @BIN.rsp` with MACOSX_DEPLOYMENT_TARGET=99.0
MACOSX_DEPLOYMENT_TARGET=99.0 "$CC" -o "$OUT/bin/elk.tmp" "@$OUT/elk.rsp" 2> "$OUT/link.log" \
  || { cat "$OUT/link.log"; exit 1; }
mv "$OUT/bin/elk.tmp" "$OUT/bin/elk"
T2=$(date +%s)
if nm "$OUT/bin/elk" 2>/dev/null | grep -q '__gmp'; then echo "error: $OUT/bin/elk contains GMP" >&2; exit 1; fi
cat > "$OUT/BUILD_INFO.txt" <<EOF
lean: $(lean --version)
compiler: $($CC --version | head -1)
cflags: $BASE_CFLAGS $EXTRA
runtime: $LIB ($(grep '^cxxflags:' "$OUT/runtime/BUILD_INFO.txt" | cut -c11-))
ldextra: $LDEXTRA
pgo profile: $([ "$PGO" = 1 ] && echo "$PROFILE ($PROFILE_HASH)" || echo none)
EOF
echo "built $OUT/bin/elk ($(wc -c < "$OUT/bin/elk" | tr -d ' ') bytes, no GMP; compile $((T1 - T0)) s, link $((T2 - T1)) s)"

# --- quick byte-identity check against the Lake build ---------------------------------------------
if [ "$CHECK" = 1 ]; then
  T=$(mktemp -d)
  n=0; bad=0
  for f in "$REF"/java-baseline/synthetic/bench_inputs/*.json; do
    [ -f "$f" ] || continue
    n=$((n + 1))
    .lake/build/bin/elk layout "$f" > "$T/a.json" 2>&1 || true
    "$OUT/bin/elk" layout "$f" > "$T/b.json" 2>&1 || true
    cmp -s "$T/a.json" "$T/b.json" || { bad=$((bad + 1)); echo "check: differs: $f"; }
  done
  rm -rf "$T"
  echo "check: $n synthetic inputs, $bad differ"
  [ "$bad" = 0 ] || exit 1
fi
