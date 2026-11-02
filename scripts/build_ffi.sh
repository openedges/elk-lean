#!/bin/sh
# Builds the elk-lean C library for embedding hosts (NAPI addon, WASM, others):
#   .lake/build/ffi/libelklean.a   every Elk.* module object + C shims + include/elk_lean.h glue
#   .lake/build/ffi/include/elk_lean.h
#   .lake/build/ffi/smoke          native smoke test (tests/ffi/smoke.c)
#   .lake/build/ffi/ldflags        extra linker flags (Lean runtime libraries) for hosts
#   .lake/build/ffi/ld             the link driver those flags are for (`cc`; Linux no-GMP: `c++`)
#   .lake/build/ffi/runtime        `gmp` (toolchain libleanrt.a + libgmp.a) or `nogmp`
#   .lake/build/ffi/libleanrt_nogmp.a   (ELK_NO_GMP=1 only) the Lean runtime the ldflags refer to
# usage: sh scripts/build_ffi.sh [--check]   (--check: compare the smoke output with `elk layout`)
# env: ELK_NO_GMP=1  link the Lean runtime rebuilt without GMP (scripts/build_runtime_nogmp.sh,
#                    docs/gmp-licensing.md) instead of the toolchain's -lleanrt -lgmp; libelklean.a
#                    itself is the same in both modes, only ldflags (and the smoke binary) change.
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
cd "$HERE"
export PATH="$HOME/.elan/bin:$PATH"
LEAN_PREFIX=$(lean --print-prefix)
OUT="$HERE/.lake/build/ffi"
mkdir -p "$OUT/include" "$OUT/obj"
# `elk` links every Elk.* module; `ElkFfi:static` adds the objects of Elk.Ffi itself
lake build elk ElkFfi:static >/dev/null
cp plugins/org.eclipse.elk.ffi/include/elk_lean.h "$OUT/include/"
CFLAGS="-O3 -DNDEBUG -fPIC -std=c11 -I $LEAN_PREFIX/include -I plugins/org.eclipse.elk.ffi/include"
cc $CFLAGS -c plugins/org.eclipse.elk.ffi/c/elk_lean.c -o "$OUT/obj/elk_lean.o"
find .lake/build/ir/Elk -name '*.c.o.export' | LC_ALL=C sort > "$OUT/objects.txt"
echo "$HERE/.lake/build/c/elk_core_ffi.o" >> "$OUT/objects.txt"
echo "$OUT/obj/elk_lean.o" >> "$OUT/objects.txt"
rm -f "$OUT/libelklean.a"
# shellcheck disable=SC2046
ar rcs "$OUT/libelklean.a" $(cat "$OUT/objects.txt")
if [ "${ELK_NO_GMP:-0}" = 1 ]; then
  sh scripts/build_runtime_nogmp.sh
  RUNTIME=nogmp
  # next to libelklean.a, so that the directory is a self-contained C library bundle
  cp .lake/build/runtime-nogmp/lib/libleanrt_nogmp.a "$OUT/"
  LEANRT="-L$OUT -lleanrt_nogmp"
  GMP=""
else
  RUNTIME=gmp
  rm -f "$OUT/libleanrt_nogmp.a"
  LEANRT="-lleanrt"
  GMP="-lgmp"
fi
# Linux: the C++ runtime is linked with the system C++ driver (`c++`), libstdc++ and libgcc static
# so that a host needs nothing beyond glibc; the toolchain's libleanrt.a (GMP mode) is built with
# the toolchain's libc++, so that mode links it with the toolchain's static libc++ instead
case "$(uname -s)" in
  Darwin) LD=cc; LDFLAGS="-L$LEAN_PREFIX/lib/lean -L$LEAN_PREFIX/lib -lInit -lStd $LEANRT $GMP -luv -lc++ -Wl,-dead_strip" ;;
  *)
    if [ "$RUNTIME" = nogmp ]; then
      LD=${CXX_LD:-c++}; CXXLIBS="-static-libstdc++ -static-libgcc"
    else
      LD=cc; CXXLIBS="-Wl,-Bstatic -lc++ -lc++abi -lunwind -Wl,-Bdynamic"
    fi
    LDFLAGS="-L$LEAN_PREFIX/lib/lean -L$LEAN_PREFIX/lib -Wl,--start-group -lInit -lStd $LEANRT -Wl,--end-group $GMP -luv -lm -lpthread -ldl $CXXLIBS -Wl,--gc-sections" ;;
esac
LDFLAGS=$(echo "$LDFLAGS" | tr -s ' ')
echo "$LDFLAGS" > "$OUT/ldflags"
echo "$LD" > "$OUT/ld"
echo "$RUNTIME" > "$OUT/runtime"
# shellcheck disable=SC2086
cc $CFLAGS -c tests/ffi/smoke.c -o "$OUT/obj/smoke.o"
# shellcheck disable=SC2086
$LD "$OUT/obj/smoke.o" "$OUT/libelklean.a" $LDFLAGS -o "$OUT/smoke"
echo "built $OUT/libelklean.a ($(wc -l < "$OUT/objects.txt" | tr -d ' ') objects), $OUT/smoke (Lean runtime: $RUNTIME)"
if [ "$RUNTIME" = nogmp ] && nm "$OUT/smoke" 2>/dev/null | grep -q '__gmp'; then
  echo "error: $OUT/smoke contains GMP symbols" >&2; exit 1
fi
if [ "${1:-}" = "--check" ]; then
  T=$(mktemp -d)
  printf '%s' '{"id":"root","children":[{"id":"a","width":30,"height":20},{"id":"b","width":30,"height":20}],"edges":[{"id":"e","sources":["a"],"targets":["b"]}]}' > "$T/g.json"
  "$OUT/smoke" "$T/g.json" '{}' > "$T/ffi.json"
  .lake/build/bin/elk layout "$T/g.json" --sort-keys > "$T/cli.json"
  if cmp -s "$T/ffi.json" "$T/cli.json"; then echo "smoke: layout identical to elk layout --sort-keys"; else echo "smoke: MISMATCH"; diff "$T/ffi.json" "$T/cli.json" | head; exit 1; fi
  # parallel sibling layout (elk_lean_init_threads, every sibling sub-graph on a task): thread caps 1
  # and 4 give the bytes of `elk layout --sort-keys`
  python3 -c "import json; print(json.dumps({'id':'root','children':[{'id':'c%d'%c,'children':[{'id':'c%d_%d'%(c,i),'width':20,'height':10+i} for i in range(6)],'edges':[{'id':'c%d_e%d'%(c,i),'sources':['c%d_%d'%(c,i-1)],'targets':['c%d_%d'%(c,i)]} for i in range(1,6)]} for c in range(5)]}))" > "$T/h.json"
  ELK_LEAN_PAR_MIN_WORK=0 "$OUT/smoke" --threads 1 "$T/h.json" '{}' > "$T/h1.json"
  ELK_LEAN_PAR_MIN_WORK=0 "$OUT/smoke" --threads 4 "$T/h.json" '{}' > "$T/h4.json"
  .lake/build/bin/elk layout "$T/h.json" --sort-keys > "$T/hcli.json"
  if cmp -s "$T/h1.json" "$T/hcli.json" && cmp -s "$T/h4.json" "$T/hcli.json"; then echo "smoke: threads 1 and 4 identical to elk layout --sort-keys"
  else echo "smoke: threads MISMATCH"; exit 1; fi
  "$OUT/smoke" --algorithms > "$T/algs.json"
  python3 -c "import json,sys; a=json.load(open(sys.argv[1])); print('smoke: algorithms', len(a))" "$T/algs.json"
  if "$OUT/smoke" "$T/g.json" '{"elk.algorithm":"doesNotExist"}' 2> "$T/err.txt"; then echo "smoke: expected an error"; exit 1; fi
  echo "smoke: error path ok: $(head -c 100 "$T/err.txt")"
  printf 'algorithm: layered\nnode a { label "A" }\nnode b { port p }\nedge a -> b.p\n' > "$T/g.elkt"
  "$OUT/smoke" --convert "$T/g.elkt" > "$T/ffi_convert.json"
  .lake/build/bin/elk convert "$T/g.elkt" > "$T/cli_convert.json"
  "$OUT/smoke" --convert "$T/g.elkt" 5 > "$T/ffi_convert_ds.json"
  .lake/build/bin/elk convert "$T/g.elkt" --defaults --sort-keys > "$T/cli_convert_ds.json"
  if cmp -s "$T/ffi_convert.json" "$T/cli_convert.json" && cmp -s "$T/ffi_convert_ds.json" "$T/cli_convert_ds.json"; then
    echo "smoke: convert identical to elk convert (plain, --defaults --sort-keys)"
  else echo "smoke: convert MISMATCH"; diff "$T/ffi_convert.json" "$T/cli_convert.json" | head; exit 1; fi
  printf 'node a\nedge a -> \n' > "$T/bad.elkt"
  if "$OUT/smoke" --convert "$T/bad.elkt" 2> "$T/cerr.txt"; then echo "smoke: expected a convert error"; exit 1; fi
  .lake/build/bin/elk convert "$T/bad.elkt" 2> "$T/cli_cerr.txt" || true
  if cmp -s "$T/cerr.txt" "$T/cli_cerr.txt"; then echo "smoke: convert error ok: $(head -c 100 "$T/cerr.txt")"
  else echo "smoke: convert error MISMATCH"; cat "$T/cerr.txt" "$T/cli_cerr.txt"; exit 1; fi
  rm -rf "$T"
fi
