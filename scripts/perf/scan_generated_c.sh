#!/bin/sh
# Static checks of the generated C (.lake/build/ir) for known Lean performance traps:
#   1. run-time Float.ofScientific / Float.ofNat / Float.ofInt calls (should only be the FastFloat
#      fallbacks in FastFloat.c; the core abbreviations Nat.toFloat / Int.toFloat need their own csimp),
#   2. run-time big Nat/Int literals (lean_cstr_to_nat / lean_cstr_to_int: GMP parse per evaluation),
#   3. functions boxing floats (lean_box_float) — usually loop states with several Float variables.
# usage: sh scripts/perf/scan_generated_c.sh [path-filter, e.g. Elk/Alg/Layered/P3Order]
set -eu
HERE=$(cd "$(dirname "$0")/../.." && pwd)
FILTER=${1:-}
find "$HERE/.lake/build/ir/Elk" -name '*.c' | grep "$FILTER" | while read -r f; do
  awk -v F="${f#"$HERE"/.lake/build/ir/}" '
    /^[A-Za-z_].*\(.*\)[ ]*\{[ ]*$/ { fn=$0; sub(/\(.*/, "", fn); n=split(fn, parts, " "); fn=parts[n]; sub(/^lp_elk_x2dlean_/, "", fn); next }
    fn ~ /^_init_/ || fn ~ /___boxed$/ { next }
    /l_Float_ofScientific\(/ { k["ofScientific\t" fn]++ }
    /l_Float_ofNat\(/ { k["ofNat\t" fn]++ }
    /l_Float_ofInt\(/ { k["ofInt\t" fn]++ }
    /lean_cstr_to_nat\(|lean_cstr_to_int\(/ { k["bigLiteral\t" fn]++ }
    /lean_box_float\(/ { k["boxFloat\t" fn]++ }
    END { for (x in k) printf "%s\t%d\t%s\n", substr(x, 1, index(x, "\t") - 1), k[x], F "\t" substr(x, index(x, "\t") + 1) }
  ' "$f"
done | sort | awk -F'\t' '{printf "%-12s %4s  %s  %s\n", $1, $2, $3, substr($4, 1, 120)}'
