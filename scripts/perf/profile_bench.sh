#!/bin/sh
# Samples `elk bench --scenarios SCENARIO` with macOS `sample` and prints the hottest functions.
#   sh scripts/perf/profile_bench.sh SCENARIO [seconds=5] [out=tests/tmp/profile_<scenario>.txt]
# Then: python3 scripts/perf/sample_inclusive.py OUT 'REGEX'   (inclusive time per matching frame)
#       python3 scripts/perf/sample_callers.py OUT 'REGEX'     (who calls e.g. allocation/copy functions)
# Env: ELK_LEAN_BIN (default .lake/build/bin/elk). The scenario names are those of `elk bench`.
set -eu
HERE=$(cd "$(dirname "$0")/../.." && pwd)
SC=$1
SECS=${2:-5}
OUT=${3:-"$HERE/tests/tmp/profile_$SC.txt"}
BIN=${ELK_LEAN_BIN:-"$HERE/.lake/build/bin/elk"}
mkdir -p "$(dirname "$OUT")"
"$BIN" bench --scenarios "$SC" --iterations 100000 --warmup 0 --output /dev/null 2>/dev/null &
PID=$!
sleep 0.5
sample "$PID" "$SECS" -file "$OUT" >/dev/null 2>&1 || true
kill "$PID" 2>/dev/null || true
wait "$PID" 2>/dev/null || true
echo "profile: $OUT"
awk '/Sort by top of stack/{f=1; next} f' "$OUT" | grep -v '__ulock_wait\|kevent\|__psynch' | head -30 \
  | awk '{c=$NF; $NF=""; print c, $0}' \
  | sed 's/lp_elk_x2dlean_//; s/__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00/LOOP@/; s/__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00/ALOOP@/g; s/__private_Init_While_0__repeatM_erased___at___00/WHILE@/; s/(in [^)]*)//' \
  | cut -c1-160
