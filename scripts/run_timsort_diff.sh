#!/bin/sh
# Differential test of Elk.Core.Util.JavaSort (port of OpenJDK 21 java.util.TimSort) against a real
# JDK: scripts/java/TimSortTrace.java sorts 13,767 generated cases (sizes 0..5,000, 13 consistent /
# inconsistent / throwing comparators, 7 key distributions) with Collections.sort and records the
# outcome, the comparator call sequence hash and the permutation hash; the Lean suite
# core.util.JavaSort.full replays every case and must agree on all three.
#   sh scripts/run_timsort_diff.sh [out_dir]          (default tests/tmp/timsort)
#   sh scripts/run_timsort_diff.sh --fixture          regenerate tests/fixtures/timsort/cases.jsonl
# JDK from mise (ELK_JAVA_TOOL, default java@temurin-21.0.13+9.0.LTS, as run_java_baseline.sh).
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
JAVA_TOOL=${ELK_JAVA_TOOL:-java@temurin-21.0.13+9.0.LTS}
run() { mise exec "$JAVA_TOOL" -- "$@"; }
OUT=tests/tmp/timsort
MODE=full
if [ "${1:-}" = "--fixture" ]; then MODE=fixture; elif [ -n "${1:-}" ]; then OUT=$1; fi
cd "$HERE"
mkdir -p "$OUT/classes"
run javac -nowarn -d "$OUT/classes" scripts/java/TimSortTrace.java
run java -version 2>&1 | head -1
if [ "$MODE" = fixture ]; then
  mkdir -p tests/fixtures/timsort
  run java -cp "$OUT/classes" TimSortTrace gen tests/fixtures/timsort/cases.jsonl fixture
  exit 0
fi
run java -cp "$OUT/classes" TimSortTrace gen "$OUT/cases.jsonl" full
export PATH="$HOME/.elan/bin:$PATH"
ELK_TIMSORT_CASES="$OUT/cases.jsonl" lake test -- --suite core.util.JavaSort.full
