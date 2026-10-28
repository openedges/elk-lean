#!/bin/sh
# Random-graph result parity against ELK Java 0.12.0 (the result baseline), with error texts and
# outcomes (ok / exception / timeout / stack overflow) on both sides.
#   sh scripts/run_random_java_parity.sh <out_dir> [--seeds 1-10] [--count 600] [--sets s,v]
#       [--timeout 15] [--jobs 3] [--java-jobs 2] [--java-timeout 60] [--java-set-timeout 1800]
#       [--with-oracle] [--force] [--stages gen,java,lean,rs,report] [--no-publish]
# 1. generate `gen_nodesize_graphs.py <dir> <count> <seed>` per seed ("s" sets; the generator's seed
#    semantics are kept, so seed k reproduces agent HX's set k) and the copies sanitised for ELK
#    Java's node size validation ("v" sets, `sanitize_for_java.py`); "o" sets (`--sets o`,
#    `gen_option_graphs.py`) are flat graphs of the non-layered algorithms with random values of
#    their own options (force model, stress dimension, radial compactor/sorter, mrtree routing, ...);
#    "p" sets (`--sets p`, `gen_p3_graphs.py`) are the layered roots of the v set of the same seed
#    with random crossing minimisation / layering options. Default `s,v` (fast); the full tracked
#    run is `--sets s,v,d,o,p` (TESTING.md 2B);
# 2. ELK Java (`ElkJavaBaseline`, unmodified Maven Central 0.12.0) one JVM per set with a watchdog;
# 3. elk-lean `elk layout` one process per input with a time limit; optionally elk-rs (`--with-oracle`);
# 4. compare (tol 0 and 1e-6, error class and text) -> <out_dir>/report.md, <out_dir>/details.tsv,
#    and classify the mismatches (`classify_random_parity.py`) -> <out_dir>/classification.md.
# Unless --no-publish, report + classification are written to tests/random_parity/report.md (tracked).
# Stages whose results exist in <out_dir> are reused (--force reruns them); with a new elk binary,
# rerun Lean only with `--stages lean,report` after deleting <out_dir>/lean.
# Environment: ELK_LEAN_BIN (default .lake/build/bin/elk), ELK_JAVA_TOOL (mise spec of the JDK),
# ORACLE_RUNNER, RANDOM_PARITY_JAVA_REBUILD=1 (recompile ElkJavaBaseline via run_java_baseline.sh).
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
REF="$HERE/.reference"
if [ ! -d "$REF" ]; then
  COMMON=$(git -C "$HERE" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)
  if [ -n "$COMMON" ]; then REF="$(dirname "$COMMON")/.reference"; fi
fi
[ $# -ge 1 ] || { sed -n '2,23p' "$0"; exit 2; }
OUT=$1
shift
PUBLISH=1
WITH_ORACLE=0
ARGS=""
for a in "$@"; do
  case "$a" in
    --no-publish) PUBLISH=0 ;;
    --with-oracle) WITH_ORACLE=1; ARGS="$ARGS $a" ;;
    *) ARGS="$ARGS $a" ;;
  esac
done
LEAN=${ELK_LEAN_BIN:-"$HERE/.lake/build/bin/elk"}
[ -x "$LEAN" ] || { echo "elk-lean binary not found: $LEAN (lake build)" >&2; exit 1; }
JAVA_TOOL=${ELK_JAVA_TOOL:-java@temurin-21.0.13+9.0.LTS}
BUILD="$REF/java-baseline"
if [ ! -f "$BUILD/classes/org/eclipse/elk/lean/baseline/ElkJavaBaseline.class" ] || [ ! -f "$BUILD/classpath.txt" ] \
   || [ "${RANDOM_PARITY_JAVA_REBUILD:-0}" = "1" ]; then
  # compiles the harness (and resolves the Maven classpath) through the regular baseline script
  EMPTY=$(mktemp -d "${TMPDIR:-/tmp}/elk-random-empty.XXXXXX")
  sh "$HERE/scripts/run_java_baseline.sh" "$EMPTY" "$EMPTY/out" >/dev/null
  rm -rf "$EMPTY"
fi
JAVA=$(mise exec "$JAVA_TOOL" -- sh -c 'command -v java')
CP="$BUILD/classes:$(cat "$BUILD/classpath.txt")"
RS=${ORACLE_RUNNER:-"$REF/elk-rs-target/release/model_parity_layout_runner"}
if [ "$WITH_ORACLE" = "1" ] && [ ! -x "$RS" ]; then
  echo "oracle runner not found: $RS (run scripts/build_oracle.sh)" >&2; exit 1
fi
# shellcheck disable=SC2086
python3 -I "$HERE/scripts/random_java_parity.py" "$OUT" --lean "$LEAN" --java "$JAVA" --java-cp "$CP" --rs "$RS" $ARGS
python3 -I "$HERE/scripts/classify_random_parity.py" "$OUT"
if [ "$PUBLISH" = "1" ]; then
  mkdir -p "$HERE/tests/random_parity"
  { cat "$OUT/report.md"; echo; sed 's/^#/##/' "$OUT/classification.md"; } \
    > "$HERE/tests/random_parity/report.md"
  echo "published tests/random_parity/report.md"
fi
sed -n '/^## Per set/,/^## Outcome/p' "$OUT/report.md" | sed '$d'
