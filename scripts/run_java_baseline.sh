#!/bin/sh
# ELK Java 0.12.0 reference layouts — the result baseline of elk-lean (performance is compared with
# elk-rs). Unmodified Maven Central artifacts; JDK and Maven from mise.
#   sh scripts/run_java_baseline.sh <models_dir> <out_dir> [--include a,b] [--limit N] [--seed 1]
# Writes <out_dir>/java_manifest.tsv (model_rel_path, input_json, java_layout_json, java_status,
# java_error), <out_dir>/inputs/** (for .elkt/.elkg: ELK's own JSON export of the loaded graph,
# RANDOM_SEED set) and <out_dir>/layouts/** (Gson output of the laid-out graph).
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
REF="$HERE/.reference"
if [ ! -d "$REF" ]; then
  COMMON=$(git -C "$HERE" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)
  if [ -n "$COMMON" ]; then REF="$(dirname "$COMMON")/.reference"; fi
fi
JAVA_TOOL=${ELK_JAVA_TOOL:-java@temurin-21.0.13+9.0.LTS}
MAVEN_TOOL=${ELK_MAVEN_TOOL:-maven@3.9.16}
M2="$REF/m2"
BUILD="$REF/java-baseline"
mkdir -p "$BUILD"
run() { mise exec "$JAVA_TOOL" "$MAVEN_TOOL" -- "$@"; }
# compile against the resolved classpath (cached in $BUILD/classpath.txt)
if [ ! -f "$BUILD/classpath.txt" ] || [ "$HERE/scripts/java/pom.xml" -nt "$BUILD/classpath.txt" ]; then
  run mvn -q -f "$HERE/scripts/java/pom.xml" -Dmaven.repo.local="$M2" dependency:build-classpath \
    -Dmdep.outputFile="$BUILD/classpath.txt" >/dev/null
fi
CP=$(cat "$BUILD/classpath.txt")
mkdir -p "$BUILD/classes"
run javac -nowarn -d "$BUILD/classes" -cp "$CP" $(find "$HERE/scripts/java/src/main/java" -name '*.java')
# ELK_JAVA_PATCHES=<dir of *.patch>: compiles the patched ELK sources (copied from external/elk, never
# modified in place) into an overlay that precedes the Maven jars — e.g. the three elk-rs reference
# patches, to tell their effect apart from other differences. Default: unmodified ELK.
OVERLAY=""
if [ -n "${ELK_JAVA_PATCHES:-}" ]; then
  ELK_SRC=${ELK_JAVA_SOURCE:-"$(dirname "$REF")/external/elk"}
  WORK="$BUILD/patched"
  rm -rf "$WORK" && mkdir -p "$WORK/src" "$WORK/classes"
  FILES=$(grep -h '^+++ b/' "$ELK_JAVA_PATCHES"/*.patch | sed 's|^+++ b/||' | sort -u)
  for f in $FILES; do mkdir -p "$WORK/src/$(dirname "$f")"; cp "$ELK_SRC/$f" "$WORK/src/$f"; done
  for p in "$ELK_JAVA_PATCHES"/*.patch; do (cd "$WORK/src" && patch -s -p1 < "$p"); done
  run javac -nowarn -d "$WORK/classes" -cp "$CP" $(cd "$WORK/src" && for f in $FILES; do printf '%s ' "$WORK/src/$f"; done)
  OVERLAY="$WORK/classes:"
  # the Maven Central ELK jars are signed; a class of a signed package cannot be overridden, so the
  # patched run uses copies of the ELK jars without signature files
  mkdir -p "$WORK/jars"
  NEWCP=""
  for j in $(echo "$CP" | tr ':' ' '); do
    case "$(basename "$j")" in
      org.eclipse.elk.*)
        cp "$j" "$WORK/jars/"
        zip -q -d "$WORK/jars/$(basename "$j")" 'META-INF/*.SF' 'META-INF/*.RSA' 'META-INF/*.DSA' 'META-INF/*.EC' >/dev/null 2>&1 || true
        NEWCP="$NEWCP${NEWCP:+:}$WORK/jars/$(basename "$j")" ;;
      *) NEWCP="$NEWCP${NEWCP:+:}$j" ;;
    esac
  done
  CP=$NEWCP
  echo "patched overlay: $(echo $FILES | wc -w | tr -d ' ') ELK source files from $ELK_JAVA_PATCHES" >&2
fi
run java -cp "$OVERLAY$BUILD/classes:$CP" org.eclipse.elk.lean.baseline.ElkJavaBaseline "$@"
