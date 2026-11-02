#!/bin/sh
# Explicit, idempotent bootstrap of the elk-lean development environment (README "Setup",
# TESTING.md § 1, pins in VERSIONING.md). Every step checks before it acts and prints what it did,
# so the script can be rerun at any time; `--check` only reports.
#
#   sh scripts/setup_dev.sh [options]          (or: mise run setup / mise run check)
#
# Default steps, in order:
#   tools           mise trust + mise install (mise.toml: java, maven, node, rust, python). Without
#                   mise (--no-mise, or mise not installed) the tools are looked up on PATH instead.
#   elan            elan (installed when missing, --no-modify-path) and the Lean toolchain named in
#                   lean-toolchain; verifies `lean --version` and `cc`.
#   submodules      git submodule update --init --recursive --depth 1 (external/*, pinned commits).
#   build           lake build; gate: no "warning:" / "error:" line (AGENTS.md), elk --version runs.
#   test            lake test; gate: "0 failed".
# Optional steps (--with-<step>, or --all):
#   oracle          clone https://github.com/openedges/elk-rs.git into $ELK_RS_DIR (../elk-rs) at the
#                   pinned commit and build the oracle (scripts/build_oracle.sh) into
#                   .reference/elk-rs-target (performance reference, secondary parity).
#   java-baseline   ELK Java 0.12.0 layouts of external/elk-models into .reference/java-baseline/corpus
#                   (scripts/run_java_baseline.sh, JDK + Maven from mise). Whole corpus: long.
#   wasm-toolchain  emsdk 6.0.13 into .reference/emsdk and the Lean sources of the toolchain into
#                   .reference/lean4-v<version> (scripts/build_wasm.sh, scripts/build_runtime_nogmp.sh).
# Options:
#   --check          report the state of every requirement, change nothing; exit 1 when a default
#                    requirement is missing
#   --only a,b       run only the listed steps (any of the names above)
#   --skip-STEP      skip a default step (--skip-build, --skip-test, ...)
#   --with-STEP      add an optional step; --all adds all three
#   --no-mise        do not use mise even when it is installed
# Environment: ELK_RS_DIR (default ../elk-rs), ELK_JAVA_TOOL / ELK_MAVEN_TOOL (run_java_baseline.sh),
#   JOBS (parallel jobs of the WASM/no-GMP builds, passed through).
set -eu
HERE=$(cd "$(dirname "$0")/.." && pwd)
cd "$HERE"
export PATH="$HOME/.elan/bin:$PATH"

# ---- pins (VERSIONING.md) ---------------------------------------------------------------------
LEAN_TOOLCHAIN=$(cat lean-toolchain)                       # leanprover/lean4:v4.35.0
LEAN_VERSION=${LEAN_TOOLCHAIN#*:v}                         # 4.35.0
ELK_RS_URL=https://github.com/openedges/elk-rs.git
ELK_RS_COMMIT=eb586b6d91ee0b55cda591546cec8f04cc7f2422     # also in scripts/build_oracle.sh (EXPECTED)
EMSDK_VERSION=6.0.13                                       # also in scripts/build_wasm.sh
EMSDK_URL=https://github.com/emscripten-core/emsdk.git
LEAN4_URL=https://github.com/leanprover/lean4
ELAN_INIT_URL=https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh

# `.reference/` lives in the main checkout; git worktrees find it through the common git dir
REF="$HERE/.reference"
COMMON=$(git -C "$HERE" rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)
if [ -n "$COMMON" ] && [ "$(dirname "$COMMON")" != "$HERE" ]; then REF="$(dirname "$COMMON")/.reference"; fi
ELK_RS=${ELK_RS_DIR:-"$HERE/../elk-rs"}
LEAN_SRC="$REF/lean4-v$LEAN_VERSION"
EMSDK="$REF/emsdk"
JAVA_BASELINE="$REF/java-baseline/corpus"
ORACLE_RUNNER="$REF/elk-rs-target/release/model_parity_layout_runner"

# ---- arguments -----------------------------------------------------------------------------------
DEFAULT_STEPS="tools elan submodules build test"
OPTIONAL_STEPS="oracle java-baseline wasm-toolchain"
STEPS="$DEFAULT_STEPS"
CHECK=0
USE_MISE=1
has_step() { case " $STEPS " in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
known_step() { case " $DEFAULT_STEPS $OPTIONAL_STEPS " in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
add_step() { known_step "$1" || { echo "unknown step: $1" >&2; exit 2; }; has_step "$1" || STEPS="${STEPS:+$STEPS }$1"; }
drop_step() { known_step "$1" || { echo "unknown step: $1" >&2; exit 2; }; STEPS=$(echo " $STEPS " | sed "s/ $1 / /" | sed 's/^ *//; s/ *$//'); }
while [ $# -gt 0 ]; do
  case "$1" in
    --check) CHECK=1 ;;
    --no-mise) USE_MISE=0 ;;
    --all) for s in $OPTIONAL_STEPS; do add_step "$s"; done ;;
    --only) [ $# -ge 2 ] || { echo "--only needs a step list" >&2; exit 2; }
            STEPS=""; for s in $(echo "$2" | tr ',' ' '); do add_step "$s"; done; shift ;;
    --only=*) STEPS=""; for s in $(echo "${1#--only=}" | tr ',' ' '); do add_step "$s"; done ;;
    --with-*) add_step "${1#--with-}" ;;
    --skip-*) drop_step "${1#--skip-}" ;;
    -h|--help) sed -n '2,/^set -eu/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown argument: $1 (see --help)" >&2; exit 2 ;;
  esac
  shift
done
if [ "$USE_MISE" = 1 ] && ! command -v mise >/dev/null 2>&1; then USE_MISE=0; fi

# ---- output helpers ------------------------------------------------------------------------------
FAIL=0
say()  { printf '\n==> %s\n' "$*"; }
ok()   { printf '  [ok]       %s\n' "$*"; }
info() { printf '  [..]       %s\n' "$*"; }
warn() { printf '  [warn]     %s\n' "$*"; }
miss() { printf '  [MISSING]  %s\n' "$*"; FAIL=1; }
opt()  { printf '  [optional] %s\n' "$*"; }
# the pinned tools and the binary that proves each of them
TOOL_BINS="java:java maven:mvn node:node rust:cargo python:python3"
with_tools() {    # with_tools <cmd...>: run through mise when it is used, else directly
  if [ "$USE_MISE" = 1 ]; then mise exec -- "$@"; else "$@"; fi
}
submodule_state() {  # prints: ok | uninitialised | moved | missing
  if ! git submodule status >/dev/null 2>&1; then echo missing; return; fi
  if git submodule status | grep -q '^-'; then echo uninitialised
  elif git submodule status | grep -q '^+'; then echo moved
  else echo ok; fi
}

# ---- --check ------------------------------------------------------------------------------------
if [ "$CHECK" = 1 ]; then
  say "elk-lean development requirements ($HERE)"
  if [ "$USE_MISE" = 1 ]; then
    ok "mise $(mise --version 2>/dev/null | head -1) (mise.toml: $(mise ls --current 2>/dev/null | awk '{print $1"@"$2}' | tr '\n' ' '))"
    if mise ls --current 2>/dev/null | grep -q 'missing'; then
      miss "mise tools not installed: $(mise ls --current 2>/dev/null | grep missing | awk '{print $1"@"$2}' | tr '\n' ' ')-> mise install"
    fi
  else
    info "mise not used; tools looked up on PATH"
  fi
  for pair in $TOOL_BINS; do
    tool=${pair%%:*}; bin=${pair##*:}
    if [ "$USE_MISE" = 1 ]; then path=$(mise which "$bin" 2>/dev/null || true); else path=$(command -v "$bin" 2>/dev/null || true); fi
    if [ -n "$path" ]; then ok "$tool: $(with_tools "$bin" --version 2>&1 | head -1 | cut -c1-70) ($path)"
    else
      case "$tool" in
        java|maven) opt "$tool: not found (needed by the java-baseline step and the Java parity gates)" ;;
        rust)       opt "$tool: not found (needed by the oracle step)" ;;
        *)          miss "$tool: not found" ;;
      esac
    fi
  done
  if command -v elan >/dev/null 2>&1; then ok "$(elan --version 2>/dev/null | head -1) ($(command -v elan))"; else miss "elan: not found (~/.elan/bin) -> $0 --only elan"; fi
  if command -v lean >/dev/null 2>&1 && lean --version 2>/dev/null | grep -q "version $LEAN_VERSION"; then
    ok "$(lean --version | head -1 | cut -c1-80)"; ok "$(lake --version 2>/dev/null | head -1)"
  else miss "Lean $LEAN_VERSION not active ($(lean --version 2>&1 | head -1)) -> elan toolchain install $LEAN_TOOLCHAIN"; fi
  if command -v cc >/dev/null 2>&1; then ok "cc: $(cc --version | head -1)"; else miss "cc (C11 compiler) not found"; fi
  case "$(submodule_state)" in
    ok) ok "submodules at the pinned commits: $(git submodule status | awk '{print $2}' | tr '\n' ' ')" ;;
    uninitialised) miss "submodules not initialised -> git submodule update --init --recursive --depth 1" ;;
    moved) miss "submodules not at the pinned commits: $(git submodule status | grep '^+' | awk '{print $2}' | tr '\n' ' ')" ;;
    *) miss "not a git checkout with submodules" ;;
  esac
  if [ -x .lake/build/bin/elk ]; then ok "lake build: .lake/build/bin/elk $(.lake/build/bin/elk --version 2>/dev/null | head -1)"; else miss "lake build not done (.lake/build/bin/elk) -> lake build"; fi
  if [ -x .lake/build/bin/elktest ]; then ok "lake test driver built (.lake/build/bin/elktest)"; else info "lake test not run yet (.lake/build/bin/elktest)"; fi
  if [ -x "$ORACLE_RUNNER" ]; then
    ok "elk-rs oracle: $ORACLE_RUNNER"
    if [ -d "$ELK_RS/.git" ]; then
      actual=$(git -C "$ELK_RS" rev-parse HEAD 2>/dev/null || true)
      if [ "$actual" = "$ELK_RS_COMMIT" ]; then ok "../elk-rs at $ELK_RS_COMMIT ($ELK_RS)"; else warn "../elk-rs at $actual, expected $ELK_RS_COMMIT (VERSIONING.md)"; fi
    fi
  else opt "elk-rs oracle not built ($ORACLE_RUNNER) -> $0 --only oracle"; fi
  if [ -f "$JAVA_BASELINE/java_manifest.tsv" ]; then
    ok "ELK Java baseline: $(($(wc -l < "$JAVA_BASELINE/java_manifest.tsv") - 1)) models in $JAVA_BASELINE"
  else opt "ELK Java baseline not generated ($JAVA_BASELINE) -> $0 --only java-baseline"; fi
  if [ -x "$EMSDK/upstream/emscripten/emcc" ]; then
    ok "emsdk $(cat "$EMSDK/upstream/emscripten/emscripten-version.txt" 2>/dev/null | tr -d '"') at $EMSDK"
  else opt "emsdk $EMSDK_VERSION not installed ($EMSDK) -> $0 --only wasm-toolchain"; fi
  if [ -d "$LEAN_SRC/.git" ]; then
    if command -v lean >/dev/null 2>&1 && [ "$(git -C "$LEAN_SRC" rev-parse HEAD)" = "$(lean --githash 2>/dev/null)" ]; then ok "Lean sources at the toolchain commit: $LEAN_SRC"
    else warn "Lean sources at $LEAN_SRC are not at the toolchain commit $(lean --githash 2>/dev/null)"; fi
  else opt "Lean sources v$LEAN_VERSION not cloned ($LEAN_SRC) -> $0 --only wasm-toolchain"; fi
  expected_in_oracle=$(sed -n 's/^EXPECTED=//p' scripts/build_oracle.sh)
  [ "$expected_in_oracle" = "$ELK_RS_COMMIT" ] || warn "ELK_RS_COMMIT differs from scripts/build_oracle.sh EXPECTED=$expected_in_oracle"
  printf '\n'
  if [ "$FAIL" = 0 ]; then echo "all default requirements satisfied"; else echo "default requirements missing (see [MISSING]); run: sh scripts/setup_dev.sh"; fi
  exit "$FAIL"
fi

# ---- steps ----------------------------------------------------------------------------------------
echo "elk-lean setup: steps = $STEPS$([ "$USE_MISE" = 1 ] && echo " (tools via mise)" || echo " (without mise)")"

if has_step tools; then
  say "tools"
  if [ "$USE_MISE" = 1 ]; then
    mise trust mise.toml >/dev/null 2>&1 || true
    mise install
    for pair in $TOOL_BINS; do
      tool=${pair%%:*}; bin=${pair##*:}
      if path=$(mise which "$bin" 2>/dev/null); then ok "$tool: $(mise exec -- "$bin" --version 2>&1 | head -1 | cut -c1-70)"; else miss "$tool ($bin) not provided by mise"; fi
    done
  else
    for bin in node python3; do
      if command -v "$bin" >/dev/null 2>&1; then ok "$bin: $("$bin" --version 2>&1 | head -1)"; else miss "$bin not on PATH (mise.toml pins the versions)"; fi
    done
    if has_step oracle; then
      if command -v cargo >/dev/null 2>&1; then ok "cargo: $(cargo --version)"; else miss "cargo not on PATH (rust 1.97.1; needed by the oracle step)"; fi
    fi
    if has_step java-baseline; then
      if command -v java >/dev/null 2>&1 && command -v mvn >/dev/null 2>&1; then ok "java/mvn on PATH"; else miss "java and mvn needed by the java-baseline step (temurin 21.0.13, maven 3.9.16)"; fi
    fi
  fi
  [ "$FAIL" = 0 ] || { echo "tools missing; aborting" >&2; exit 1; }
fi

if has_step elan; then
  say "elan and Lean $LEAN_VERSION"
  if ! command -v elan >/dev/null 2>&1; then
    info "installing elan (no toolchain, PATH not modified: $ELAN_INIT_URL)"
    curl -sSf "$ELAN_INIT_URL" | sh -s -- -y --default-toolchain none --no-modify-path
    export PATH="$HOME/.elan/bin:$PATH"
  fi
  ok "$(elan --version | head -1)"
  if ! elan toolchain list 2>/dev/null | grep -q "^$LEAN_TOOLCHAIN"; then
    info "installing toolchain $LEAN_TOOLCHAIN"
    elan toolchain install "$LEAN_TOOLCHAIN"
  fi
  lean --version | grep -q "version $LEAN_VERSION" || { miss "lean --version is '$(lean --version)', expected $LEAN_VERSION (lean-toolchain)"; exit 1; }
  ok "$(lean --version | head -1 | cut -c1-80)"
  ok "$(lake --version | head -1)"
  if command -v cc >/dev/null 2>&1; then ok "cc: $(cc --version | head -1)"; else miss "cc (C11 compiler) not found"; exit 1; fi
fi

if has_step submodules; then
  say "submodules (external/*, shallow, pinned commits)"
  state=$(submodule_state)
  if [ "$state" != ok ]; then
    git submodule update --init --recursive --depth 1
    state=$(submodule_state)
  fi
  case "$state" in
    ok) git submodule status | while read -r line; do ok "$line"; done ;;
    moved) miss "submodule not at the pinned commit: $(git submodule status | grep '^+')"; exit 1 ;;
    *) miss "submodule initialisation failed ($state)"; exit 1 ;;
  esac
fi

if has_step build; then
  say "lake build (log: tests/tmp/setup_build.log)"
  mkdir -p tests/tmp
  lake build 2>&1 | tee tests/tmp/setup_build.log
  n=$(grep -cE '(warning|error):' tests/tmp/setup_build.log || true)
  [ "$n" = 0 ] || { miss "$n warning/error lines in lake build (AGENTS.md gate: 0)"; exit 1; }
  [ -x .lake/build/bin/elk ] || { miss ".lake/build/bin/elk not produced"; exit 1; }
  ok "lake build: 0 warnings, 0 errors; elk $(.lake/build/bin/elk --version | head -1)"
fi

if has_step test; then
  say "lake test (log: tests/tmp/setup_test.log)"
  mkdir -p tests/tmp
  lake test 2>&1 | tee tests/tmp/setup_test.log
  summary=$(grep -E '[0-9]+ passed, [0-9]+ failed' tests/tmp/setup_test.log | tail -1)
  case "$summary" in
    *" 0 failed"*) ok "lake test: $summary" ;;
    *) miss "lake test: ${summary:-no summary line}"; exit 1 ;;
  esac
fi

if has_step oracle; then
  say "elk-rs oracle ($ELK_RS -> $REF/elk-rs-target)"
  if [ ! -d "$ELK_RS/.git" ]; then
    info "cloning $ELK_RS_URL"
    git clone "$ELK_RS_URL" "$ELK_RS"
    git -C "$ELK_RS" checkout --detach "$ELK_RS_COMMIT"
  fi
  actual=$(git -C "$ELK_RS" rev-parse HEAD)
  if [ "$actual" = "$ELK_RS_COMMIT" ]; then ok "../elk-rs at $ELK_RS_COMMIT"; else warn "../elk-rs at $actual, expected $ELK_RS_COMMIT (VERSIONING.md); left untouched"; fi
  if [ -x "$ORACLE_RUNNER" ]; then
    ok "oracle already built: $ORACLE_RUNNER (delete $REF/elk-rs-target to rebuild)"
  elif [ "$USE_MISE" = 1 ]; then
    ELK_RS_DIR="$ELK_RS" sh scripts/build_oracle.sh
  else
    info "building with cargo on PATH ($(cargo --version))"
    (cd "$ELK_RS" && CARGO_TARGET_DIR="$REF/elk-rs-target" cargo build --release --workspace --bins)
  fi
  if [ -x "$ORACLE_RUNNER" ]; then ok "oracle: $ORACLE_RUNNER, $(dirname "$ORACLE_RUNNER")/perf_benchmark"; else miss "oracle build did not produce $ORACLE_RUNNER"; exit 1; fi
fi

if has_step java-baseline; then
  say "ELK Java 0.12.0 baseline ($JAVA_BASELINE)"
  if [ -f "$JAVA_BASELINE/java_manifest.tsv" ]; then
    ok "already present: $(($(wc -l < "$JAVA_BASELINE/java_manifest.tsv") - 1)) models (delete the directory to regenerate)"
  else
    [ "$USE_MISE" = 1 ] || { miss "scripts/run_java_baseline.sh needs mise (JDK and Maven via mise exec)"; exit 1; }
    [ -d external/elk-models/examples ] || { miss "external/elk-models missing; run the submodules step first"; exit 1; }
    sh scripts/run_java_baseline.sh external/elk-models "$JAVA_BASELINE"
    if [ -f "$JAVA_BASELINE/java_manifest.tsv" ]; then ok "baseline: $(($(wc -l < "$JAVA_BASELINE/java_manifest.tsv") - 1)) models"; else miss "baseline not produced"; exit 1; fi
  fi
  info "result parity: sh scripts/run_java_parity.sh $JAVA_BASELINE tests/tmp/java_parity"
  info "reverse-order run (tells JVM-context-dependent models apart, TESTING.md § 1): sh scripts/run_java_baseline.sh external/elk-models $REF/java-baseline/corpus_reverse --reverse true"
fi

if has_step wasm-toolchain; then
  say "emsdk $EMSDK_VERSION and Lean sources ($REF)"
  mkdir -p "$REF"
  if [ -x "$EMSDK/upstream/emscripten/emcc" ] && grep -q "$EMSDK_VERSION" "$EMSDK/upstream/emscripten/emscripten-version.txt" 2>/dev/null; then
    ok "emsdk $EMSDK_VERSION at $EMSDK"
  else
    [ -d "$EMSDK/.git" ] || { info "cloning $EMSDK_URL"; git clone "$EMSDK_URL" "$EMSDK"; }
    PY=$(with_tools python3 -c 'import sys; print(sys.executable)' 2>/dev/null || command -v python3)
    info "emsdk install/activate $EMSDK_VERSION (EMSDK_PYTHON=$PY)"
    (cd "$EMSDK" && EMSDK_PYTHON="$PY" ./emsdk install "$EMSDK_VERSION" && EMSDK_PYTHON="$PY" ./emsdk activate "$EMSDK_VERSION")
    if [ -x "$EMSDK/upstream/emscripten/emcc" ]; then ok "emsdk $EMSDK_VERSION at $EMSDK"; else miss "emsdk install failed"; exit 1; fi
  fi
  if [ ! -d "$LEAN_SRC/.git" ]; then
    info "cloning Lean sources v$LEAN_VERSION"
    git clone --depth 1 --branch "v$LEAN_VERSION" "$LEAN4_URL" "$LEAN_SRC"
  fi
  if [ "$(git -C "$LEAN_SRC" rev-parse HEAD)" = "$(lean --githash)" ]; then ok "Lean sources at the toolchain commit: $LEAN_SRC"
  else miss "Lean sources at $LEAN_SRC are not at the toolchain commit $(lean --githash)"; exit 1; fi
  info "WASM: sh scripts/build_wasm.sh; no-GMP runtime: ELK_NO_GMP=1 sh scripts/build_ffi.sh"
fi

printf '\n'
echo "done: $STEPS"
echo "next: sh scripts/setup_dev.sh --check   (or mise run check) shows the state of every requirement"
