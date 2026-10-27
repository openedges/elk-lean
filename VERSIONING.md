# elk-lean Versioning and Reference Policy

## Version alignment

elk-lean `MAJOR.MINOR` always matches the ELK release it ports; `PATCH` counts
elk-lean's own published fixes on top of that release (the same scheme elkjs
and elk-rs use):

```
elk-lean 0.12.0 = ELK 0.12.0 port
elk-lean 0.12.1 = ELK 0.12.0 + elk-lean fixes
```

The package version lives in `lakefile.lean` (`version := v!"0.12.0"`),
`plugins/org.eclipse.elk.api/Elk/Api.lean` (`Elk.Api.version`) and, from
Phase 8, in the npm manifests. They must always agree.

Git tags: the first release of a base version is `vX.Y.Z`; later build-only
revisions of the same version use `vX.Y.Z+lean.N`.

## Pinned references

| Reference | Path | Commit |
|-----------|------|--------|
| ELK Java 0.12.0 | `external/elk` | `323312916048544e4e594eab3303cdb0d01e2929` |
| elkjs 0.12.0 | `external/elkjs` | `ff5771d7165445c42c408bb8a090c8035272218c` |
| elk-models | `external/elk-models` | `ac5af2ba511c0037e4f347e8bd91f013950951c7` |
| elk-live | `external/elk-live` | `cbf63a2437ff4b82bebbe548881ca6bc11417e8e` |
| elk-rs 0.12.1 (performance reference, secondary trace oracle) | `../elk-rs` | `eb586b6d91ee0b55cda591546cec8f04cc7f2422` |
| Lean | `lean-toolchain` | `leanprover/lean4:v4.35.0` |
| **ELK Java 0.12.0 (result reference)** | Maven Central `org.eclipse.elk:*:0.12.0`, cached in `.reference/m2` | release artifacts, unmodified (`scripts/java/pom.xml`) |
| JDK / Maven for the Java baseline | `mise` (`java@temurin-21.0.13+9.0.LTS`, `maven@3.9.16`) | `scripts/run_java_baseline.sh` (`ELK_JAVA_TOOL`, `ELK_MAVEN_TOOL`) |
| emscripten (WASM build) | `.reference/emsdk` | emsdk `6.0.13` (emsdk repo `d7b41306`), `scripts/build_wasm.sh` |
| Lean 4 source for the WASM runtime | `.reference/lean4-v4.35.0` | tag `v4.35.0` (`eb6cafb7`) |

The submodules were created as shallow clones of exactly these commits
(`git fetch --depth 1 origin <sha>`); `git submodule update --init` reproduces
them. Never edit files under `external/`.

The elk-rs oracle is built out of tree (`CARGO_TARGET_DIR=.reference/elk-rs-target`)
so the sibling `../elk-rs` checkout stays untouched. If `../elk-rs` moves to a
different commit, rebuild the oracle and record the new commit here and in
`HISTORY.md`; performance and elk-rs trace numbers are only comparable against the same oracle.

`.reference/` (gitignored, shared by all git worktrees of this repository) holds every
generated reference: the elk-rs build, the Maven cache and compiled Java driver, the ELK Java
baseline outputs (`.reference/java-baseline/corpus`, `corpus_reverse`), emsdk and the Lean source.

## Upgrading to a new ELK release
1. Update the four submodule pins and the oracle commit.
2. Diff `external/elk` between the releases; port the changes plugin by plugin.
3. Rerun the full parity gates (`TESTING.md` § 2) and record the numbers.
4. Bump the version, update `CHANGELOG.md`, tag.
