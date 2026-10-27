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
| elk-rs 0.12.1 (oracle) | `../elk-rs` | `eb586b6d91ee0b55cda591546cec8f04cc7f2422` |
| Lean | `lean-toolchain` | `leanprover/lean4:v4.35.0` |

The submodules were created as shallow clones of exactly these commits
(`git fetch --depth 1 origin <sha>`); `git submodule update --init` reproduces
them. Never edit files under `external/`.

The oracle is built out of tree (`CARGO_TARGET_DIR=.reference/elk-rs-target`)
so the sibling `../elk-rs` checkout stays untouched. If `../elk-rs` moves to a
different commit, rebuild the oracle and record the new commit here and in
`HISTORY.md`; parity numbers are only comparable against the same oracle.

## Upgrading to a new ELK release
1. Update the four submodule pins and the oracle commit.
2. Diff `external/elk` between the releases; port the changes plugin by plugin.
3. Rerun the full parity gates (`TESTING.md` § 2) and record the numbers.
4. Bump the version, update `CHANGELOG.md`, tag.
