#!/bin/sh
# Publish the elk-lean npm packages: the @openedges/elk-lean-<triple> platform packages first, then
# the main `@openedges/elk-lean` package, skipping every package@version that is already on the
# registry (npm never allows republishing a version).
#
# Usage: sh scripts/publish_npm.sh [--dry-run] [--expect-version <version>]
#
#   --dry-run          `npm publish --dry-run`; missing build artefacts only warn
#   --expect-version   fail unless every package.json carries this version
#                      (CI passes the tag's base version, e.g. 0.12.0 for v0.12.0 or v0.12.0+lean.1)
#
# Authentication: in GitHub Actions the `release.yml` publish-npm job runs with `id-token: write`,
# so npm (11.5.1+) publishes through Trusted Publishing (OIDC). Every package must trust that
# workflow (VERSIONING.md "Releases"); CI has no stored-token fallback. A package that does not
# exist on the registry yet cannot be trusted before its first version is there: the maintainer
# publishes that first version locally (`npm login`, then this script). Authentication is not
# needed for --dry-run.
#
# Environment:
#   NPM_DIST_TAG      dist-tag to publish under (default: latest)
#
# Every package is validated (version, build artefact present) before the first publish so a bad
# main package cannot leave the platform packages published alone. Expects the platform `.node`
# addons in plugins/org.eclipse.elk.js/npm/<triple>/ (scripts/build_napi.sh --copy-to-npm) and the
# web/Node WASM builds in plugins/org.eclipse.elk.js/dist/wasm{,-node}/ (scripts/build_wasm.sh).
# Only the platform packages listed in the main package's optionalDependencies are published; the
# other npm/<triple>/ directories are templates for platforms the release does not build yet.
# Run from the repository root.
set -eu

dry_run=false
expect_version=""
while [ $# -gt 0 ]; do
  case "$1" in
    --dry-run) dry_run=true ;;
    --expect-version) shift; expect_version="${1:-}"; [ -n "$expect_version" ] || { echo "publish_npm: --expect-version needs a value" >&2; exit 2; } ;;
    -h|--help) awk 'NR > 1 && !/^#/ { exit } NR > 1 { sub(/^# ?/, ""); print }' "$0"; exit 0 ;;
    *) echo "publish_npm: unknown argument: $1" >&2; exit 2 ;;
  esac
  shift
done

[ -f lakefile.lean ] || { echo "publish_npm: run from the repository root" >&2; exit 1; }
js_dir="plugins/org.eclipse.elk.js"
dist_tag="${NPM_DIST_TAG:-latest}"

pkg_field() { # pkg_field <dir> <field>
  node -p "require('./$1/package.json').$2"
}

artifact_check() { # artifact_check <dir> <description> <glob>
  # shellcheck disable=SC2086  # $3 is a glob
  if ! ls $3 >/dev/null 2>&1; then
    if [ "$dry_run" = true ]; then
      echo "publish_npm: warning: $1 has no $2 (dry run continues)"
    else
      echo "publish_npm: $1 has no $2; refusing to publish an empty package" >&2
      exit 1
    fi
  fi
}

# Publish order: the platform packages the main package depends on, then the main package.
dirs=""
for name in $(node -p "Object.keys(require('./$js_dir/package.json').optionalDependencies || {}).join(' ')"); do
  triple="${name#@openedges/elk-lean-}"
  dir="$js_dir/npm/$triple"
  [ -f "$dir/package.json" ] || { echo "publish_npm: $name has no template directory $dir" >&2; exit 1; }
  [ "$(pkg_field "$dir" name)" = "$name" ] || { echo "publish_npm: $dir/package.json is not $name" >&2; exit 1; }
  dirs="$dirs $dir"
done
dirs="$dirs $js_dir"

# Pass 1: validate every package before touching the registry.
for dir in $dirs; do
  name="$(pkg_field "$dir" name)"
  version="$(pkg_field "$dir" version)"
  if [ -n "$expect_version" ] && [ "$version" != "$expect_version" ]; then
    echo "publish_npm: $name has version $version, expected $expect_version" >&2
    exit 1
  fi
  if [ "$(pkg_field "$dir" private)" = "true" ]; then
    echo "publish_npm: $name is marked private" >&2
    exit 1
  fi
  if [ "$dir" = "$js_dir" ]; then
    artifact_check "$dir" "dist/wasm/*.wasm" "$dir/dist/wasm/*.wasm"
    artifact_check "$dir" "web WASM glue" "$dir/dist/wasm/elk_lean.mjs"
    artifact_check "$dir" "dist/wasm-node/*.wasm" "$dir/dist/wasm-node/*.wasm"
    artifact_check "$dir" "Node WASM glue" "$dir/dist/wasm-node/elk_lean.cjs"
  else
    artifact_check "$dir" "*.node addon" "$dir/*.node"
    artifact_check "$dir" "LICENSE" "$dir/LICENSE"
  fi
done

# Pass 2: publish what is missing.
published=0
skipped=0
for dir in $dirs; do
  name="$(pkg_field "$dir" name)"
  version="$(pkg_field "$dir" version)"
  # `npm view` prints the version when it exists, nothing when the package exists without that
  # version, and fails (E404) when the package does not exist yet.
  if [ -n "$(npm view "$name@$version" version 2>/dev/null || true)" ]; then
    echo "publish_npm: skip $name@$version: already on the registry"
    skipped=$((skipped + 1))
    continue
  fi
  if [ "$dry_run" = true ]; then
    echo "publish_npm: dry run $name@$version (--tag $dist_tag)"
    (cd "$dir" && npm publish --access public --tag "$dist_tag" --dry-run)
  else
    echo "publish_npm: publishing $name@$version (--tag $dist_tag)"
    (cd "$dir" && npm publish --access public --tag "$dist_tag")
  fi
  published=$((published + 1))
done
echo "publish_npm: done (published=$published skipped=$skipped dry_run=$dry_run)"
