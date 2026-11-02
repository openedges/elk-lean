#!/usr/bin/env python3
"""Set or check the elk-lean package version in every file that carries it (VERSIONING.md).
Usage:
    python3 scripts/bump_version.py <version>
    python3 scripts/bump_version.py --check
<version> is the bare package version, for example 0.12.1: no leading `v` and no `+lean.N`
build metadata (git tags are `v<version>` and `v<version>+lean.<N>`; npm strips build metadata,
so the registry only ever sees <version>).
Files (all must agree; `--check` verifies that and prints the version, exit 1 on a mismatch):
  lakefile.lean                                      `version := v!"<version>"`
  plugins/org.eclipse.elk.api/Elk/Api.lean           `def version : String := "<version>"`
  plugins/org.eclipse.elk.js/package.json            version + optionalDependencies (@openedges/elk-lean-*)
  plugins/org.eclipse.elk.js/npm/*/package.json      version
  plugins/org.eclipse.elk.live/package.json          version (private demo)
  plugins/org.eclipse.elk.live/package-lock.json     root package version entries
Run from the repository root.
"""
import glob
import json
import os
import re
import sys

LAKEFILE = "lakefile.lean"
API = "plugins/org.eclipse.elk.api/Elk/Api.lean"
JS = "plugins/org.eclipse.elk.js/package.json"
PLATFORMS = sorted(glob.glob("plugins/org.eclipse.elk.js/npm/*/package.json"))
LIVE = "plugins/org.eclipse.elk.live/package.json"
LIVE_LOCK = "plugins/org.eclipse.elk.live/package-lock.json"
LAKE_RE = re.compile(r'^(\s*version\s*:=\s*v!")([^"]+)(")', re.M)
API_RE = re.compile(r'^(def version : String := ")([^"]+)(")', re.M)
VERSION_RE = re.compile(r"^\d+\.\d+\.\d+(-[0-9A-Za-z.-]+)?$")


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def write(path, text):
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def read_json(path):
    return json.loads(read(path))


def write_json(path, data):
    write(path, json.dumps(data, indent=2, ensure_ascii=False) + "\n")


def collect():
    """Every (file, description, version) the repository carries."""
    found = []
    m = LAKE_RE.search(read(LAKEFILE))
    found.append((LAKEFILE, "version :=", m.group(2) if m else None))
    m = API_RE.search(read(API))
    found.append((API, "Elk.Api.version", m.group(2) if m else None))
    js = read_json(JS)
    found.append((JS, "version", js.get("version")))
    for name, dep in (js.get("optionalDependencies") or {}).items():
        found.append((JS, f"optionalDependencies[{name}]", dep))
    for p in PLATFORMS:
        found.append((p, "version", read_json(p).get("version")))
    found.append((LIVE, "version", read_json(LIVE).get("version")))
    if os.path.exists(LIVE_LOCK):
        lock = read_json(LIVE_LOCK)
        found.append((LIVE_LOCK, "version", lock.get("version")))
        root = (lock.get("packages") or {}).get("")
        if root is not None:
            found.append((LIVE_LOCK, 'packages[""].version', root.get("version")))
    return found


def check():
    found = collect()
    versions = {v for _, _, v in found}
    if len(versions) != 1 or None in versions:
        print("bump_version: the version differs between files:", file=sys.stderr)
        for path, what, v in found:
            print(f"  {path}: {what} = {v}", file=sys.stderr)
        return 1
    print(versions.pop())
    return 0


def set_version(version):
    if not VERSION_RE.match(version):
        print(f"bump_version: not a bare version: {version}", file=sys.stderr)
        return 2
    text, n = LAKE_RE.subn(lambda m: m.group(1) + version + m.group(3), read(LAKEFILE))
    assert n == 1, LAKEFILE
    write(LAKEFILE, text)
    text, n = API_RE.subn(lambda m: m.group(1) + version + m.group(3), read(API))
    assert n == 1, API
    write(API, text)
    js = read_json(JS)
    js["version"] = version
    for name in list((js.get("optionalDependencies") or {}).keys()):
        js["optionalDependencies"][name] = version
    write_json(JS, js)
    for p in PLATFORMS:
        d = read_json(p)
        d["version"] = version
        write_json(p, d)
    d = read_json(LIVE)
    d["version"] = version
    write_json(LIVE, d)
    if os.path.exists(LIVE_LOCK):
        lock = read_json(LIVE_LOCK)
        lock["version"] = version
        root = (lock.get("packages") or {}).get("")
        if root is not None:
            root["version"] = version
        write_json(LIVE_LOCK, lock)
    print(f"bump_version: set {version} in {LAKEFILE}, {API}, {JS}, {len(PLATFORMS)} platform packages, {LIVE}")
    return check()


def main(argv):
    if len(argv) != 2 or argv[1] in ("-h", "--help"):
        print(__doc__.strip())
        return 0 if len(argv) == 2 else 2
    if not os.path.exists(LAKEFILE):
        print("bump_version: run from the repository root", file=sys.stderr)
        return 2
    if argv[1] == "--check":
        return check()
    return set_version(argv[1])


if __name__ == "__main__":
    sys.exit(main(sys.argv))
