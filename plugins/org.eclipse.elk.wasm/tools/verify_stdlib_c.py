#!/usr/bin/env python3
"""Check that the regenerated toolchain C (stdlib_c.py) is the code of the Lean release.

Each generated `.c` is compiled natively with the toolchain's bundled clang and the flags of the
release build (leanc internal flags + `-O3 -DNDEBUG -DLEAN_EXPORTING`, the `static.export` facet)
and compared with the corresponding member of the shipped `libInit.a` / `libStd.a`. Members are
identified by the module initialiser they define (`meta_initialize_<Module>`). Objects must be
byte-identical except for the Mach-O header region (LC_BUILD_VERSION minimum OS version, which
leanc pins through MACOSX_DEPLOYMENT_TARGET), so this check runs on macOS hosts only.

usage: verify_stdlib_c.py --lean LEAN --stdlib-c DIR --work DIR [--jobs N]
"""
import argparse
import concurrent.futures
import os
import re
import subprocess
import sys

HEADER_REGION = 4096


def ar_members(path):
    """BSD/GNU ar reader: list of (name, bytes)."""
    data = open(path, "rb").read()
    if not data.startswith(b"!<arch>\n"):
        sys.exit("not an ar archive: " + path)
    pos = 8
    out = []
    while pos + 60 <= len(data):
        hdr = data[pos:pos + 60]
        name = hdr[0:16].decode().strip()
        size = int(hdr[48:58].decode().strip())
        body = data[pos + 60:pos + 60 + size]
        if name.startswith("#1/"):
            n = int(name[3:])
            name = body[:n].rstrip(b"\0").decode()
            body = body[n:]
        out.append((name, body))
        pos += 60 + size + (size & 1)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", required=True)
    ap.add_argument("--stdlib-c", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--jobs", type=int, default=4)
    a = ap.parse_args()
    prefix = subprocess.run([a.lean, "--print-prefix"], check=True, capture_output=True, text=True).stdout.strip()
    clang = os.path.join(prefix, "bin", "clang")
    shipped = {}
    for lib in ("libInit.a", "libStd.a"):
        for name, body in ar_members(os.path.join(prefix, "lib", "lean", lib)):
            m = re.search(rb"_meta_initialize_([A-Za-z0-9_]+)\0", body)
            if m:
                shipped[m.group(1).decode()] = body
    mods = [l.strip() for l in open(os.path.join(a.stdlib_c, "modules.txt")) if l.strip()]
    os.makedirs(a.work, exist_ok=True)
    flags = ["-I", os.path.join(prefix, "include"), "-fstack-clash-protection", "-ffp-contract=off",
             "-fdata-sections", "-ffunction-sections", "-fvisibility=hidden",
             "-Wno-unused-command-line-argument", "--sysroot", prefix, "-nostdinc",
             "-isystem", os.path.join(prefix, "include", "clang"), "-O3", "-DNDEBUG", "-DLEAN_EXPORTING"]
    env = dict(os.environ, MACOSX_DEPLOYMENT_TARGET="99.0")

    def check(m):
        key = m.replace(".", "_")
        ref = shipped.get(key)
        if ref is None:
            return (m, "no shipped object")
        c = os.path.join(a.stdlib_c, *m.split(".")) + ".c"
        o = os.path.join(a.work, key + ".o")
        r = subprocess.run([clang, "-c", "-o", o, c] + flags, capture_output=True, text=True, env=env)
        if r.returncode != 0:
            return (m, "compile failed: " + r.stderr[-500:])
        mine = open(o, "rb").read()
        os.remove(o)
        if len(mine) != len(ref):
            return (m, "size %d != shipped %d" % (len(mine), len(ref)))
        diff = [i for i in range(len(mine)) if mine[i] != ref[i]] if mine != ref else []
        if any(i >= HEADER_REGION for i in diff) or len(diff) > 4:
            return (m, "%d bytes differ (first at %d)" % (len(diff), diff[0]))
        return (m, None)

    bad = []
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as ex:
        for i, (m, err) in enumerate(ex.map(check, mods), 1):
            if err:
                bad.append("%s: %s" % (m, err))
            if i % 100 == 0:
                print("  %d/%d" % (i, len(mods)), flush=True)
    print("stdlib C verification: %d modules, %d identical to the release objects, %d different"
          % (len(mods), len(mods) - len(bad), len(bad)))
    for b in bad:
        print("  " + b)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
