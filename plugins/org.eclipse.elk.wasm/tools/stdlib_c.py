#!/usr/bin/env python3
"""Generate the C code of the toolchain modules (Init, Std, ...) that elk-lean imports.

The Lean release ships Init/Std only as native archives (libInit.a, libStd.a), so a wasm32 build
needs their C again. It is regenerated from the toolchain's own sources (`<prefix>/src/lean`) by the
toolchain's own `lean -c`, against the toolchain's shipped .olean files, exactly like the release
build did (`verify_stdlib_c.py` checks that the result compiles to the shipped objects).

Roots are the toolchain modules whose initialisers the elk-lean C references
(`initialize_Init`, `initialize_Std_Data_HashMap`, ...); the closure follows `lean --deps`.

usage: stdlib_c.py --lean LEAN --elk-ir DIR --out DIR [--jobs N]
Writes OUT/<Module/Path>.c, OUT/modules.txt (one module per line) and OUT/toolchain.txt (stamp).
Idempotent: existing C files are kept while the toolchain stamp is unchanged.
"""
import argparse
import concurrent.futures
import os
import re
import subprocess
import sys

INIT_DECL = re.compile(r"^lean_object\* initialize_([A-Za-z0-9_]+)\(uint8_t builtin\);", re.M)


def toolchain_modules(src_root):
    """All toolchain source modules under Init/ and Std/ (name -> path)."""
    mods = {}
    for top in ("Init", "Std"):
        if os.path.exists(os.path.join(src_root, top + ".lean")):
            mods[top] = os.path.join(src_root, top + ".lean")
        for d, _, files in os.walk(os.path.join(src_root, top)):
            for f in files:
                if f.endswith(".lean"):
                    p = os.path.join(d, f)
                    rel = os.path.relpath(p, src_root)[: -len(".lean")]
                    mods[rel.replace(os.sep, ".")] = p
    return mods


def mangle(name):
    # Lean name mangling for module initialisers; toolchain module components are plain
    # alphanumeric identifiers, which is checked below.
    if not all(re.match(r"^[A-Za-z][A-Za-z0-9]*$", c) for c in name.split(".")):
        return None
    return name.replace(".", "_")


def roots_from_elk_c(elk_ir, mods):
    by_mangled = {}
    for m in mods:
        k = mangle(m)
        if k is not None:
            by_mangled[k] = m
    roots = set()
    for d, _, files in os.walk(elk_ir):
        for f in files:
            if not f.endswith(".c"):
                continue
            with open(os.path.join(d, f), encoding="utf-8", errors="replace") as fh:
                text = fh.read()
            for k in INIT_DECL.findall(text):
                if k.startswith("elk_x2dlean_"):
                    continue
                if k not in by_mangled:
                    sys.exit("stdlib_c.py: initialiser initialize_%s (from %s) is not an Init/Std module"
                             % (k, os.path.join(d, f)))
                roots.add(by_mangled[k])
    return sorted(roots)


def deps(lean, path, libdir):
    out = subprocess.run([lean, "--deps", path], check=True, capture_output=True, text=True).stdout
    res = []
    for line in out.split():
        rel = os.path.relpath(line, libdir)
        if rel.startswith("..") or not rel.endswith(".olean"):
            sys.exit("stdlib_c.py: unexpected dependency %s of %s" % (line, path))
        res.append(rel[: -len(".olean")].replace(os.sep, "."))
    return res


def closure(lean, roots, mods, libdir, jobs):
    seen = set(roots)
    frontier = list(roots)
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        while frontier:
            results = list(ex.map(lambda m: deps(lean, mods[m], libdir), frontier))
            frontier = []
            for ds in results:
                for d in ds:
                    if d not in mods:
                        sys.exit("stdlib_c.py: dependency %s is not an Init/Std module" % d)
                    if d not in seen:
                        seen.add(d)
                        frontier.append(d)
    return sorted(seen)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", required=True)
    ap.add_argument("--elk-ir", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--jobs", type=int, default=4)
    a = ap.parse_args()
    prefix = subprocess.run([a.lean, "--print-prefix"], check=True, capture_output=True, text=True).stdout.strip()
    version = subprocess.run([a.lean, "--version"], check=True, capture_output=True, text=True).stdout.strip()
    src_root = os.path.join(prefix, "src", "lean")
    libdir = os.path.join(prefix, "lib", "lean")
    os.makedirs(a.out, exist_ok=True)
    stamp = os.path.join(a.out, "toolchain.txt")
    old = open(stamp).read().strip() if os.path.exists(stamp) else None
    if old != version:
        for d, _, files in os.walk(a.out):
            for f in files:
                if f.endswith(".c"):
                    os.remove(os.path.join(d, f))
    mods = toolchain_modules(src_root)
    roots = roots_from_elk_c(a.elk_ir, mods)
    allmods = closure(a.lean, roots, mods, libdir, a.jobs)
    todo = []
    for m in allmods:
        c = os.path.join(a.out, *m.split(".")) + ".c"
        if not os.path.exists(c):
            todo.append((m, c))
    print("stdlib C: roots %s, %d modules, %d to generate" % (" ".join(roots), len(allmods), len(todo)), flush=True)

    def gen(item):
        m, c = item
        os.makedirs(os.path.dirname(c), exist_ok=True)
        tmp = c + ".tmp"
        # `-R src_root` derives the module name from the path, like the core Lake build
        r = subprocess.run([a.lean, "-R", src_root, mods[m], "-c", tmp], capture_output=True, text=True)
        if r.returncode != 0:
            return "%s: lean exited with %d\n%s%s" % (m, r.returncode, r.stdout[-2000:], r.stderr[-2000:])
        os.replace(tmp, c)
        return None

    done = 0
    errors = []
    with concurrent.futures.ThreadPoolExecutor(a.jobs) as ex:
        for err in ex.map(gen, todo):
            done += 1
            if err:
                errors.append(err)
            if done % 50 == 0:
                print("  %d/%d" % (done, len(todo)), flush=True)
    if errors:
        sys.exit("stdlib_c.py: failed:\n" + "\n".join(errors))
    with open(os.path.join(a.out, "modules.txt"), "w") as fh:
        fh.write("\n".join(allmods) + "\n")
    with open(stamp, "w") as fh:
        fh.write(version + "\n")


if __name__ == "__main__":
    main()
