#!/usr/bin/env python3
"""Finds the PLAN 7.1 item-16 pattern in the generated C (.lake/build/ir): an array element read with
lean_array_fget/uget(A, I) whose exclusivity is tested (lean_is_exclusive(V)) or which is updated by a
C call that tests it (array push/set/fset/uset on V, ...) *before* the slot A[I] is written back
(lean_array_fset/uset(A, I, ...)). Such an `Array.modify`/`Array.map` update always copies the element
(a record update allocates a fresh object, an array element is copied). Fix: `Array.modifyIn`, or an
out-of-line (`@[noinline]`) updater when the element type has no `Inhabited` instance.

    python3 scripts/perf/scan_modify_order.py .lake/build/ir/Elk/Alg/Layered [more dirs]

Prints one line per (file, function, element variable); the count goes to stderr."""
import os, re, sys, collections
fn_re = re.compile(r'^LEAN_EXPORT [^(]*\b(\w+)\(|^static [^(]*\b(\w+)\(.*\)\{$|^[A-Za-z_][^;(]*\b(lp_\w+)\(.*\)\{$')
get_re = re.compile(r'(v_\w+) = lean_array_(?:fget|uget|get_borrowed)\((v_\w+), (v_\w+)\);')
hits = collections.Counter()
for d in sys.argv[1:]:
    for root, _, files in os.walk(d):
        for f in files:
            if not f.endswith('.c'): continue
            p = os.path.join(root, f)
            lines = open(p, errors='replace').read().split('\n')
            fn = '?'
            for i, l in enumerate(lines):
                m = fn_re.match(l)
                if m and l.rstrip().endswith('{'):
                    fn = next(g for g in m.groups() if g)
                    continue
                m = get_re.search(l)
                if not m: continue
                v, a, idx = m.groups()
                # look ahead up to 400 lines, until function end
                tested = False
                for j in range(i + 1, min(i + 600, len(lines))):
                    lj = lines[j]
                    if lj.startswith('LEAN_EXPORT') or lj.startswith('static '): break
                    if re.search(r'lean_array_[fu]set\(%s, %s,' % (re.escape(a), re.escape(idx)), lj):
                        if tested:
                            hits[(os.path.relpath(p, d), fn.replace('lp_elk_x2dlean_', ''), v)] += 1
                        break
                    if re.search(r'lean_is_exclusive\(%s\)' % re.escape(v), lj) or \
                       re.search(r'lean_(?:array_push|array_fset|array_uset|array_set|copy_expand_array|ensure_exclusive_array|float_array_push|float_array_fset|float_array_uset|byte_array_push)\(%s[,)]' % re.escape(v), lj):
                        tested = True
for (p, fn, v), c in sorted(hits.items()):
    print(f"{p}\t{fn}\t{v}")
print(len(hits), 'hits', file=sys.stderr)
