#!/usr/bin/env python3
"""Inclusive samples of the outermost frames matching REGEX in a macOS `sample` call graph.

    python3 scripts/perf/sample_inclusive.py PROFILE.txt 'Elk_Alg_Layered_P[1-5].*_process' [N]
"""
import collections
import re
import sys


def short(s):
    for a, b in [('lp_elk_x2dlean_', ''),
                 ('__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00', 'LOOP@'),
                 ('__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00', 'ALOOP@'),
                 ('__private_Init_While_0__repeatM_erased___at___00', 'WHILE@')]:
        s = s.replace(a, b)
    return s


def main():
    lines = open(sys.argv[1]).read().split('\n')
    pat = re.compile(sys.argv[2])
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 30
    start = next(i for i, l in enumerate(lines) if l.startswith('Call graph:'))
    end = next(i for i, l in enumerate(lines) if l.startswith('Total number in stack') or l.startswith('Sort by top of stack'))
    stack, inc = [], collections.Counter()
    for l in lines[start + 1:end]:
        m = re.match(r'^([\s+!:|]*)(\d+)\s+(\S+)', l)
        if not m:
            continue
        depth, cnt, sym = m.start(2), int(m.group(2)), m.group(3)
        while stack and stack[-1][0] >= depth:
            stack.pop()
        if pat.search(sym) and not any(pat.search(s) for _, s in stack):
            inc[sym] += cnt
        stack.append((depth, sym))
    tot = sum(inc.values()) or 1
    print('total', tot)
    for s, c in inc.most_common(n):
        print(f"{c:6d} {100 * c / tot:5.1f}% {short(s)[:150]}")


if __name__ == '__main__':
    main()
