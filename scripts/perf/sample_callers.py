#!/usr/bin/env python3
"""Attributes the samples of frames matching REGEX (e.g. allocation, array copies) to the nearest
elk-lean frame above them in a macOS `sample` call graph.

    python3 scripts/perf/sample_callers.py PROFILE.txt '^(mi_free|lean_dec_ref_cold|lean_alloc_small_object_core)' [N]
    python3 scripts/perf/sample_callers.py PROFILE.txt 'lean_copy_expand_array|lean_copy_array'
"""
import collections
import re
import sys

from sample_inclusive import short


def main():
    lines = open(sys.argv[1]).read().split('\n')
    target = re.compile(sys.argv[2])
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    start = next(i for i, l in enumerate(lines) if l.startswith('Call graph:'))
    end = next(i for i, l in enumerate(lines) if l.startswith('Total number in stack') or l.startswith('Sort by top of stack'))
    stack, callers, total = [], collections.Counter(), 0
    for l in lines[start + 1:end]:
        m = re.match(r'^([\s+!:|]*)(\d+)\s+(\S+)', l)
        if not m:
            continue
        depth, cnt, sym = m.start(2), int(m.group(2)), m.group(3)
        while stack and stack[-1][0] >= depth:
            stack.pop()
        if target.search(sym) and not any(target.search(s) for _, s in stack):
            total += cnt
            for _, s in reversed(stack):
                if s.startswith('lp_elk_x2dlean_'):
                    callers[s] += cnt
                    break
            else:
                callers['<none>'] += cnt
        stack.append((depth, sym))
    print('total', total)
    for s, c in callers.most_common(n):
        print(c, short(s)[:160])


if __name__ == '__main__':
    main()
