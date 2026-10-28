#!/usr/bin/env python3
"""gen_hashset_ops.py <out> <seed> [n]: HashSet op sequence whose bins really treeify: phases of growth with
hashes sharing their low 6..8 bits (one table bin at capacity 64..256), removals, iterator removals,
removeAll and clear; every hash distinct. Input of scripts/java/HashSetOrder.java."""
import random, sys
out, seed = sys.argv[1], int(sys.argv[2])
n = int(sys.argv[3]) if len(sys.argv) > 3 else 1500
rnd = random.Random(seed)
used = set()
def mkhash():
    while True:
        r = rnd.random()
        if r < 0.75:
            low = rnd.choice([0, 64, 128, 192, 7, 71])  # spread low bits: bins 0/7 at 64, splits later
            s = (rnd.getrandbits(16) << 16) | ((rnd.getrandbits(8) << 8) | low) & 0xFFFF
        else:
            s = rnd.getrandbits(32)
        hi = s >> 16
        lo = (s & 0xFFFF) ^ hi
        h = (hi << 16) | lo
        if h not in used:
            used.add(h)
            return h - (1 << 32) if h >= (1 << 31) else h
alive = {}
nid = 0
lines = []
grow = True
for _ in range(n):
    if len(alive) > 120: grow = False
    if len(alive) < 15: grow = True
    x = rnd.random()
    padd = 0.8 if grow else 0.25
    if x < padd or not alive:
        h = mkhash(); alive[nid] = h; lines.append(f"a {nid} {h}"); nid += 1
    else:
        y = rnd.random()
        if y < 0.08:
            k = rnd.choice(list(alive)); lines.append(f"a {k} {alive[k]}")
        elif y < 0.5:
            k = rnd.choice(list(alive)); lines.append(f"r {k} {alive[k]}"); del alive[k]
        elif y < 0.8:
            k = rnd.choice(list(alive)); lines.append(f"i {k} {alive[k]}"); del alive[k]
        elif y < 0.995:
            ks = rnd.sample(list(alive), min(len(alive), rnd.randint(1, 12)))
            lines.append("R " + " ".join(f"{k} {alive[k]}" for k in ks))
            for k in ks: del alive[k]
        else:
            lines.append("c"); alive = {}
    if rnd.random() < 0.3:
        lines.append("p")
lines.append("p")
open(out, "w").write("\n".join(lines) + "\n")
