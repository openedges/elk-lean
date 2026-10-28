#!/usr/bin/env python3
"""Layered crossing minimisation / layering option variants of random graphs ("p" sets of
`scripts/run_random_java_parity.sh`, agent P3J).

    python3 -I scripts/gen_p3_graphs.py OUT_DIR SEED INPUT_DIR...

Every graph of the input directories (the "v" sets: `gen_nodesize_graphs.py` + `sanitize_for_java.py`)
whose root algorithm is layered is copied to OUT_DIR as `<input dir name>_<file>` with random crossing
minimisation options on the root and on every layered compound child: strategy (LAYER_SWEEP /
MEDIAN_LAYER_SWEEP / INTERACTIVE / NONE), greedy switch types and threshold, model order
strategy/influences, forceNodeModelOrder, thoroughness, random seed, semi-interactive, port sorting,
node promotion, interactive reference point; for INTERACTIVE (and semi-interactive) the nodes get
positions and some edges sections with bend points. Non-layered roots are skipped, so the number of
outputs depends on the inputs. The output is a function of SEED and the input files (`random.Random`).
"""
import json, os, random, sys

out, seed, inputs = sys.argv[1], int(sys.argv[2]), sys.argv[3:]
rng = random.Random(seed)
os.makedirs(out, exist_ok=True)
P = 'elk.layered.'


def p3_options(lo):
    strat = rng.choices(['LAYER_SWEEP', 'MEDIAN_LAYER_SWEEP', 'INTERACTIVE', 'NONE'], [35, 30, 25, 10])[0]
    lo[P + 'crossingMinimization.strategy'] = strat
    if rng.random() < 0.7:
        lo[P + 'crossingMinimization.greedySwitch.type'] = rng.choice(['OFF', 'ONE_SIDED', 'TWO_SIDED'])
    if rng.random() < 0.5:
        lo[P + 'crossingMinimization.greedySwitch.activationThreshold'] = rng.choice([0, 5, 40, 1000])
    if rng.random() < 0.4:
        lo[P + 'crossingMinimization.greedySwitchHierarchical.type'] = rng.choice(['OFF', 'ONE_SIDED', 'TWO_SIDED'])
    if rng.random() < 0.5:
        lo[P + 'considerModelOrder.strategy'] = rng.choice(['NONE', 'NODES_AND_EDGES', 'PREFER_EDGES', 'PREFER_NODES'])
    if rng.random() < 0.25:
        lo[P + 'crossingMinimization.forceNodeModelOrder'] = True
    if rng.random() < 0.3:
        lo[P + 'considerModelOrder.crossingCounterNodeInfluence'] = rng.choice([0, 0.001, 0.5, 2])
    if rng.random() < 0.3:
        lo[P + 'considerModelOrder.crossingCounterPortInfluence'] = rng.choice([0, 0.001, 0.5])
    if rng.random() < 0.25:
        lo[P + 'considerModelOrder.portModelOrder'] = True
    if rng.random() < 0.5:
        lo[P + 'thoroughness'] = rng.randint(1, 12)
    if rng.random() < 0.6:
        lo['elk.randomSeed'] = rng.randint(1, 100000)
    if rng.random() < 0.2:
        lo[P + 'crossingMinimization.semiInteractive'] = True
    if rng.random() < 0.3:
        lo[P + 'portSortingStrategy'] = rng.choice(['INPUT_ORDER', 'PORT_DEGREE'])
    if rng.random() < 0.15:
        lo[P + 'layering.nodePromotion.strategy'] = rng.choice(
            ['MODEL_ORDER_LEFT_TO_RIGHT', 'MODEL_ORDER_RIGHT_TO_LEFT'])
    if rng.random() < 0.3:
        lo[P + 'interactiveReferencePoint'] = rng.choice(['CENTER', 'TOP_LEFT'])
    return strat


def place(node):
    """Random positions for the children (interactive input) and bend points for some edges."""
    for ch in node.get('children', []):
        ch['x'] = round(rng.uniform(-50, 600), 1)
        ch['y'] = round(rng.uniform(-50, 600), 1)
        if rng.random() < 0.15:
            ch['x'] = 0.0
    ids = {}

    def collect(n, ox, oy):
        for ch in n.get('children', []):
            ids[ch['id']] = (ch, ox + ch.get('x', 0), oy + ch.get('y', 0))
            for p in ch.get('ports', []):
                ids[p['id']] = (p, ox + ch.get('x', 0) + p.get('x', 0), oy + ch.get('y', 0) + p.get('y', 0))
    collect(node, 0, 0)
    for e in node.get('edges', []):
        if rng.random() < 0.5 and e.get('sources') and e.get('targets'):
            s = ids.get(e['sources'][0])
            t = ids.get(e['targets'][0])
            if not s or not t:
                continue
            sx, sy = s[1], s[2]
            tx, ty = t[1], t[2]
            k = rng.randint(1, 3)
            bends = []
            for i in range(k):
                f = (i + 1) / (k + 1)
                bends.append({'x': round(sx + (tx - sx) * f + rng.uniform(-30, 30), 1),
                              'y': round(sy + (ty - sy) * f + rng.uniform(-60, 60), 1)})
            if rng.random() < 0.2 and bends:
                bends[0]['x'] = bends[-1]['x']  # equal x of two points
            e['sections'] = [{'id': e['id'] + '_s0', 'startPoint': {'x': sx, 'y': sy}, 'endPoint': {'x': tx, 'y': ty},
                              'bendPoints': bends}]


def visit(node, is_root):
    lo = node.setdefault('layoutOptions', {})
    alg = lo.get('elk.algorithm', 'layered' if is_root else None)
    if alg == 'layered' and (is_root or node.get('children')):
        strat = p3_options(lo)
        if strat == 'INTERACTIVE' or lo.get(P + 'crossingMinimization.semiInteractive'):
            place(node)
    for ch in node.get('children', []):
        visit(ch, False)
    if not node['layoutOptions']:
        del node['layoutOptions']


n = 0
for d in inputs:
    tag = os.path.basename(os.path.normpath(d))
    for f in sorted(os.listdir(d)):
        if not f.endswith('.json'):
            continue
        g = json.load(open(os.path.join(d, f)))
        if g.get('layoutOptions', {}).get('elk.algorithm', 'layered') != 'layered':
            continue
        visit(g, True)
        json.dump(g, open(os.path.join(out, f'{tag}_{f}'), 'w'))
        n += 1
print(f'{n} graphs -> {out}')
