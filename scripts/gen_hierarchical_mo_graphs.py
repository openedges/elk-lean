#!/usr/bin/env python3
"""Random hierarchical (INCLUDE_CHILDREN) layered graphs with model order options (agent GS).

    python3 -I scripts/gen_hierarchical_mo_graphs.py OUT_DIR COUNT SEED

Two or three levels of compound nodes, model order options (cycle breaking, layering, node promotion,
considerModelOrder.*) on the root and/or compound children, NO_LAYOUT nodes (also compound ones, with and
without ALGORITHM), noModelOrder flags, cycle breaking group ids, layer constraints, self loops and
hierarchy-crossing edges. Written to look for observable effects of Java's hierarchy-wide node model
order numbering (`ElkGraphImporter.importHierarchicalGraph`); lay the set out with
`ElkJavaBaseline OUT_DIR <java_dir>` and compare with elk-lean (docs/robustness-random-graphs.md §19).
The output is a function of COUNT and SEED (`random.Random`).
"""
import json, os, random, sys

out, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
os.makedirs(out, exist_ok=True)
L = 'elk.layered.'


def mo_options(lo, strength):
    if rng.random() < strength:
        lo[L + 'cycleBreaking.strategy'] = rng.choice(
            ['MODEL_ORDER', 'GREEDY_MODEL_ORDER', 'SCC_CONNECTIVITY', 'SCC_NODE_TYPE', 'DFS_NODE_ORDER',
             'BFS_NODE_ORDER', 'GREEDY', 'DEPTH_FIRST'])
    if rng.random() < strength:
        lo[L + 'layering.strategy'] = rng.choice(['BF_MODEL_ORDER', 'DF_MODEL_ORDER', 'NETWORK_SIMPLEX',
                                                  'LONGEST_PATH', 'COFFMAN_GRAHAM'])
    if rng.random() < strength * 0.6:
        lo[L + 'layering.nodePromotion.strategy'] = rng.choice(['MODEL_ORDER_LEFT_TO_RIGHT',
                                                               'MODEL_ORDER_RIGHT_TO_LEFT', 'NONE'])
    if rng.random() < strength:
        lo[L + 'considerModelOrder.strategy'] = rng.choice(['NONE', 'NODES_AND_EDGES', 'PREFER_EDGES',
                                                            'PREFER_NODES'])
    if rng.random() < strength * 0.4:
        lo[L + 'crossingMinimization.forceNodeModelOrder'] = True
    if rng.random() < strength * 0.4:
        lo[L + 'considerModelOrder.components'] = rng.choice(['NONE', 'INSIDE_PORT_SIDE_GROUPS',
                                                              'GROUP_MODEL_ORDER', 'MODEL_ORDER'])
    if rng.random() < strength * 0.3:
        lo[L + 'considerModelOrder.crossingCounterNodeInfluence'] = rng.choice([0.001, 0.5, 2])
    if rng.random() < strength * 0.3:
        lo[L + 'considerModelOrder.crossingCounterPortInfluence'] = rng.choice([0.001, 0.5])
    if rng.random() < strength * 0.3:
        lo[L + 'considerModelOrder.groupModelOrder.cbGroupOrderStrategy'] = rng.choice(
            ['ONLY_WITHIN_GROUP', 'ENFORCED', 'MODEL_ORDER'])
    if rng.random() < 0.3:
        lo[L + 'crossingMinimization.greedySwitch.type'] = rng.choice(['OFF', 'ONE_SIDED', 'TWO_SIDED'])
    if rng.random() < 0.2:
        lo[L + 'mergeEdges'] = True


def make_graph(i):
    ctr = [0]
    edges_all = []

    def node(depth, prefix):
        ctr[0] += 1
        nid = '%sn%d' % (prefix, ctr[0])
        n = {'id': nid, 'width': rng.choice([20, 30, 40, 55]), 'height': rng.choice([20, 30, 40])}
        lo = {}
        if rng.random() < 0.12:
            lo['elk.noLayout'] = True
        if rng.random() < 0.15:
            lo[L + 'considerModelOrder.noModelOrder'] = True
        if rng.random() < 0.25:
            lo[L + 'considerModelOrder.groupModelOrder.cycleBreakingId'] = rng.randint(0, 3)
        if rng.random() < 0.15:
            lo[L + 'layering.layerConstraint'] = rng.choice(['FIRST', 'LAST', 'FIRST_SEPARATE', 'LAST_SEPARATE'])
        if depth < 2 and rng.random() < 0.35:
            k = rng.randint(1, 5)
            n['children'] = [node(depth + 1, nid + '_') for _ in range(k)]
            if rng.random() < 0.8:
                if rng.random() < 0.15:
                    lo['elk.algorithm'] = rng.choice(['layered', 'org.eclipse.elk.layered'])
                mo_options(lo, rng.choice([0.0, 0.3, 0.7]))
            if rng.random() < 0.1:
                lo['elk.hierarchyHandling'] = rng.choice(['SEPARATE_CHILDREN', 'INCLUDE_CHILDREN'])
            ch = [c['id'] for c in n['children']]
            n['edges'] = []
            for e in range(rng.randint(0, 2 * k)):
                n['edges'].append({'id': '%s_e%d' % (nid, e), 'sources': [rng.choice(ch)], 'targets': [rng.choice(ch)]})
        if lo:
            n['layoutOptions'] = lo
        return n

    top = [node(0, 'g%d_' % i) for _ in range(rng.randint(2, 7))]
    root_lo = {'elk.algorithm': 'layered', 'elk.hierarchyHandling': 'INCLUDE_CHILDREN'}
    mo_options(root_lo, rng.choice([0.0, 0.4, 0.8, 1.0]))
    if rng.random() < 0.3:
        root_lo['elk.direction'] = rng.choice(['RIGHT', 'DOWN', 'LEFT', 'UP'])

    # all nodes for hierarchy-crossing edges
    alln = []

    def collect(n):
        alln.append(n['id'])
        for c in n.get('children', []):
            collect(c)
    for t in top:
        collect(t)
    edges = []
    ids = [t['id'] for t in top]
    for e in range(rng.randint(1, 3 * len(top))):
        if rng.random() < 0.25:
            s, t = rng.choice(alln), rng.choice(alln)
        else:
            s, t = rng.choice(ids), rng.choice(ids)
        edges.append({'id': 'g%d_e%d' % (i, e), 'sources': [s], 'targets': [t]})
    return {'id': 'root', 'layoutOptions': root_lo, 'children': top, 'edges': edges}


for i in range(count):
    with open(os.path.join(out, 'h%04d.json' % i), 'w') as f:
        json.dump(make_graph(i), f, indent=1)
