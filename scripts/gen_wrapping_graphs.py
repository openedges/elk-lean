#!/usr/bin/env python3
"""Random layered graphs for the layered features no other set reaches ("w" sets of
`scripts/run_random_java_parity.sh --sets w`, agent COV).

    python3 -I scripts/gen_wrapping_graphs.py OUT_DIR COUNT SEED

Path-like and general layered graphs with random values of the options that the corpus and the
other random sets never (or hardly ever) select: graph wrapping (`wrapping.strategy` SINGLE_EDGE /
MULTI_EDGE, cutting strategy ARD / MSD / MANUAL, MSD freedom, correction factor, additional edge
spacing, multi-edge improvements and distance penalty, validify strategy; aspect ratios including 0,
negative and huge values), comment boxes (attached by one edge to a node or to a port on each side,
attached to several nodes, unattached, chains of comments), hypernodes (several edges, orthogonal
routing, joint junction points), edge labels (inline, HEAD/CENTER/TAIL placement, side selection,
center label placement strategy, several labels per edge, labels on self loops), node and port label
placements, spline routing (CONSERVATIVE / SLOPPY with the sloppy layer spacing factor), BK fixed
alignments and edge straightening, `mergeEdges` / `mergeHierarchyEdges` (a compound child with
`INCLUDE_CHILDREN` and hierarchy-crossing edges in some graphs), thoroughness and edge thickness.
Some graphs also set one of the object-typed options that ELK Java cannot parse from JSON
(`wrapping.cutting.cuts`, `wrapping.validify.forbiddenIndices`, `labels.labelManager`, ...: Java
throws `IllegalStateException: IDataType class expected for layout option ...` in the importer).
The JSON path does not validate option ranges, so out-of-range and degenerate values are drawn on
purpose. Graph k of a seed does not depend on COUNT (one `random.Random` per graph, seeded with
SEED and k), so a smaller count is a prefix of a larger one.
"""
import json, os, random, sys

out, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
os.makedirs(out, exist_ok=True)
L = 'elk.layered.'
SIDES = ['NORTH', 'SOUTH', 'EAST', 'WEST']
OBJECT_OPTIONS = [
    (L + 'wrapping.cutting.cuts', '2,4'),
    (L + 'wrapping.validify.forbiddenIndices', '1'),
    ('elk.labels.labelManager', 'x'),
    (L + 'considerModelOrder.groupModelOrder.cmEnforcedGroupOrders', '0,1'),
]


def pick(rng, items, weights=None):
    return rng.choices(items, weights)[0] if weights else rng.choice(items)


def label(rng, text, opts=None):
    lab = {'text': text, 'width': pick(rng, [0, 8, 15, 30, 60]), 'height': pick(rng, [0, 5, 10, 14])}
    if opts:
        lab['layoutOptions'] = opts
    return lab


def edge_label(rng, eid, k):
    lo = {}
    if rng.random() < 0.6:
        lo['elk.edgeLabels.placement'] = pick(rng, ['HEAD', 'CENTER', 'TAIL'], [3, 4, 3])
    if rng.random() < 0.35:
        lo['elk.edgeLabels.inline'] = pick(rng, [True, False], [3, 1])
    if rng.random() < 0.1:
        lo[L + 'edgeLabels.centerLabelPlacementStrategy'] = pick(
            rng, ['MEDIAN_LAYER', 'TAIL_LAYER', 'HEAD_LAYER', 'SPACE_EFFICIENT_LAYER', 'WIDEST_LAYER', 'CENTER_LAYER'])
    return label(rng, '%s_l%d' % (eid, k), lo)


def wrapping_options(rng, lo):
    lo[L + 'wrapping.strategy'] = pick(rng, ['SINGLE_EDGE', 'MULTI_EDGE', 'OFF'], [4, 5, 1])
    if rng.random() < 0.8:
        lo[L + 'wrapping.cutting.strategy'] = pick(rng, ['ARD', 'MSD', 'MANUAL'], [4, 4, 2])
    if rng.random() < 0.4:
        lo[L + 'wrapping.cutting.msd.freedom'] = pick(rng, [0, 1, 2, 3, 10, -1, -5])
    if rng.random() < 0.4:
        lo[L + 'wrapping.correctionFactor'] = pick(rng, [1.0, 0.5, 2.0, 0.25, 4, 0, -1, 1e-9])
    if rng.random() < 0.3:
        lo[L + 'wrapping.additionalEdgeSpacing'] = pick(rng, [0, 5, 10, 25, -10])
    if rng.random() < 0.4:
        lo[L + 'wrapping.multiEdge.improveCuts'] = rng.random() < 0.5
    if rng.random() < 0.3:
        lo[L + 'wrapping.multiEdge.distancePenalty'] = pick(rng, [0, 1, 2, 5, 100, -2])
    if rng.random() < 0.4:
        lo[L + 'wrapping.multiEdge.improveWrappedEdges'] = rng.random() < 0.5
    if rng.random() < 0.5:
        lo[L + 'wrapping.validify.strategy'] = pick(rng, ['GREEDY', 'LOOK_BACK', 'NO'])
    if rng.random() < 0.85:
        lo['elk.aspectRatio'] = pick(rng, [0.05, 0.1, 0.2, 0.3, 0.5, 0.8, 1.0, 1.6, 3, 0, -1, 1e-6, 1e9],
                                     [6, 8, 8, 6, 5, 3, 3, 2, 1, 1, 1, 1, 1])
    if rng.random() < 0.25:
        lo[L + 'layering.strategy'] = pick(rng, ['LONGEST_PATH', 'NETWORK_SIMPLEX', 'COFFMAN_GRAHAM',
                                                 'LONGEST_PATH_SOURCE', 'MIN_WIDTH'])


def graph_options(rng, lo, features):
    if 'wrap' in features:
        wrapping_options(rng, lo)
    if rng.random() < 0.3:
        lo['elk.direction'] = pick(rng, ['RIGHT', 'DOWN', 'LEFT', 'UP'])
    routing = pick(rng, ['ORTHOGONAL', 'POLYLINE', 'SPLINES', None], [4, 2, 3, 2])
    if 'hyper' in features and rng.random() < 0.8:
        routing = 'ORTHOGONAL'
    if routing:
        lo['elk.edgeRouting'] = routing
    if routing == 'SPLINES' or rng.random() < 0.1:
        if rng.random() < 0.7:
            lo[L + 'edgeRouting.splines.mode'] = pick(rng, ['CONSERVATIVE', 'SLOPPY'])
        if rng.random() < 0.5:
            lo[L + 'edgeRouting.splines.sloppy.layerSpacingFactor'] = pick(rng, [0.2, 0.5, 1, 0, -0.5, 3])
    if rng.random() < 0.3:
        lo[L + 'nodePlacement.strategy'] = pick(rng, ['BRANDES_KOEPF', 'NETWORK_SIMPLEX', 'LINEAR_SEGMENTS',
                                                      'SIMPLE'], [5, 1, 1, 1])
    if rng.random() < 0.4:
        lo[L + 'nodePlacement.bk.fixedAlignment'] = pick(rng, ['NONE', 'LEFTUP', 'RIGHTUP', 'LEFTDOWN',
                                                               'RIGHTDOWN', 'BALANCED'])
    if rng.random() < 0.3:
        lo[L + 'nodePlacement.bk.edgeStraightening'] = pick(rng, ['NONE', 'IMPROVE_STRAIGHTNESS'])
    if rng.random() < 0.3:
        lo[L + 'mergeEdges'] = True
    if rng.random() < 0.15:
        lo[L + 'mergeHierarchyEdges'] = rng.random() < 0.5
    if rng.random() < 0.3:
        lo[L + 'thoroughness'] = pick(rng, [1, 2, 7, 20, 0, -1])
    if rng.random() < 0.4:
        lo[L + 'edgeLabels.sideSelection'] = pick(rng, ['ALWAYS_UP', 'ALWAYS_DOWN', 'DIRECTION_UP', 'DIRECTION_DOWN',
                                                        'SMART_UP', 'SMART_DOWN'])
    if rng.random() < 0.15:
        lo[L + 'edgeLabels.centerLabelPlacementStrategy'] = pick(
            rng, ['MEDIAN_LAYER', 'TAIL_LAYER', 'HEAD_LAYER', 'SPACE_EFFICIENT_LAYER', 'WIDEST_LAYER', 'CENTER_LAYER'])
    if rng.random() < 0.2:
        lo['elk.spacing.edgeLabel'] = pick(rng, [0, 2, 5, 12])
    if rng.random() < 0.15:
        lo['elk.spacing.labelLabel'] = pick(rng, [0, 3, 8])
    if rng.random() < 0.2:
        lo['elk.spacing.nodeNode'] = pick(rng, [0, 5, 20, 40])
    if rng.random() < 0.2:
        lo[L + 'spacing.nodeNodeBetweenLayers'] = pick(rng, [0, 5, 20, 50])
    if rng.random() < 0.15:
        lo[L + 'spacing.edgeNodeBetweenLayers'] = pick(rng, [0, 5, 20])
    if rng.random() < 0.1:
        lo[L + 'spacing.edgeEdgeBetweenLayers'] = pick(rng, [0, 5, 20])
    if rng.random() < 0.1:
        lo['elk.spacing.edgeEdge'] = pick(rng, [0, 5, 20])
    if rng.random() < 0.15:
        lo[L + 'feedbackEdges'] = True
    if rng.random() < 0.1:
        lo[L + 'unnecessaryBendpoints'] = True
    if rng.random() < 0.1:
        lo['elk.edgeLabels.inline'] = True
    if rng.random() < 0.15:
        lo['elk.nodeLabels.placement'] = pick(rng, ['[H_CENTER, V_TOP, OUTSIDE]', '[H_LEFT, V_CENTER, INSIDE]',
                                                    'H_CENTER V_CENTER INSIDE', 'OUTSIDE V_BOTTOM H_RIGHT'])
    if rng.random() < 0.1:
        lo['elk.portLabels.placement'] = pick(rng, ['OUTSIDE', 'INSIDE', '[OUTSIDE, NEXT_TO_PORT_IF_POSSIBLE]'])
    if rng.random() < 0.035:
        k, v = pick(rng, OBJECT_OPTIONS)
        lo[k] = v


def make_graph(rng, i):
    features = set()
    if rng.random() < 0.55:
        features.add('wrap')
    if rng.random() < 0.35:
        features.add('comment')
    if rng.random() < 0.3:
        features.add('hyper')
    if rng.random() < 0.6:
        features.add('elabels')
    if rng.random() < 0.15:
        features.add('compound')
    prefix = 'g%d_' % i
    n = rng.randint(3, 14) if 'wrap' not in features else rng.randint(4, 24)
    nodes = []
    for k in range(n):
        node = {'id': '%sn%d' % (prefix, k), 'width': pick(rng, [10, 20, 30, 40, 60, 0]),
                'height': pick(rng, [10, 20, 30, 45, 0])}
        lo = {}
        if rng.random() < 0.25:
            node['labels'] = [label(rng, '%sn%d_l%d' % (prefix, k, j)) for j in range(rng.randint(1, 2))]
            if rng.random() < 0.5:
                lo['elk.nodeLabels.placement'] = pick(
                    rng, ['[H_CENTER, V_TOP, OUTSIDE]', '[H_LEFT, V_CENTER, INSIDE]', 'H_CENTER V_CENTER INSIDE',
                          'OUTSIDE V_BOTTOM H_RIGHT', 'INSIDE V_TOP H_LEFT', '[H_CENTER, V_BOTTOM, OUTSIDE]'])
        if rng.random() < 0.3:
            ports = []
            fixed = rng.random() < 0.6
            if fixed:
                lo['elk.portConstraints'] = pick(rng, ['FIXED_SIDE', 'FIXED_ORDER', 'FIXED_POS'], [5, 3, 1])
            for j in range(rng.randint(1, 4)):
                p = {'id': '%sn%d_p%d' % (prefix, k, j), 'width': pick(rng, [0, 4, 8]), 'height': pick(rng, [0, 4, 8])}
                plo = {}
                if fixed or rng.random() < 0.3:
                    plo['elk.port.side'] = pick(rng, SIDES)
                if lo.get('elk.portConstraints') == 'FIXED_POS':
                    p['x'], p['y'] = rng.randint(0, 30), rng.randint(0, 30)
                if rng.random() < 0.2:
                    p['labels'] = [label(rng, p['id'] + '_l')]
                if plo:
                    p['layoutOptions'] = plo
                ports.append(p)
            node['ports'] = ports
            if rng.random() < 0.3:
                lo['elk.portLabels.placement'] = pick(rng, ['OUTSIDE', 'INSIDE', '[OUTSIDE, NEXT_TO_PORT_IF_POSSIBLE]',
                                                            '[INSIDE, ALWAYS_SAME_SIDE]'])
        if lo:
            node['layoutOptions'] = lo
        nodes.append(node)
    ends = [nd['id'] for nd in nodes]
    port_ids = {nd['id']: [p['id'] for p in nd.get('ports', [])] for nd in nodes}

    def end(nid):
        ps = port_ids.get(nid, [])
        if ps and rng.random() < 0.75:
            return rng.choice(ps)
        return nid

    edges = []
    ec = [0]

    def add_edge(s, t, labels=None, opts=None):
        e = {'id': '%se%d' % (prefix, ec[0]), 'sources': [s], 'targets': [t]}
        ec[0] += 1
        if labels is None and 'elabels' in features and rng.random() < 0.4:
            labels = [edge_label(rng, e['id'], j) for j in range(pick(rng, [1, 1, 2, 3]))]
        if labels:
            e['labels'] = labels
        if opts is None and rng.random() < 0.12:
            opts = {'elk.edge.thickness': pick(rng, [0, 1, 2, 5, 12])}
        if opts:
            e['layoutOptions'] = opts
        edges.append(e)
        return e

    # backbone: a path (wrapping works on path-like graphs) or a random DAG
    pathlike = 'wrap' in features and rng.random() < 0.7
    for k in range(1, n):
        if pathlike:
            src = k - 1 if rng.random() < 0.85 else rng.randrange(0, k)
        else:
            src = rng.randrange(0, k)
        add_edge(end(ends[src]), end(ends[k]))
    for _ in range(rng.randint(0, n // 2 if pathlike else n)):
        a, b = rng.randrange(n), rng.randrange(n)
        if rng.random() < 0.85 and a > b:
            a, b = b, a
        add_edge(end(ends[a]), end(ends[b]))
    if rng.random() < 0.3:
        # self loops (with labels)
        for _ in range(rng.randint(1, 2)):
            a = rng.randrange(n)
            labels = [edge_label(rng, 'sl%d' % ec[0], j) for j in range(rng.randint(0, 2))]
            add_edge(end(ends[a]), end(ends[a]), labels=labels or None)

    if 'comment' in features:
        for c in range(rng.randint(1, 4)):
            cid = '%sc%d' % (prefix, c)
            cnode = {'id': cid, 'width': pick(rng, [20, 40, 80]), 'height': pick(rng, [10, 20, 40]),
                     'layoutOptions': {'elk.commentBox': True}}
            if rng.random() < 0.3:
                cnode['labels'] = [label(rng, cid + '_l')]
            kind = pick(rng, ['node', 'port', 'none', 'two', 'chain'], [5, 4, 1, 1, 1])
            target = rng.randrange(n)
            if kind == 'port':
                tn = nodes[target]
                tlo = tn.setdefault('layoutOptions', {})
                if rng.random() < 0.8:
                    tlo['elk.portConstraints'] = pick(rng, ['FIXED_SIDE', 'FIXED_ORDER'])
                pid = '%s_cp%d' % (tn['id'], c)
                tn.setdefault('ports', []).append({'id': pid, 'width': 4, 'height': 4,
                                                   'layoutOptions': {'elk.port.side': pick(rng, SIDES)}})
                port_ids[tn['id']] = port_ids.get(tn['id'], []) + [pid]
                tgt = pid
            else:
                tgt = ends[target]
            nodes.append(cnode)
            if kind == 'none':
                continue
            if kind == 'chain' and c > 0:
                tgt = '%sc%d' % (prefix, c - 1)
            if rng.random() < 0.5:
                add_edge(cid, tgt, labels=[])
            else:
                add_edge(tgt, cid, labels=[])
            if kind == 'two':
                add_edge(cid, ends[rng.randrange(n)], labels=[])

    if 'hyper' in features:
        for h in range(rng.randint(1, 3)):
            hid = '%sh%d' % (prefix, h)
            hnode = {'id': hid, 'width': pick(rng, [0, 1, 2, 4]), 'height': pick(rng, [0, 1, 2, 4]),
                     'layoutOptions': {'elk.hypernode': True}}
            nodes.append(hnode)
            src = rng.randrange(n)
            add_edge(end(ends[src]), hid, labels=[])
            for _ in range(rng.randint(1, 4)):
                t = rng.randrange(n)
                if rng.random() < 0.8:
                    add_edge(hid, end(ends[t]), labels=[])
                else:
                    add_edge(end(ends[t]), hid, labels=[])

    root_lo = {'elk.algorithm': 'layered'}
    graph_options(rng, root_lo, features)
    graph = {'id': 'root', 'layoutOptions': root_lo, 'children': nodes, 'edges': edges}
    if 'compound' in features:
        # a compound child with its own path; hierarchy-crossing edges for mergeHierarchyEdges
        root_lo['elk.hierarchyHandling'] = 'INCLUDE_CHILDREN'
        cid = prefix + 'cmp'
        kids = [{'id': '%s_k%d' % (cid, j), 'width': 20, 'height': 20} for j in range(rng.randint(1, 4))]
        cedges = [{'id': '%s_e%d' % (cid, j), 'sources': [kids[j - 1]['id']], 'targets': [kids[j]['id']]}
                  for j in range(1, len(kids))]
        comp = {'id': cid, 'children': kids, 'edges': cedges}
        if rng.random() < 0.4:
            comp['layoutOptions'] = {L + 'mergeEdges': True}
        nodes.append(comp)
        for _ in range(rng.randint(1, 4)):
            k = rng.choice(kids)['id']
            o = ends[rng.randrange(n)]
            if rng.random() < 0.5:
                add_edge(o, k, labels=[])
            else:
                add_edge(k, o, labels=[])
    return graph


for i in range(count):
    rng = random.Random('%d/%d' % (seed, i))
    with open(os.path.join(out, 'w%04d.json' % i), 'w') as f:
        json.dump(make_graph(rng, i), f, indent=1)
