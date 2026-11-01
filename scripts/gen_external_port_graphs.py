#!/usr/bin/env python3
"""Random layered graphs that mix the external-port features ("x" sets of
`scripts/run_random_java_parity.sh --sets x`, agent EXT).

    python3 -I scripts/gen_external_port_graphs.py OUT_DIR COUNT SEED

Compound nodes of two or three levels whose ports sit on all four sides, with
`org.eclipse.elk.portConstraints` drawn from FREE / FIXED_SIDE / FIXED_ORDER / FIXED_RATIO / FIXED_POS /
UNDEFINED on parents and children, explicit `port.side`, `port.index`, `port.borderOffset`, `port.anchor`,
port labels with `portLabels.placement` and `portLabels.treatAsGroup`, `portAlignment.*`,
`spacing.portPort`, `spacing.portsSurrounding` and `padding`; hierarchy handling INCLUDE_CHILDREN /
SEPARATE_CHILDREN / INHERIT mixed across levels with cross-hierarchy edges (inner node -> parent port ->
outside node, edges spanning two or three levels, edges from and to the external ports themselves,
hyperedges across levels; the edge is listed in its lowest common ancestor, in the root or in the source's
parent); inside self loops (`insideSelfLoops.activate`, `insideSelfLoops.yo`) on compound nodes;
interactive layouts (INTERACTIVE cycle breaking / layering / crossing minimisation) with preset node and
external port positions; all four directions; ORTHOGONAL / POLYLINE / SPLINES routing; node size
constraints and options; `allowNonFlowPortsToSwitchSides`, `feedbackEdges`, `mergeHierarchyEdges`,
`crossingMinimization.hierarchicalSweepiness`, `considerModelOrder.*`; and some compound children laid out
by force / mrtree / rectpacking under a layered parent (`RecursiveGraphLayoutEngine` external ports). The
JSON path does not validate option ranges, so degenerate values are drawn on purpose (zero-size ports,
ports outside their node, negative offsets and indexes, sweepiness out of [-1, 1]). Graph k of a seed does
not depend on COUNT (one `random.Random` per graph, seeded with SEED and k), so a smaller count is a
prefix of a larger one.
"""
import json, os, random, sys

out, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
os.makedirs(out, exist_ok=True)
L = 'elk.layered.'
SIDES = ['NORTH', 'SOUTH', 'EAST', 'WEST']
PORT_CONSTRAINTS = ['FREE', 'FIXED_SIDE', 'FIXED_ORDER', 'FIXED_RATIO', 'FIXED_POS', 'UNDEFINED']
PORT_LABEL_PLACEMENTS = ['INSIDE', 'OUTSIDE', '[INSIDE, NEXT_TO_PORT_IF_POSSIBLE]',
                         '[OUTSIDE, NEXT_TO_PORT_IF_POSSIBLE]', '[OUTSIDE, ALWAYS_SAME_SIDE]',
                         '[INSIDE, ALWAYS_OTHER_SAME_SIDE]', '[OUTSIDE, SPACE_EFFICIENT]',
                         '[INSIDE, SPACE_EFFICIENT]', '[OUTSIDE, NEXT_TO_PORT_IF_POSSIBLE, SPACE_EFFICIENT]', '']
# rejected by ELK Java's node size calculator (`Invalid port label placement`), drawn in a few graphs only
INVALID_PORT_LABEL_PLACEMENTS = ['OUTSIDE ALWAYS_SAME_SIDE SPACE_EFFICIENT', '[INSIDE, ALWAYS_OTHER_SAME_SIDE, SPACE_EFFICIENT]']
CONSTRAINTS = ['PORTS', 'PORT_LABELS', 'NODE_LABELS', 'MINIMUM_SIZE']
SIZE_OPTIONS = ['DEFAULT_MINIMUM_SIZE', 'MINIMUM_SIZE_ACCOUNTS_FOR_PADDING', 'COMPUTE_PADDING',
                'OUTSIDE_NODE_LABELS_OVERHANG', 'PORTS_OVERHANG', 'UNIFORM_PORT_SPACING',
                'SPACE_EFFICIENT_PORT_LABELS', 'FORCE_TABULAR_NODE_LABELS', 'ASYMMETRICAL', 'PORT_LABELS_OUTSIDE']
ALIGNMENTS = ['BEGIN', 'CENTER', 'END', 'JUSTIFIED', 'DISTRIBUTED']
HH = ['INCLUDE_CHILDREN', 'SEPARATE_CHILDREN', 'INHERIT']


def pick(rng, items, weights=None):
    return rng.choices(items, weights)[0] if weights else rng.choice(items)


def subset(rng, xs, p=0.35):
    return [x for x in xs if rng.random() < p]


def margins(rng, vals):
    return '[top=%s,left=%s,bottom=%s,right=%s]' % tuple(pick(rng, vals) for _ in range(4))


def label(rng, text):
    return {'text': text, 'width': pick(rng, [0, 6, 15, 30]), 'height': pick(rng, [0, 5, 10])}


class Gen:
    def __init__(self, rng, i):
        self.rng = rng
        self.prefix = 'g%d_' % i
        self.ctr = 0
        self.ectr = 0
        self.parent = {}      # element id -> owning node id ('root' for top level nodes)
        self.kind = {}        # element id -> 'node' | 'port'
        self.nodes = {}       # node id -> json
        self.depth = {}
        self.compounds = []
        self.edges_of = {'root': []}
        # a few graphs keep the combinations ELK Java rejects (port label placement validation, ports without
        # side under a non-layered algorithm, hyperedges); the others avoid them so that most graphs lay out
        self.invalid = rng.random() < 0.04
        self.sided = False

    def eid(self):
        self.ectr += 1
        return '%se%d' % (self.prefix, self.ectr)

    # ---------------------------------------------------------------- nodes and ports
    def port_options(self, rng, node_lo, p, w, h):
        pc = node_lo.get('elk.portConstraints')
        plo = {}
        if pc in ('FIXED_SIDE', 'FIXED_ORDER', 'FIXED_RATIO', 'FIXED_POS') or rng.random() < 0.5:
            if rng.random() < 0.93:
                plo['elk.port.side'] = pick(rng, SIDES + ['UNDEFINED'], [3, 3, 3, 3, 1])
        if self.sided and plo.get('elk.port.side', 'UNDEFINED') == 'UNDEFINED' and not self.invalid:
            # the node size calculator of the non-layered algorithms needs a side on every port
            plo['elk.port.side'] = pick(rng, SIDES)
        if pc in ('FIXED_RATIO', 'FIXED_POS') or rng.random() < 0.2:
            # positions on, inside or outside the border (degenerate on purpose)
            side = plo.get('elk.port.side', pick(rng, SIDES))
            fx = {'WEST': 0, 'EAST': w}.get(side, rng.uniform(0, w))
            fy = {'NORTH': 0, 'SOUTH': h}.get(side, rng.uniform(0, h))
            if rng.random() < 0.15:
                fx, fy = fx + pick(rng, [-20, -5, 5, 30]), fy + pick(rng, [-20, 5, 30])
            p['x'], p['y'] = round(fx - p['width'] / 2, 1), round(fy - p['height'] / 2, 1)
        if rng.random() < 0.3:
            plo['elk.port.index'] = pick(rng, [0, 1, 2, 3, 5, 9, -1, 100])
        if rng.random() < 0.25:
            plo['elk.port.borderOffset'] = pick(rng, [0, 2, 5, 10, -3, -10, 0.5])
        if rng.random() < 0.12:
            plo['elk.port.anchor'] = '(%s,%s)' % (pick(rng, [0, 1, 2, -2, 10]), pick(rng, [0, 1, 3, -1, 12]))
        if rng.random() < 0.08:
            plo[L + 'allowNonFlowPortsToSwitchSides'] = rng.random() < 0.7
        if rng.random() < 0.06:
            plo['elk.portLabels.placement'] = pick(rng, PORT_LABEL_PLACEMENTS[:-1])
        return plo

    def add_ports(self, rng, nid, node, lo, many):
        w, h = node['width'], node['height']
        ports = []
        np_ = rng.randint(1, 7) if many else pick(rng, [0, 0, 1, 2, 3, 4])
        for j in range(np_):
            pid = '%s_p%d' % (nid, j)
            p = {'id': pid, 'width': pick(rng, [0, 0, 4, 6, 8, 12], [1, 1, 3, 3, 3, 1]),
                 'height': pick(rng, [0, 4, 6, 8, 12], [1, 3, 3, 3, 1])}
            plo = self.port_options(rng, lo, p, w, h)
            if plo:
                p['layoutOptions'] = plo
            if rng.random() < 0.3:
                p['labels'] = [label(rng, '%s_l%d' % (pid, k)) for k in range(pick(rng, [1, 1, 2]))]
            ports.append(p)
            self.parent[pid] = nid
            self.kind[pid] = 'port'
        if ports:
            node['ports'] = ports

    def node_options(self, rng, lo, compound):
        if rng.random() < (0.85 if compound else 0.55):
            lo['elk.portConstraints'] = pick(rng, PORT_CONSTRAINTS, [2, 4, 3, 2, 2, 1])
        if rng.random() < (0.5 if compound else 0.3):
            c = subset(rng, CONSTRAINTS, 0.45)
            lo['elk.nodeSize.constraints'] = ' '.join(c) if rng.random() < 0.7 else '[' + ', '.join(c) + ']'
        if rng.random() < 0.25:
            lo['elk.nodeSize.options'] = ' '.join(subset(rng, SIZE_OPTIONS, 0.25))
        if rng.random() < 0.15:
            lo['elk.nodeSize.minimum'] = '(%s,%s)' % (pick(rng, [0, 20, 60, 120]), pick(rng, [0, 20, 50]))
        if rng.random() < 0.3:
            lo['elk.portLabels.placement'] = pick(rng, PORT_LABEL_PLACEMENTS)
            if self.invalid and rng.random() < 0.3:
                lo['elk.portLabels.placement'] = pick(rng, INVALID_PORT_LABEL_PLACEMENTS)
        if 'ALWAYS' in lo.get('elk.portLabels.placement', '') and not self.invalid:
            # ALWAYS_(OTHER_)SAME_SIDE with SPACE_EFFICIENT (also through the size option) is rejected
            opts = lo.get('elk.nodeSize.options', '').replace('SPACE_EFFICIENT_PORT_LABELS', '').split()
            if 'elk.nodeSize.options' in lo:
                lo['elk.nodeSize.options'] = ' '.join(opts)
        if rng.random() < 0.12:
            lo['elk.portLabels.treatAsGroup'] = rng.random() < 0.5
        if rng.random() < 0.2:
            lo['elk.portAlignment.default'] = pick(rng, ALIGNMENTS)
        for s in ('north', 'south', 'east', 'west'):
            if rng.random() < 0.08:
                lo['elk.portAlignment.' + s] = pick(rng, ALIGNMENTS)
        if rng.random() < 0.25:
            lo['elk.spacing.portPort'] = pick(rng, [0, 2, 5, 10, 25, -4])
        if rng.random() < 0.2:
            lo['elk.spacing.portsSurrounding'] = margins(rng, [0, 0, 3, 8, -2])
        if compound and rng.random() < 0.4:
            lo['elk.padding'] = margins(rng, [0, 5, 12, 20, -5])
        if rng.random() < 0.08:
            lo['elk.spacing.labelPort'] = pick(rng, [0, 1, 4])
        if rng.random() < 0.1:
            lo['elk.nodeLabels.placement'] = pick(rng, ['[H_CENTER, V_TOP, INSIDE]', 'OUTSIDE V_BOTTOM H_LEFT',
                                                        'INSIDE V_CENTER H_RIGHT H_PRIORITY'])

    def make_node(self, rng, owner, depth, max_depth, layered_parent):
        self.ctr += 1
        nid = '%sn%d' % (self.prefix, self.ctr)
        compound = depth < max_depth and rng.random() < (0.55 if depth == 0 else 0.35)
        alg = pick(rng, ['force', 'mrtree', 'rectpacking']) if compound and layered_parent and rng.random() < 0.08 else None
        # ports laid out by a non-layered algorithm (its own or its parent's) get a side
        self.sided = not layered_parent or alg is not None
        node = {'id': nid, 'width': pick(rng, [10, 20, 30, 40, 60, 0], [2, 3, 3, 2, 1, 1]),
                'height': pick(rng, [10, 20, 30, 45, 0], [2, 3, 3, 1, 1])}
        if compound and rng.random() < 0.3:
            node['width'], node['height'] = pick(rng, [80, 150, 5]), pick(rng, [60, 120, 5])
        lo = {}
        self.node_options(rng, lo, compound)
        self.parent[nid] = owner
        self.kind[nid] = 'node'
        self.nodes[nid] = node
        self.depth[nid] = depth
        self.add_ports(rng, nid, node, lo, compound and rng.random() < 0.9)
        if rng.random() < 0.25:
            node['labels'] = [label(rng, nid + '_l')]
        if compound:
            self.compounds.append(nid)
            self.edges_of[nid] = []
            if alg is not None:
                lo['elk.algorithm'] = alg
                layered_child = False
            else:
                layered_child = True
                if rng.random() < 0.6:
                    lo['elk.hierarchyHandling'] = pick(rng, HH, [3, 2, 3])
            kids = [self.make_node(rng, nid, depth + 1, max_depth, layered_child)
                    for _ in range(rng.randint(1, 5))]
            node['children'] = kids
            if rng.random() < 0.15:
                lo[L + 'insideSelfLoops.activate'] = True
            if rng.random() < 0.15:
                lo['elk.direction'] = pick(rng, ['RIGHT', 'DOWN', 'LEFT', 'UP'])
            if rng.random() < 0.1:
                lo['elk.edgeRouting'] = pick(rng, ['ORTHOGONAL', 'POLYLINE', 'SPLINES'])
        if lo:
            node['layoutOptions'] = lo
        return node

    # ---------------------------------------------------------------- edges
    def ancestors(self, el):
        """Owning nodes of an element, innermost first, ending with 'root'."""
        out = []
        cur = self.parent.get(el)
        while cur is not None:
            out.append(cur)
            cur = self.parent.get(cur)
        return out

    def lca(self, a, b):
        aa = self.ancestors(a)
        bset = set(self.ancestors(b))
        for x in aa:
            if x in bset:
                return x
        return 'root'

    def add_edge(self, srcs, tgts, where=None, yo=False):
        rng = self.rng
        e = {'id': self.eid(), 'sources': srcs, 'targets': tgts}
        if rng.random() < 0.1:
            e['labels'] = [label(rng, e['id'] + '_l')]
        lo = {}
        if yo:
            lo[L + 'insideSelfLoops.yo'] = True
        if rng.random() < 0.05:
            lo['elk.edge.thickness'] = pick(rng, [0, 2, 6])
        if lo:
            e['layoutOptions'] = lo
        if where is None:
            r = rng.random()
            if r < 0.75:
                where = self.lca(srcs[0], tgts[0])
            elif r < 0.9:
                where = 'root'
            else:
                where = self.ancestors(srcs[0])[0]
                if self.kind.get(srcs[0]) == 'port':
                    where = self.parent[where] if where in self.parent else 'root'
        if where not in self.edges_of:
            where = 'root'
        self.edges_of[where].append(e)

    def elements_in(self, owner):
        """Children of owner and their ports."""
        out = []
        for el, par in self.parent.items():
            if par == owner and self.kind[el] == 'node':
                out.append(el)
                out.extend(p for p, pp in self.parent.items() if pp == el and self.kind[p] == 'port')
        return out

    def ports_of(self, nid):
        return [p for p, pp in self.parent.items() if pp == nid and self.kind[p] == 'port']

    def make_edges(self):
        rng = self.rng
        owners = ['root'] + self.compounds
        # edges inside each graph, among its children and with its own (external) ports
        for owner in owners:
            els = self.elements_in(owner)
            if not els:
                continue
            ext = self.ports_of(owner) if owner != 'root' else []
            for _ in range(rng.randint(1, len(els) + 1)):
                a, b = pick(rng, els), pick(rng, els)
                if a == b or self.parent.get(a) == b or self.parent.get(b) == a:
                    continue
                self.add_edge([a], [b], where=owner if rng.random() < 0.85 else None)
            for p in ext:
                if rng.random() < 0.75:
                    k = pick(rng, els)
                    if self.parent.get(k) == p:
                        continue
                    if rng.random() < 0.5:
                        self.add_edge([p], [k], where=owner if rng.random() < 0.8 else None)
                    else:
                        self.add_edge([k], [p], where=owner if rng.random() < 0.8 else None)
            # external port to external port through the compound node
            if len(ext) >= 2 and rng.random() < 0.2:
                a, b = rng.sample(ext, 2)
                self.add_edge([a], [b], where=owner)
        # edges from the outside to the compound's ports (the outer half of an external port path)
        for c in self.compounds:
            outer = self.parent[c]
            els = [x for x in self.elements_in(outer) if x != c and self.parent.get(x) != c]
            for p in self.ports_of(c):
                if els and rng.random() < 0.6:
                    o = pick(rng, els)
                    if rng.random() < 0.5:
                        self.add_edge([o], [p], where=outer if rng.random() < 0.8 else None)
                    else:
                        self.add_edge([p], [o], where=outer if rng.random() < 0.8 else None)
        # cross-hierarchy edges spanning two or three levels
        all_els = list(self.parent)
        for _ in range(rng.randint(0, 5)):
            a, b = pick(rng, all_els), pick(rng, all_els)
            if a == b or a in self.ancestors(b) or b in self.ancestors(a):
                continue
            if self.kind[a] == 'port' and self.parent[a] in self.ancestors(b):
                continue
            self.add_edge([a], [b])
        # hyperedges (several sources or targets) across levels
        for _ in range(pick(rng, [0, 1, 2]) if self.invalid or rng.random() < 0.05 else 0):
            k = rng.randint(3, 4)
            cand = rng.sample(all_els, min(k, len(all_els)))
            if len(cand) < 3:
                continue
            ns = rng.randint(1, len(cand) - 1)
            srcs, tgts = cand[:ns], cand[ns:]
            if set(srcs) & set(tgts):
                continue
            self.add_edge(srcs, tgts)
        # inside self loops: edges between the ports of a compound node (or the node itself), listed in
        # the compound node
        for c in self.compounds:
            node = self.nodes[c]
            lo = node.get('layoutOptions', {})
            act = lo.get(L + 'insideSelfLoops.activate')
            if act or rng.random() < 0.1:
                ps = self.ports_of(c)
                for _ in range(rng.randint(1, 3)):
                    a = pick(rng, ps) if ps and rng.random() < 0.8 else c
                    b = pick(rng, ps) if ps and rng.random() < 0.8 else c
                    self.add_edge([a], [b], where=c if rng.random() < 0.7 else self.parent[c],
                                  yo=rng.random() < 0.6)

    # ---------------------------------------------------------------- interactive positions
    def preset_positions(self):
        rng = self.rng
        for nid, node in self.nodes.items():
            if rng.random() < 0.9:
                node['x'], node['y'] = round(rng.uniform(-20, 300), 1), round(rng.uniform(-20, 300), 1)
            for p in node.get('ports', []):
                if 'x' not in p and rng.random() < 0.8:
                    p['x'] = round(pick(rng, [0, node['width'], rng.uniform(-10, node['width'] + 10)]), 1)
                    p['y'] = round(pick(rng, [0, node['height'], rng.uniform(-10, node['height'] + 10)]), 1)


def root_options(rng, lo, hier):
    lo['elk.algorithm'] = 'layered'
    if hier is not None:
        lo['elk.hierarchyHandling'] = hier
    if rng.random() < 0.5:
        lo['elk.direction'] = pick(rng, ['RIGHT', 'DOWN', 'LEFT', 'UP'])
    routing = pick(rng, ['ORTHOGONAL', 'POLYLINE', 'SPLINES', None], [4, 2, 2, 3])
    if routing:
        lo['elk.edgeRouting'] = routing
    if rng.random() < 0.15:
        lo[L + 'feedbackEdges'] = True
    if rng.random() < 0.2:
        lo[L + 'mergeHierarchyEdges'] = rng.random() < 0.5
    if rng.random() < 0.1:
        lo[L + 'mergeEdges'] = True
    if rng.random() < 0.2:
        lo[L + 'crossingMinimization.hierarchicalSweepiness'] = pick(rng, [-1, -0.5, 0, 0.1, 0.5, 1, 2, -3])
    if rng.random() < 0.1:
        lo[L + 'crossingMinimization.greedySwitchHierarchical.type'] = pick(rng, ['OFF', 'ONE_SIDED', 'TWO_SIDED'])
    if rng.random() < 0.15:
        lo[L + 'considerModelOrder.strategy'] = pick(rng, ['NONE', 'NODES_AND_EDGES', 'PREFER_EDGES', 'PREFER_NODES'])
    if rng.random() < 0.06:
        lo[L + 'considerModelOrder.portModelOrder'] = True
    if rng.random() < 0.06:
        lo[L + 'considerModelOrder.components'] = pick(rng, ['NONE', 'INSIDE_PORT_SIDE_GROUPS', 'MODEL_ORDER'])
    if rng.random() < 0.08:
        lo[L + 'allowNonFlowPortsToSwitchSides'] = True
    if rng.random() < 0.08:
        lo[L + 'insideSelfLoops.activate'] = True
    if rng.random() < 0.15:
        lo['elk.spacing.nodeNode'] = pick(rng, [0, 5, 20, 40])
    if rng.random() < 0.15:
        lo[L + 'spacing.nodeNodeBetweenLayers'] = pick(rng, [0, 5, 20, 50])
    if rng.random() < 0.1:
        lo['elk.spacing.edgeNode'] = pick(rng, [0, 5, 15])
    if rng.random() < 0.1:
        lo['elk.spacing.portPort'] = pick(rng, [0, 5, 15])
    if rng.random() < 0.15:
        lo['elk.padding'] = margins(rng, [0, 5, 12, 30])
    if rng.random() < 0.1:
        lo['elk.portConstraints'] = pick(rng, PORT_CONSTRAINTS)
    if rng.random() < 0.08:
        lo[L + 'nodePlacement.strategy'] = pick(rng, ['BRANDES_KOEPF', 'NETWORK_SIMPLEX', 'LINEAR_SEGMENTS',
                                                      'SIMPLE'])
    if rng.random() < 0.08:
        lo[L + 'cycleBreaking.strategy'] = pick(rng, ['GREEDY', 'DEPTH_FIRST', 'MODEL_ORDER'])
    if rng.random() < 0.05:
        lo[L + 'layering.strategy'] = pick(rng, ['NETWORK_SIMPLEX', 'LONGEST_PATH', 'COFFMAN_GRAHAM'])
    if rng.random() < 0.06:
        lo[L + 'compaction.postCompaction.strategy'] = pick(rng, ['EDGE_LENGTH', 'LEFT', 'RIGHT'])
    if rng.random() < 0.08:
        lo['elk.separateConnectedComponents'] = rng.random() < 0.5


def make_graph(rng, i):
    g = Gen(rng, i)
    max_depth = pick(rng, [1, 2, 2], [1, 2, 1])
    hier = pick(rng, ['INCLUDE_CHILDREN', 'SEPARATE_CHILDREN', 'INHERIT', None], [5, 3, 1, 3])
    top = [g.make_node(rng, 'root', 0, max_depth, True) for _ in range(rng.randint(2, 6))]
    g.make_edges()
    lo = {}
    root_options(rng, lo, hier)
    interactive = rng.random() < 0.08
    if interactive:
        for k in ('cycleBreaking.strategy', 'layering.strategy', 'crossingMinimization.strategy'):
            if rng.random() < 0.8:
                lo[L + k] = 'INTERACTIVE'
        if rng.random() < 0.5:
            lo['elk.interactiveLayout'] = True
        g.preset_positions()
    for nid, edges in g.edges_of.items():
        if not edges:
            continue
        if nid == 'root':
            continue
        g.nodes[nid]['edges'] = edges
    graph = {'id': 'root', 'layoutOptions': lo, 'children': top, 'edges': g.edges_of['root']}
    return graph


for i in range(count):
    rng = random.Random('%d/%d' % (seed, i))
    with open(os.path.join(out, 'x%04d.json' % i), 'w') as f:
        json.dump(make_graph(rng, i), f, indent=1)
