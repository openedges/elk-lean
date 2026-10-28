#!/usr/bin/env python3
"""Random graphs that exercise the node size / port label cell system (PH review):
ports with and without labels, nodes with and without labels, every node-size constraint/option
combination, port label placements, port constraints, hierarchy, several algorithms.
usage: gen_nodesize.py OUT_DIR COUNT [SEED]"""
import json, os, random, sys

ALGS = ["layered", "layered", "layered", "rectpacking", "mrtree", "radial", "force", "stress", "box", "fixed"]
CONSTRAINTS = ["NODE_LABELS", "PORT_LABELS", "PORTS", "MINIMUM_SIZE"]
OPTIONS = ["DEFAULT_MINIMUM_SIZE", "MINIMUM_SIZE_ACCOUNTS_FOR_PADDING", "COMPUTE_PADDING",
           "OUTSIDE_NODE_LABELS_OVERHANG", "PORTS_OVERHANG", "UNIFORM_PORT_SPACING",
           "SPACE_EFFICIENT_PORT_LABELS", "FORCE_TABULAR_NODE_LABELS", "ASYMMETRICAL"]
PORT_LABEL_PLACEMENTS = [[], ["INSIDE"], ["OUTSIDE"], ["INSIDE", "NEXT_TO_PORT_IF_POSSIBLE"],
                         ["OUTSIDE", "NEXT_TO_PORT_IF_POSSIBLE"], ["INSIDE", "SPACE_EFFICIENT"],
                         ["OUTSIDE", "SPACE_EFFICIENT"], ["INSIDE", "ALWAYS_SAME_SIDE"],
                         ["OUTSIDE", "ALWAYS_OTHER_SAME_SIDE"], ["INSIDE", "NEXT_TO_PORT_IF_POSSIBLE", "SPACE_EFFICIENT"]]
H = ["H_LEFT", "H_CENTER", "H_RIGHT"]
V = ["V_TOP", "V_CENTER", "V_BOTTOM"]
PORT_CONSTRAINTS = ["FREE", "FIXED_SIDE", "FIXED_ORDER", "FIXED_RATIO", "FIXED_POS", "UNDEFINED"]
SIDES = ["NORTH", "SOUTH", "EAST", "WEST"]


def subset(rng, xs, pmin=0.0):
    out = [x for x in xs if rng.random() < 0.4]
    if not out and rng.random() < pmin:
        out = [rng.choice(xs)]
    return out


def node_label_placement(rng):
    if rng.random() < 0.25:
        return None
    parts = [rng.choice(H), rng.choice(V), rng.choice(["INSIDE", "OUTSIDE"])]
    if rng.random() < 0.3:
        parts.append("H_PRIORITY")
    return " ".join(parts)


def label(rng, i, prefix):
    return {"id": f"{prefix}l{i}", "text": rng.choice(["a", "label", "a longer label text", ""]),
            "width": round(rng.uniform(0, 60), 1) if rng.random() < 0.9 else 0,
            "height": round(rng.uniform(0, 20), 1) if rng.random() < 0.9 else 0}


def size_options(rng, lo):
    c = subset(rng, CONSTRAINTS, 0.6)
    if c:
        lo["elk.nodeSize.constraints"] = " ".join(c)
    o = subset(rng, OPTIONS)
    if o:
        lo["elk.nodeSize.options"] = " ".join(o)
    if rng.random() < 0.3:
        lo["elk.nodeSize.minimum"] = f"({rng.choice([0, 10, 40, 100])},{rng.choice([0, 10, 30, 80])})"
    p = rng.choice(PORT_LABEL_PLACEMENTS)
    if p:
        lo["elk.portLabels.placement"] = " ".join(p)
    nlp = node_label_placement(rng)
    if nlp:
        lo["elk.nodeLabels.placement"] = nlp
    if rng.random() < 0.3:
        lo["elk.padding"] = f"[top={rng.choice([0, 5, 12])},left={rng.choice([0, 5, 12])},bottom={rng.choice([0, 5, 12])},right={rng.choice([0, 5, 12])}]"
    if rng.random() < 0.3:
        lo["elk.spacing.labelPort"] = str(rng.choice([0, 1, 3, 8]))
    if rng.random() < 0.3:
        lo["elk.spacing.portPort"] = str(rng.choice([0, 5, 10, 20]))
    if rng.random() < 0.3:
        lo["elk.spacing.labelLabel"] = str(rng.choice([0, 2, 6]))
    if rng.random() < 0.3:
        lo["elk.spacing.labelNode"] = str(rng.choice([0, 3, 7]))
    if rng.random() < 0.3:
        lo["elk.spacing.portsSurrounding"] = f"[top={rng.choice([0, 4])},left={rng.choice([0, 4])},bottom={rng.choice([0, 4])},right={rng.choice([0, 4])}]"
    if rng.random() < 0.2:
        lo["elk.portAlignment.default"] = rng.choice(["BEGIN", "CENTER", "END", "JUSTIFIED", "DISTRIBUTED"])


def make_node(rng, nid, depth, ids):
    n = {"id": nid, "width": round(rng.uniform(10, 80), 1), "height": round(rng.uniform(10, 60), 1)}
    lo = {}
    if rng.random() < 0.5:
        size_options(rng, lo)
    if rng.random() < 0.6:
        lo["elk.portConstraints"] = rng.choice(PORT_CONSTRAINTS)
    if lo:
        n["layoutOptions"] = lo
    nl = rng.choice([0, 0, 1, 1, 2, 3])
    if nl:
        n["labels"] = [label(rng, i, nid) for i in range(nl)]
    np_ = rng.choice([0, 0, 1, 2, 3, 5])
    if np_:
        ports = []
        for i in range(np_):
            p = {"id": f"{nid}p{i}", "width": rng.choice([0, 4, 8, 12]), "height": rng.choice([0, 4, 8, 12])}
            plo = {}
            if rng.random() < 0.6:
                plo["elk.port.side"] = rng.choice(SIDES)
            if rng.random() < 0.2:
                plo["elk.port.borderOffset"] = str(rng.choice([-3, 0, 2, 5]))
            if rng.random() < 0.15:
                plo["elk.port.index"] = str(rng.randint(0, 4))
            if rng.random() < 0.15:
                plo["elk.portLabels.placement"] = " ".join(rng.choice(PORT_LABEL_PLACEMENTS)) or "INSIDE"
            if plo:
                p["layoutOptions"] = plo
            pl = rng.choice([0, 0, 0, 1, 1, 2])
            if pl:
                p["labels"] = [label(rng, j, p["id"]) for j in range(pl)]
            ports.append(p)
            ids.append(p["id"])
        n["ports"] = ports
    ids.append(nid)
    if depth < 2 and rng.random() < 0.25:
        children, edges, cids = make_children(rng, nid + "_", depth + 1)
        n["children"] = children
        if edges:
            n["edges"] = edges
        clo = n.setdefault("layoutOptions", {})
        if rng.random() < 0.5:
            clo["elk.hierarchyHandling"] = "INCLUDE_CHILDREN"
        if rng.random() < 0.4:
            clo["elk.algorithm"] = rng.choice(ALGS)
    return n


def make_children(rng, prefix, depth):
    count = rng.randint(1, 8) if depth else rng.randint(2, 12)
    ids = []
    children = [make_node(rng, f"{prefix}n{i}", depth, ids) for i in range(count)]
    endpoints = [i for i in ids]
    edges = []
    for i in range(rng.randint(0, count + 3)):
        s, t = rng.choice(endpoints), rng.choice(endpoints)
        if s == t or s.startswith(t) or t.startswith(s):
            continue
        e = {"id": f"{prefix}e{i}", "sources": [s], "targets": [t]}
        if rng.random() < 0.3:
            e["labels"] = [label(rng, 0, e["id"])]
        edges.append(e)
    return children, edges, ids


def main():
    out, count = sys.argv[1], int(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    os.makedirs(out, exist_ok=True)
    for k in range(count):
        rng = random.Random(seed * 100003 + k)
        lo = {"elk.algorithm": rng.choice(ALGS)}
        size_options(rng, lo)
        if rng.random() < 0.5:
            lo["elk.hierarchyHandling"] = rng.choice(["INCLUDE_CHILDREN", "SEPARATE_CHILDREN"])
        if rng.random() < 0.3:
            lo["elk.direction"] = rng.choice(["RIGHT", "DOWN", "LEFT", "UP"])
        if rng.random() < 0.3:
            lo["elk.edgeRouting"] = rng.choice(["ORTHOGONAL", "POLYLINE", "SPLINES"])
        if rng.random() < 0.3:
            lo["elk.layered.nodePlacement.strategy"] = rng.choice(["BRANDES_KOEPF", "NETWORK_SIMPLEX", "LINEAR_SEGMENTS", "SIMPLE"])
        if rng.random() < 0.3:
            lo["elk.layered.crossingMinimization.strategy"] = rng.choice(["LAYER_SWEEP", "NONE", "INTERACTIVE"])
        children, edges, _ = make_children(rng, "", 0)
        g = {"id": "root", "layoutOptions": lo, "children": children}
        if edges:
            g["edges"] = edges
        with open(os.path.join(out, f"g{k:04d}.json"), "w") as f:
            json.dump(g, f, indent=1)
    print(f"wrote {count} graphs to {out}")


if __name__ == "__main__":
    main()
