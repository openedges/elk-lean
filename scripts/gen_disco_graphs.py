#!/usr/bin/env python3
"""Random DisCo graphs ("c" sets of `scripts/run_random_java_parity.sh`, agent DIS).

    python3 -I scripts/gen_disco_graphs.py OUT_DIR COUNT [SEED]

None of the other generators selects `org.eclipse.elk.disco`. Here every graph has a DisCo layout
node: usually the root, sometimes (about one graph in seven) a compound child of a `fixed` root, so
that edges between the DisCo node's ports and its children become DisCo extensions (at the root,
ELK Java throws a `NullPointerException` for edges that start at the root and only lays out edges
that end there). The DisCo children form random connected components (nodes at given positions,
optional labels and ports with labels, edges with or without sections and bend points, edge labels,
the odd self loop and hyperedge); the DisCo options vary: the component layout algorithm (none,
`fixed`, `box`, `layered`, `random`, `rectpacking`), `aspectRatio`, `spacing.componentComponent`,
`padding`, `edge.thickness`, `polyomino.fill` and the polyomino sort/traversal options (which ELK
Java reads from an empty holder, i.e. never). Values are written as ELK Java parses them.
"""
import json
import os
import random
import sys


def pick(rng, p=0.5):
    return rng.random() < p


def rnd(rng, lo, hi):
    return round(rng.uniform(lo, hi), 1)


def label(rng, ident, x0, y0):
    return {"id": ident, "text": rng.choice(["a", "label", "long label"]),
            "x": rnd(rng, x0 - 10, x0 + 30), "y": rnd(rng, y0 - 10, y0 + 30),
            "width": rnd(rng, 2, 40), "height": rnd(rng, 2, 15)}


def border_point(rng, w, h):
    side = rng.randrange(4)
    if side == 0:
        return rnd(rng, 0, w), 0.0, side
    if side == 1:
        return w, rnd(rng, 0, h), side
    if side == 2:
        return rnd(rng, 0, w), h, side
    return 0.0, rnd(rng, 0, h), side


def make_ports(rng, nid, w, h):
    ports = []
    for k in range(rng.randint(1, 3)):
        px, py, _ = border_point(rng, w, h)
        pw, ph = rng.choice([(0, 0), (4, 4), (8, 6)])
        port = {"id": f"{nid}p{k}", "x": round(px - pw / 2, 1), "y": round(py - ph / 2, 1), "width": pw, "height": ph}
        if pick(rng, 0.2):
            port["labels"] = [label(rng, f"{nid}p{k}l", 0, 0)]
        ports.append(port)
    return ports


def section(rng, sid, a, b):
    sec = {"id": sid, "startPoint": {"x": a[0], "y": a[1]}, "endPoint": {"x": b[0], "y": b[1]}}
    bends = []
    for _ in range(rng.choice([0, 0, 1, 2, 3])):
        bends.append({"x": rnd(rng, min(a[0], b[0]) - 30, max(a[0], b[0]) + 30),
                      "y": rnd(rng, min(a[1], b[1]) - 30, max(a[1], b[1]) + 30)})
    if bends:
        sec["bendPoints"] = bends
    return sec


def anchor(shape, port):
    """Absolute anchor (relative to the DisCo node) of an edge end."""
    if port is not None:
        return (round(shape["x"] + port["x"] + port["width"] / 2, 1),
                round(shape["y"] + port["y"] + port["height"] / 2, 1))
    return (round(shape["x"] + shape["width"] / 2, 1), round(shape["y"] + shape["height"] / 2, 1))


def disco_children(rng, tag, area):
    """Nodes and inner edges of a DisCo node, grouped in random components."""
    children, edges, ends = [], [], []
    ncomp = rng.randint(1, 7)
    eid = 0
    for c in range(ncomp):
        cx, cy = rnd(rng, 0, area), rnd(rng, 0, area)
        comp = []
        for k in range(rng.randint(1, 4)):
            nid = f"{tag}c{c}n{k}"
            w, h = (rnd(rng, 5, 80), rnd(rng, 5, 60)) if not pick(rng, 0.05) else (0, 0)
            node = {"id": nid, "x": rnd(rng, cx - 60, cx + 60), "y": rnd(rng, cy - 60, cy + 60),
                    "width": w, "height": h}
            if pick(rng, 0.2):
                node["labels"] = [label(rng, f"{nid}l", 0, 0)]
            if pick(rng, 0.25):
                node["ports"] = make_ports(rng, nid, w, h)
            children.append(node)
            comp.append(node)
        for k in range(1, len(comp)):
            s, t = comp[rng.randrange(k)], comp[k]
            if pick(rng):
                s, t = t, s
            ends.append((s, t))
        for _ in range(rng.choice([0, 0, 1, 2])):
            s, t = rng.choice(comp), rng.choice(comp)
            if s is not t or pick(rng, 0.2):
                ends.append((s, t))
    for s, t in ends:
        sp = rng.choice(s["ports"]) if s.get("ports") and pick(rng, 0.6) else None
        tp = rng.choice(t["ports"]) if t.get("ports") and pick(rng, 0.6) else None
        e = {"id": f"{tag}e{eid}", "sources": [sp["id"] if sp else s["id"]],
             "targets": [tp["id"] if tp else t["id"]]}
        if pick(rng, 0.75):
            e["sections"] = [section(rng, f"{tag}e{eid}s", anchor(s, sp), anchor(t, tp))]
        if pick(rng, 0.15):
            a = anchor(s, sp)
            e["labels"] = [label(rng, f"{tag}e{eid}l", a[0], a[1])]
        if pick(rng, 0.2):
            e["layoutOptions"] = {"elk.edge.thickness": str(rng.choice([0, 1, 3, 6]))}
        edges.append(e)
        eid += 1
    if len(children) >= 3 and pick(rng, 0.03):
        a, b, c = rng.sample(children, 3)
        edges.append({"id": f"{tag}h", "sources": [a["id"], b["id"]], "targets": [c["id"]]})
    return children, edges


def external_edges(rng, tag, owner_id, w, h, children, outgoing_only):
    """Ports of the DisCo node and edges between them and its children (DisCo extensions)."""
    ports, edges = [], []
    for k in range(rng.randint(1, 3)):
        px, py, _ = border_point(rng, w, h)
        ports.append({"id": f"{owner_id}P{k}", "x": round(px - 2, 1), "y": round(py - 2, 1), "width": 4, "height": 4})
    for k in range(rng.randint(1, 4)):
        port = rng.choice(ports)
        child = rng.choice(children)
        outer = (round(port["x"] + 2, 1), round(port["y"] + 2, 1))
        inner = anchor(child, None)
        incoming = not outgoing_only and pick(rng, 0.5)
        if incoming:
            e = {"id": f"{tag}x{k}", "sources": [port["id"]], "targets": [child["id"]]}
            a, b = outer, inner
        else:
            e = {"id": f"{tag}x{k}", "sources": [child["id"]], "targets": [port["id"]]}
            a, b = inner, outer
        if pick(rng, 0.9):
            e["sections"] = [section(rng, f"{tag}x{k}s", a, b)]
        edges.append(e)
    return ports, edges


def disco_options(rng):
    lo = {"elk.algorithm": "disco"}
    alg = rng.choice(["", "", "", "", "fixed", "fixed", "box", "box", "layered", "random", "rectpacking"])
    if alg:
        lo["org.eclipse.elk.disco.componentCompaction.componentLayoutAlgorithm"] = alg
    if pick(rng, 0.1):
        lo["org.eclipse.elk.disco.componentCompaction.strategy"] = "POLYOMINO"
    if pick(rng, 0.3):
        lo["elk.aspectRatio"] = str(rng.choice([0.3, 0.5, 1.0, 1.6, 3.0]))
    if pick(rng, 0.4):
        lo["elk.spacing.componentComponent"] = str(rng.choice([0, 5, 20, 41, 60]))
    if pick(rng, 0.3):
        lo["elk.padding"] = "[top=%d,left=%d,bottom=%d,right=%d]" % tuple(rng.choice([0, 5, 14, 20]) for _ in range(4))
    if pick(rng, 0.15):
        lo["elk.edge.thickness"] = str(rng.choice([0, 2, 5]))
    if pick(rng, 0.3):
        lo["org.eclipse.elk.polyomino.fill"] = rng.choice(["true", "false"])
    if pick(rng, 0.2):
        lo["org.eclipse.elk.polyomino.lowLevelSort"] = rng.choice(["BY_SIZE", "BY_SIZE_AND_SHAPE"])
    if pick(rng, 0.2):
        lo["org.eclipse.elk.polyomino.highLevelSort"] = rng.choice(
            ["NUM_OF_EXTERNAL_SIDES_THAN_NUM_OF_EXTENSIONS_LAST", "CORNER_CASES_THAN_SINGLE_SIDE_LAST"])
    if pick(rng, 0.2):
        lo["org.eclipse.elk.polyomino.traversalStrategy"] = rng.choice(
            ["SPIRAL", "LINE_BY_LINE", "MANHATTAN", "JITTER", "QUADRANTS_LINE_BY_LINE", "QUADRANTS_MANHATTAN",
             "QUADRANTS_JITTER", "COMBINE_LINE_BY_LINE_MANHATTAN", "COMBINE_JITTER_MANHATTAN"])
    if lo.get("org.eclipse.elk.disco.componentCompaction.componentLayoutAlgorithm") == "random":
        lo["elk.randomSeed"] = str(rng.choice([1, 7, 42]))
    return lo


def make_graph(rng):
    area = rng.choice([150, 300, 600])
    if pick(rng, 1 / 7):
        # DisCo on a compound child of a fixed root: extensions in both directions
        w, h = rnd(rng, 100, 400), rnd(rng, 100, 400)
        children, edges = disco_children(rng, "d", area)
        comp = {"id": "dc", "x": 10, "y": 10, "width": w, "height": h, "layoutOptions": disco_options(rng),
                "children": children}
        if pick(rng, 0.7):
            ports, ext = external_edges(rng, "d", "dc", w, h, children, outgoing_only=False)
            comp["ports"] = ports
            edges = edges + ext
        if edges:
            comp["edges"] = edges
        other = {"id": "o", "x": w + 40, "y": 10, "width": 30, "height": 30}
        g = {"id": "root", "layoutOptions": {"elk.algorithm": "fixed"}, "children": [comp, other]}
        if comp.get("ports") and pick(rng, 0.5):
            g["edges"] = [{"id": "oe", "sources": ["o"], "targets": [comp["ports"][0]["id"]]}]
        return g
    children, edges = disco_children(rng, "r", area)
    g = {"id": "root", "layoutOptions": disco_options(rng), "children": children}
    if pick(rng, 0.15):
        w, h = rnd(rng, 100, 400), rnd(rng, 100, 400)
        g["width"], g["height"] = w, h
        ports, ext = external_edges(rng, "r", "root", w, h, children, outgoing_only=pick(rng, 0.6))
        g["ports"] = ports
        edges = edges + ext
    if edges:
        g["edges"] = edges
    return g


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    out, count = sys.argv[1], int(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    os.makedirs(out, exist_ok=True)
    for k in range(count):
        rng = random.Random(seed * 300007 + k)
        with open(os.path.join(out, f"g{k:04d}.json"), "w") as f:
            json.dump(make_graph(rng), f, indent=1)
    print(f"wrote {count} graphs to {out}")


if __name__ == "__main__":
    main()
