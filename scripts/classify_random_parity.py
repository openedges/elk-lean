#!/usr/bin/env python3
"""Classifies the ELK Java vs elk-lean differences of a random parity run.

    python3 -I scripts/classify_random_parity.py <run_dir> [--out <run_dir>/classification.md]
        [--examples 5] [--min-support 20]

Reads `<run_dir>/details.tsv` (written by `scripts/run_random_java_parity.sh`) and, for the inputs
both implementations laid out, the input graph and both layouts. Three views:

1. **Features**: the options present anywhere in the input (root algorithm, child algorithms, node
   size constraints/options, port/node label placement, port constraints, hierarchy handling, edge
   routing, direction, spacing/padding, ...), each with its mismatch rate and the lift against the
   population of inputs both sides laid out (`lift = P(mismatch | feature) / P(mismatch)`).
2. **Origin of the difference**: the layouts are compared element by element (tol 0) and every
   difference is attributed to the *layout unit* that computes it (a graph laid out by one algorithm
   invocation: a node with children, plus the graphs a layered `INCLUDE_CHILDREN` layout takes in).
   A compound child's size belongs to its own unit, its position to the parent unit, its ports and
   labels to its own unit unless the parent unit is non-layered (whose node micro layout places them).
   ELK lays out bottom-up, so the deepest units with differences are where they start (the units
   above inherit the changed child sizes). Kinds: `node-size`, `node-position`, `port-position`,
   `node-label`, `port-label`, `edge-route`, `edge-label`, `edge-extra-section`/`edge-missing-section`
   (sections on one side only), `graph-size`, `structure`.
3. **Flags**: every origin unit gets a flag from its algorithm and kinds (`unit_flags`, `FLAG_TEXT`):
   `NML:<alg>` (non-layered, node sizes/ports/labels), `DEF:<alg>` (non-layered, positions only, and
   Java's algorithm specific option defaults `JAVA_DEFAULTS` not set explicitly), `POS:<alg>`,
   `LNODE`, `LPOS`, `LEDGE`, `LSIZE`, `STRUCT`, `SEC:<alg>`; an input counts under each of its flags. Tables give
   counts, `rs=lean` (difference inherited from elk-rs, with `--with-oracle`), features with the highest
   lift under the flag, the origin kinds, and examples.

The functions `graph_features` / `options_summary` are also used by the run driver for the
`options` column of `details.tsv`.
"""
from __future__ import annotations

import argparse
import collections
import csv
import json
import math
import os
import sys

csv.field_size_limit(64 * 1024 * 1024)

DEFAULT_ALGORITHM = "layered"
LAYERED_IDS = {"layered", "org.eclipse.elk.layered"}


def short_alg(alg):
    if not alg:
        return DEFAULT_ALGORITHM
    alg = str(alg)
    return alg[len("org.eclipse.elk."):] if alg.startswith("org.eclipse.elk.") else alg


def opt(lo, key):
    """Option value by full (`elk.x`) or short (`x`) key."""
    if key in lo:
        return lo[key]
    if key.startswith("elk.") and key[4:] in lo:
        return lo[key[4:]]
    if "org.eclipse." + key in lo:
        return lo["org.eclipse." + key]
    return None


# ---------------------------------------------------------------------------------------------
# layout units (who lays out which graph)


def layout_units(root):
    """Maps the id of every node with children to (unit owner id, owner algorithm, included flag)
    following `RecursiveGraphLayoutEngine.layoutRecursively`: hierarchy handling `INHERIT` takes the
    parent's value (the root's becomes `SEPARATE_CHILDREN`); a layered node with `INCLUDE_CHILDREN`
    lays out its descendants unless one sets `SEPARATE_CHILDREN` or another algorithm (only layered
    supports the compound feature, so other algorithms ignore `INCLUDE_CHILDREN`)."""
    units = {}

    def visit(node, parent_hh, including):
        lo = node.get("layoutOptions", {}) or {}
        hh = opt(lo, "elk.hierarchyHandling") or "INHERIT"
        if hh == "INHERIT":
            hh = parent_hh if parent_hh else "SEPARATE_CHILDREN"
        explicit = opt(lo, "elk.algorithm")
        alg = short_alg(explicit)
        children = node.get("children", []) or []
        next_including = None
        if children:
            if including is not None and hh != "SEPARATE_CHILDREN" and (explicit is None or alg == including[1]):
                units[node["id"]] = (including[0], including[1], True)
                next_including = including
            else:
                units[node["id"]] = (node["id"], alg, False)
                if hh == "INCLUDE_CHILDREN" and alg in LAYERED_IDS:
                    next_including = (node["id"], alg)
        for c in children:
            visit(c, hh, next_including)

    visit(root, None, None)
    return units


# ---------------------------------------------------------------------------------------------
# features


def graph_features(g):
    """Set of feature strings of an input graph (options present anywhere)."""
    f = set()
    units = layout_units(g)
    root_alg = short_alg(opt(g.get("layoutOptions", {}) or {}, "elk.algorithm"))
    f.add(f"alg={root_alg}")
    root_id = g.get("id")
    for nid, (owner, alg, included) in units.items():
        if nid == root_id:
            continue
        f.add("compound")
        f.add(f"childalg={alg}{'(included)' if included else ''}")
    stats = collections.Counter()

    def node_opts(lo, where):
        c = opt(lo, "elk.nodeSize.constraints")
        if c is not None:
            vals = str(c).split()
            for v in vals:
                f.add(f"sizeConstraint={v}")
            if vals:
                f.add("sizeConstraint=any")
        o = opt(lo, "elk.nodeSize.options")
        if o is not None:
            for v in str(o).split():
                f.add(f"sizeOption={v}")
        if opt(lo, "elk.nodeSize.minimum") is not None:
            f.add("nodeSize.minimum")
        p = opt(lo, "elk.portLabels.placement")
        if p is not None:
            f.add(f"portLabels={' '.join(str(p).split()) or '(empty)'}")
        nl = opt(lo, "elk.nodeLabels.placement")
        if nl is not None:
            parts = str(nl).split()
            f.add("nodeLabels=" + ("INSIDE" if "INSIDE" in parts else "OUTSIDE" if "OUTSIDE" in parts else "other"))
            if "H_PRIORITY" in parts:
                f.add("nodeLabels.H_PRIORITY")
        pc = opt(lo, "elk.portConstraints")
        if pc is not None:
            f.add(f"portConstraints={pc}")
        if opt(lo, "elk.padding") is not None:
            f.add("padding")
        for k in ("labelPort", "portPort", "labelLabel", "labelNode", "portsSurrounding"):
            if opt(lo, f"elk.spacing.{k}") is not None:
                f.add(f"spacing.{k}")
        pa = opt(lo, "elk.portAlignment.default")
        if pa is not None:
            f.add(f"portAlignment={pa}")
        hh = opt(lo, "elk.hierarchyHandling")
        if hh is not None:
            f.add(f"hierarchyHandling={hh}@{where}")

    def walk(n, depth):
        lo = n.get("layoutOptions", {}) or {}
        node_opts(lo, "root" if depth == 0 else "child")
        if depth > 0:
            stats["nodes"] += 1
        if n.get("labels"):
            f.add("nodeLabels.present" if depth > 0 else "rootLabels.present")
        for p in n.get("ports", []) or []:
            stats["ports"] += 1
            plo = p.get("layoutOptions", {}) or {}
            if opt(plo, "elk.port.side") is None:
                f.add("port.side.missing")
            if opt(plo, "elk.port.borderOffset") is not None:
                f.add("port.borderOffset")
            if opt(plo, "elk.port.index") is not None:
                f.add("port.index")
            if opt(plo, "elk.portLabels.placement") is not None:
                f.add("portLabels@port")
            if p.get("labels"):
                f.add("portLabels.present")
        for e in n.get("edges", []) or []:
            stats["edges"] += 1
            if e.get("labels"):
                f.add("edgeLabels.present")
        for c in n.get("children", []) or []:
            walk(c, depth + 1)

    walk(g, 0)
    if stats["ports"]:
        f.add("ports.present")
    rlo = g.get("layoutOptions", {}) or {}
    for key, name in (("elk.edgeRouting", "edgeRouting"), ("elk.direction", "direction"),
                      ("elk.layered.nodePlacement.strategy", "nodePlacement"),
                      ("elk.layered.crossingMinimization.strategy", "crossingMin")):
        v = opt(rlo, key)
        if v is not None:
            f.add(f"{name}={v}")
    for nid, (owner, alg, included) in units.items():
        lo = node_by_id(g, nid).get("layoutOptions", {}) or {}
        if opt(lo, "elk.hierarchyHandling") == "INCLUDE_CHILDREN" and alg not in LAYERED_IDS and not included:
            f.add("INCLUDE_CHILDREN-ignored(non-layered)")
    return f


_node_index_cache = {}


def node_by_id(g, nid):
    key = id(g)
    idx = _node_index_cache.get(key)
    if idx is None:
        idx = {}
        stack = [g]
        while stack:
            n = stack.pop()
            idx[n.get("id")] = n
            stack.extend(n.get("children", []) or [])
        _node_index_cache.clear()
        _node_index_cache[key] = idx
    return idx.get(nid, {})


def options_summary(g):
    """Compact `details.tsv` column: root algorithm, child algorithms, then the other features."""
    f = graph_features(g)
    alg = next((x[4:] for x in f if x.startswith("alg=")), DEFAULT_ALGORITHM)
    child = sorted(x[9:] for x in f if x.startswith("childalg="))
    rest = sorted(x for x in f if not x.startswith(("alg=", "childalg=")))
    return alg, ",".join(child) if child else "-", " ".join(rest)


# ---------------------------------------------------------------------------------------------
# origin of the differences


def num_eq(a, b):
    try:
        x, y = float(a), float(b)
    except (TypeError, ValueError):
        return a == b
    if math.isnan(x) and math.isnan(y):
        return True
    return x == y


def deep_diff(a, b):
    """True when two JSON values differ (numbers by value, tol 0, lists of objects by id)."""
    if isinstance(a, bool) or isinstance(b, bool):
        return a != b
    if isinstance(a, (int, float)) and isinstance(b, (int, float)):
        return not num_eq(a, b)
    if type(a) is not type(b):
        return True
    if isinstance(a, dict):
        if set(a) != set(b):
            return True
        return any(deep_diff(a[k], b[k]) for k in a)
    if isinstance(a, list):
        if len(a) != len(b):
            return True
        if a and all(isinstance(x, dict) and "id" in x for x in a + b):
            a = sorted(a, key=lambda x: str(x["id"]))
            b = sorted(b, key=lambda x: str(x["id"]))
        return any(deep_diff(x, y) for x, y in zip(a, b))
    return a != b


GEOM = ("x", "y", "width", "height")


def geom_diff(a, b, keys=GEOM):
    for k in keys:
        if (k in a) != (k in b):
            return True
        if k in a and not num_eq(a[k], b[k]):
            return True
    return False


def by_id(xs):
    return {str(x.get("id")): x for x in (xs or []) if isinstance(x, dict)}


def labels_diff(a, b):
    la, lb = by_id(a.get("labels")), by_id(b.get("labels"))
    if set(la) != set(lb):
        return True
    return any(geom_diff(la[k], lb[k]) for k in la)


def origin_of(java, lean, units):
    """{unit owner id: set of difference kinds} of the deepest layout units with differences, and
    the full {unit: kinds} map."""
    local = collections.defaultdict(set)
    parent_unit = {}

    def unit_of(nid):
        return units.get(nid, (nid, None, False))[0]

    def visit(jn, ln, depth):
        nid = jn.get("id")
        u = unit_of(nid)
        if depth == 0 and geom_diff(jn, ln, ("width", "height")):
            local[u].add("graph-size")
        jc, lc = by_id(jn.get("children")), by_id(ln.get("children"))
        if set(jc) != set(lc):
            local[u].add("structure")
        for cid in jc:
            if cid not in lc:
                continue
            a, b = jc[cid], lc[cid]
            compound = bool(a.get("children"))
            if geom_diff(a, b, ("x", "y")):
                local[u].add("node-position")
            # a compound child's size comes from its own layout unit; its ports and labels too, unless
            # the parent unit is a non-layered algorithm, whose node micro layout (Java
            # `NodeMicroLayout`) places the ports and labels of every child, compound ones included
            cu = unit_of(cid) if compound else u
            if compound and cu != u:
                parent_unit.setdefault(cu, u)
            if geom_diff(a, b, ("width", "height")):
                local[cu].add("node-size" if not compound else "graph-size")
            if compound and units.get(u, (u, DEFAULT_ALGORITHM, False))[1] not in LAYERED_IDS:
                cu = u
            pa, pb = by_id(a.get("ports")), by_id(b.get("ports"))
            if set(pa) != set(pb):
                local[cu].add("structure")
            for pid in pa:
                if pid in pb:
                    if geom_diff(pa[pid], pb[pid]):
                        local[cu].add("port-position")
                    if labels_diff(pa[pid], pb[pid]):
                        local[cu].add("port-label")
            if labels_diff(a, b):
                local[cu].add("node-label")
            if compound:
                visit(a, b, depth + 1)
        je, le = by_id(jn.get("edges")), by_id(ln.get("edges"))
        if set(je) != set(le):
            local[u].add("structure")
        for eid in je:
            if eid not in le:
                continue
            a, b = je[eid], le[eid]
            if labels_diff(a, b):
                local[u].add("edge-label")
            if ("sections" in a) != ("sections" in b):
                # ELK Java writes no section for an edge the algorithm did not route
                local[u].add("edge-extra-section" if "sections" in b else "edge-missing-section")
                continue
            ra = {k: v for k, v in a.items() if k not in ("labels",)}
            rb = {k: v for k, v in b.items() if k not in ("labels",)}
            if deep_diff(ra, rb):
                local[u].add("edge-route")

    visit(java, lean, 0)
    if not local:
        return {}, {}
    # ancestors of every unit with differences
    has_desc = set()
    for u in local:
        p = parent_unit.get(u)
        seen = set()
        while p is not None and p not in seen:
            seen.add(p)
            has_desc.add(p)
            p = parent_unit.get(p)
    origins = {u: k for u, k in local.items() if u not in has_desc}
    return origins, dict(local)


# ---------------------------------------------------------------------------------------------
# classes

LEAF_KINDS = {"node-size", "port-position", "port-label", "node-label"}
POS_KINDS = {"node-position", "graph-size", "edge-route", "edge-label"}

# ELK Java's algorithm specific option defaults that differ from the CoreOptions defaults
# (`supports <option> = <value>` in the .melk files; see sanitize_for_java.py ALGORITHM_DEFAULTS)
JAVA_DEFAULTS = {
    "box": ("elk.padding", "elk.spacing.nodeNode", "elk.aspectRatio"),
    "fixed": ("elk.padding",),
    "force": ("elk.padding", "elk.spacing.nodeNode", "elk.spacing.edgeLabel", "elk.aspectRatio"),
    "mrtree": ("elk.padding", "elk.spacing.nodeNode", "elk.spacing.edgeNode", "elk.aspectRatio"),
    "rectpacking": ("elk.padding", "elk.spacing.nodeNode", "elk.aspectRatio"),
}

FLAG_TEXT = {
    "NML": "node micro layout of a non-layered algorithm: sizes/ports/labels of the nodes it lays out",
    "DEF": "non-layered algorithm whose Java option defaults (padding/spacing/aspect ratio) were not set "
           "explicitly: positions/graph size/routes",
    "POS": "non-layered algorithm, positions/graph size/routes (no default-option explanation)",
    "LNODE": "layered: node sizes/ports/labels (LabelAndNodeSizeProcessor, port placement, label placement)",
    "LPOS": "layered: node positions (no node size/port/label difference in the same unit)",
    "LEDGE": "layered: edge routes / edge labels only",
    "LSIZE": "layered: graph size only",
    "STRUCT": "structure (missing/extra elements)",
    "SEC": "edges with a section on one side only (ELK Java writes none for edges the algorithm does not "
           "route; `edge-extra-section`: elk-lean has one)",
}


def unit_flags(alg, kinds, unit_lo):
    """Flags of one origin unit: `<FLAG>` or `<FLAG>:<algorithm>` (see FLAG_TEXT); `SEC:<alg>` is
    added next to the flag of the other kinds."""
    out = set()
    if kinds & {"edge-extra-section", "edge-missing-section"}:
        out.add(f"SEC:{alg}")
        kinds = kinds - {"edge-extra-section", "edge-missing-section"}
        if not kinds:
            return out
    if "structure" in kinds:
        out.add("STRUCT")
    elif alg not in LAYERED_IDS:
        if kinds & LEAF_KINDS:
            out.add(f"NML:{alg}")
        elif [k for k in JAVA_DEFAULTS.get(alg, ()) if opt(unit_lo, k) is None]:
            out.add(f"DEF:{alg}")
        else:
            out.add(f"POS:{alg}")
    elif kinds & LEAF_KINDS:
        out.add("LNODE")
    elif "node-position" in kinds:
        out.add("LPOS")
    elif kinds & {"edge-route", "edge-label"}:
        out.add("LEDGE")
    else:
        out.add("LSIZE")
    return out


def flag_head(flag):
    return flag.split(":", 1)[0]


# ---------------------------------------------------------------------------------------------


def load(path):
    with open(path, encoding="utf-8") as f:
        txt = f.read()
    try:
        return json.loads(txt)
    except ValueError:
        return json.loads(txt.replace("-Infinity", '"-Inf"').replace("Infinity", '"Inf"').replace("NaN", '"NaN"'))


def fmt_pct(a, b):
    return f"{100.0 * a / b:.1f}%" if b else "-"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("run_dir")
    ap.add_argument("--out")
    ap.add_argument("--examples", type=int, default=5)
    ap.add_argument("--min-support", type=int, default=20)
    ap.add_argument("--tsv", help="per-input classification (default <run_dir>/classes.tsv)")
    args = ap.parse_args()
    run = args.run_dir
    out = args.out or os.path.join(run, "classification.md")
    tsv = args.tsv or os.path.join(run, "classes.tsv")
    with open(os.path.join(run, "details.tsv"), encoding="utf-8") as f:
        rows = list(csv.DictReader(f, delimiter="\t"))

    pop = [r for r in rows if r["lean_outcome"] == "ok" and r["java_outcome"] == "ok"]
    feats = {}
    classes = {}
    flagsets = {}
    origins_txt = {}
    class_rows = []
    for r in pop:
        key = (r["set"], r["input"])
        g = load(r["input_path"])
        feats[key] = graph_features(g)
        if r["match_class"] == "exact":
            continue
        if r["match_class"] == "tol1e-6":
            classes[key] = "T"
            flagsets[key] = {"T"}
            origins_txt[key] = "-"
            continue
        units = layout_units(g)
        try:
            java = load(r["java_layout"])
            lean = load(r["lean_layout"])
            origins, _ = origin_of(java, lean, units)
        except Exception as e:  # noqa: BLE001
            classes[key] = "Z"
            flagsets[key] = {"Z"}
            origins_txt[key] = f"compare error {type(e).__name__}"
            continue
        flags = set()
        parts = []
        root_alg = short_alg(opt(g.get("layoutOptions", {}) or {}, "elk.algorithm"))
        for u, k in sorted(origins.items()):
            alg = root_alg if u == g.get("id") else units.get(u, (u, root_alg, False))[1]
            flags |= unit_flags(alg, k, node_by_id(g, u).get("layoutOptions", {}) or {})
            parts.append(f"{u}[{alg}]:{'+'.join(sorted(k))}")
        flagsets[key] = flags if flags else {"Z"}
        classes[key] = "+".join(sorted(flagsets[key]))
        origins_txt[key] = " ".join(parts) if parts else "-"
        class_rows.append((r["set"], r["input"], classes[key], origins_txt[key], r.get("rs_vs_lean", "")))

    with open(tsv, "w", encoding="utf-8") as f:
        f.write("set\tinput\tclass\torigins\trs_vs_lean\n")
        for c in class_rows:
            f.write("\t".join(c) + "\n")

    total = len(pop)
    mism = [k for k in feats if k in classes]
    n_mis = len(mism)
    base = n_mis / total if total else 0.0
    lines = []
    w = lines.append
    w("# Random-graph ELK Java parity: mismatch classification")
    w("")
    w(f"Population: inputs both ELK Java and elk-lean laid out: **{total}**; not exactly equal (tol 0): "
      f"**{n_mis}** ({fmt_pct(n_mis, total)}). Generated by `scripts/classify_random_parity.py`.")
    w("")
    by_set = collections.defaultdict(lambda: [0, 0])
    for k in feats:
        by_set[k[0][0]][0] += 1
        if k in classes:
            by_set[k[0][0]][1] += 1
    w("| set kind | both ok | mismatched | rate |")
    w("|---|---:|---:|---:|")
    for s, (a, b) in sorted(by_set.items()):
        w(f"| {s} | {a} | {b} | {fmt_pct(b, a)} |")
    w("")

    # classes
    w("## Classes (origin of the difference)")
    w("")
    w("Every difference is attributed to the deepest layout unit (one algorithm invocation) whose own "
      "results differ; each such origin gets a flag. An input counts once under every flag it has "
      "(`T` = equal within 1e-6). `rs=lean`: elk-rs produced the same layout as elk-lean (1e-6), i.e. the "
      "difference is inherited from elk-rs.")
    w("")
    kinds_present = sorted({k[0][0] for k in feats})
    w("| flag | meaning | inputs | share of mismatches | rs=lean | " + " | ".join(f"set {x}" for x in kinds_present) + " |")
    w("|---|---|---:|---:|---:|" + "---:|" * len(kinds_present))
    per_kind = collections.Counter()
    for k, fs in flagsets.items():
        for h in {flag_head(f) for f in fs}:
            per_kind[(h, k[0][0])] += 1
    rowmap = {(r["set"], r["input"]): r for r in pop}
    heads = collections.Counter()
    heads_rs = collections.Counter()
    full = collections.Counter()
    full_rs = collections.Counter()
    for k, fs in flagsets.items():
        same = rowmap[k].get("rs_vs_lean") == "same"
        for h in {flag_head(f) for f in fs}:
            heads[h] += 1
            heads_rs[h] += same
        for f in fs:
            full[f] += 1
            full_rs[f] += same
    for h, n in heads.most_common():
        w(f"| {h} | {FLAG_TEXT.get(h, {'T': 'equal within 1e-6', 'Z': 'unattributed'}.get(h, ''))} | {n} | "
          f"{fmt_pct(n, n_mis)} | {heads_rs[h]} | " + " | ".join(str(per_kind[(h, x)]) for x in kinds_present) + " |")
    w("")
    w("Per flag and algorithm:")
    w("")
    per_kind_full = collections.Counter()
    for k, fs in flagsets.items():
        for f in fs:
            per_kind_full[(f, k[0][0])] += 1
    w("| flag | inputs | rs=lean | " + " | ".join(f"set {x}" for x in kinds_present) + " |")
    w("|---|---:|---:|" + "---:|" * len(kinds_present))
    for f, n in full.most_common():
        w(f"| {f} | {n} | {full_rs[f]} | " + " | ".join(str(per_kind_full[(f, x)]) for x in kinds_present) + " |")
    w("")
    cc = collections.Counter(classes.values())
    w("Most frequent flag combinations:")
    w("")
    w("| combination | inputs |")
    w("|---|---:|")
    for c, n in cc.most_common(15):
        w(f"| {c} | {n} |")
    w("")

    # root algorithm table
    w("## By root algorithm")
    w("")
    w("| root algorithm | both ok | mismatched | rate | lift |")
    w("|---|---:|---:|---:|---:|")
    alg_c = collections.defaultdict(lambda: [0, 0])
    for k, f in feats.items():
        a = next(x[4:] for x in f if x.startswith("alg="))
        alg_c[a][0] += 1
        alg_c[a][1] += k in classes
    for a, (t, m) in sorted(alg_c.items(), key=lambda kv: -kv[1][1]):
        w(f"| {a} | {t} | {m} | {fmt_pct(m, t)} | {(m / t / base) if t and base else 0:.2f} |")
    w("")
    w("## By child algorithms (inputs with compound nodes)")
    w("")
    w("| root / child algorithms | both ok | mismatched | rate | lift |")
    w("|---|---:|---:|---:|---:|")
    ch_c = collections.defaultdict(lambda: [0, 0])
    for k, f in feats.items():
        if "compound" not in f:
            continue
        a = next(x[4:] for x in f if x.startswith("alg="))
        ch = ",".join(sorted(x[9:] for x in f if x.startswith("childalg=")))
        ch_c[f"{a} / {ch}"][0] += 1
        ch_c[f"{a} / {ch}"][1] += k in classes
    for a, (t, m) in sorted(ch_c.items(), key=lambda kv: -kv[1][1])[:25]:
        w(f"| {a} | {t} | {m} | {fmt_pct(m, t)} | {(m / t / base) if t and base else 0:.2f} |")
    w("")

    # feature lift
    fc = collections.Counter()
    fm = collections.Counter()
    for k, f in feats.items():
        for x in f:
            fc[x] += 1
            if k in classes:
                fm[x] += 1
    def feature_table(title, keys, note):
        tot = len(keys)
        mis = sum(1 for k in keys if k in classes)
        rate = mis / tot if tot else 0.0
        c_all, c_mis = collections.Counter(), collections.Counter()
        for k in keys:
            for x in feats[k]:
                c_all[x] += 1
                c_mis[x] += k in classes
        w(f"## {title}")
        w("")
        w(f"{note} {tot} inputs, {mis} mismatched ({fmt_pct(mis, tot)}). Lift = mismatch rate with the feature / "
          f"rate of this population; support >= {args.min_support}; the 20 highest and the 10 lowest lifts.")
        w("")
        w("| feature | inputs | mismatched | rate | lift |")
        w("|---|---:|---:|---:|---:|")
        items = sorted(((x, c_all[x], c_mis[x]) for x in c_all if c_all[x] >= args.min_support),
                       key=lambda it: (-(it[2] / it[1]), -it[1]))
        shown = items if len(items) <= 30 else items[:20] + items[-10:]
        for x, t, m in shown:
            w(f"| `{x}` | {t} | {m} | {fmt_pct(m, t)} | {(m / t / rate) if rate else 0:.2f} |")
        w("")

    feature_table("Features (all inputs both sides laid out)", list(feats),
                  "Options present anywhere in the input; the generator sets most of them somewhere in most "
                  "graphs, so lifts near 1 carry little information.")
    layered_only = [k for k, f in feats.items()
                    if "alg=layered" in f and all(x.startswith("childalg=layered") for x in f if x.startswith("childalg="))]
    feature_table("Features of the layered-only inputs", layered_only,
                  "Inputs whose every layout unit is layered (no node micro layout of another algorithm):")

    # per flag detail
    w("## Flag details")
    w("")
    for flag, n in full.most_common():
        if n < 3:
            continue
        keys = [k for k in mism if flag in flagsets[k]]
        w(f"### {flag} ({n})")
        w("")
        kc = collections.Counter()
        for k in keys:
            for x in feats[k]:
                kc[x] += 1
        lifted = []
        for x, m in kc.items():
            t = fc[x]
            if t >= args.min_support and m >= 3:
                lifted.append(((m / n) / (t / total), x, m, t))
        lifted.sort(reverse=True)
        if lifted:
            w("Features over-represented under the flag (share under the flag / share in the population):")
            w("")
            for lift, x, m, t in lifted[:8]:
                w(f"- `{x}`: {m}/{n} vs {t}/{total} overall (x{lift:.2f})")
            w("")
        oc = collections.Counter()
        alg = flag.split(":", 1)[1] if ":" in flag else None
        for k in keys:
            for part in origins_txt[k].split():
                if "]:" in part and (alg is None or f"[{alg}]" in part):
                    oc[part.split("]:", 1)[1]] += 1
        if oc:
            w("Difference kinds at the origins: " + ", ".join(f"`{a_}` {b_}" for a_, b_ in oc.most_common(8)))
            w("")
        w("Examples:")
        w("")
        for k in sorted(keys)[: args.examples]:
            r = rowmap[k]
            w(f"- `{k[0]}/{k[1]}` origins `{origins_txt[k][:160]}`; first diff `{r.get('first_diff', '')[:120]}`")
        w("")
    with open(out, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    print(f"classified {n_mis} mismatches of {total} -> {out}")


if __name__ == "__main__":
    main()
