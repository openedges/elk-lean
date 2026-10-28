#!/usr/bin/env python3
"""Random graphs that exercise the algorithm specific options of the non-layered algorithms ("o" sets
of `scripts/run_random_java_parity.sh`, agent OPT).

    python3 -I scripts/gen_option_graphs.py OUT_DIR COUNT [SEED]

`gen_nodesize_graphs.py` (the "s"/"v" sets) varies node size options and hierarchy but never sets an
algorithm's own options, so the option parsers and the strategy branches they select (force model,
stress dimension, radial compactor/sorter/wedge/translation, mrtree weighting/routing/search order,
rectangle packing strategies, VertiFlex strategy, SPOrE processing order, ...) are not covered there.
Here every graph is a single flat level (no ports, no hierarchy, plain node sizes, optional node
labels) laid out by one algorithm with a random subset of its options; about one graph in six sets
no option at all (the algorithm defaults). Trees are generated for the tree algorithms (radial, mrtree,
vertiflex), edgeless graphs for rectangle packing, arbitrary graphs otherwise. Values are written as
ELK Java parses them (enum constant names, decimal numbers).
"""
import json
import os
import random
import sys


def pick(rng, p=0.5):
    return rng.random() < p


def tree_edges(rng, n):
    edges = []
    for i in range(1, n):
        edges.append((rng.randrange(0, i), i))
    return edges


def any_edges(rng, n):
    edges = []
    for _ in range(rng.randint(0, 2 * n)):
        s, t = rng.randrange(n), rng.randrange(n)
        if s != t:
            edges.append((s, t))
    return edges


def opts_force(rng):
    lo = {}
    if pick(rng, 0.6):
        lo["elk.force.model"] = rng.choice(["EADES", "FRUCHTERMAN_REINGOLD"])
    if pick(rng, 0.3):
        lo["elk.force.iterations"] = str(rng.choice([1, 10, 50, 300]))
    if pick(rng, 0.3):
        lo["elk.force.repulsion"] = str(rng.choice([1.0, 2.5, 5.0, 10.0]))
    if pick(rng, 0.3):
        lo["elk.force.temperature"] = str(rng.choice([0.0005, 0.001, 0.01]))
    if pick(rng, 0.3):
        lo["elk.randomSeed"] = str(rng.choice([1, 2, 7, 42]))
    if pick(rng, 0.2):
        lo["elk.spacing.nodeNode"] = str(rng.choice([10, 40, 80]))
    if pick(rng, 0.2):
        lo["elk.separateConnectedComponents"] = rng.choice(["true", "false"])
    if pick(rng, 0.2):
        lo["elk.aspectRatio"] = str(rng.choice([0.5, 1.0, 1.6, 3.0]))
    if pick(rng, 0.2):
        lo["elk.padding"] = "[top=%d,left=%d,bottom=%d,right=%d]" % tuple(rng.choice([0, 5, 20]) for _ in range(4))
    return lo


def opts_stress(rng):
    lo = {}
    if pick(rng, 0.6):
        lo["elk.stress.dimension"] = rng.choice(["XY", "X", "Y"])
    if pick(rng, 0.3):
        lo["elk.stress.desiredEdgeLength"] = str(rng.choice([20, 50, 100, 200]))
    if pick(rng, 0.2):
        lo["elk.stress.epsilon"] = str(rng.choice([0.1, 0.001, 0.0001]))
    if pick(rng, 0.2):
        lo["elk.stress.iterationLimit"] = str(rng.choice([1, 5, 50]))
    if pick(rng, 0.2):
        lo["elk.interactive"] = "true"
    if pick(rng, 0.2):
        lo["elk.force.model"] = rng.choice(["EADES", "FRUCHTERMAN_REINGOLD"])
    return lo


def opts_radial(rng):
    lo = {}
    if pick(rng, 0.4):
        lo["elk.radial.compactor"] = rng.choice(["NONE", "RADIAL_COMPACTION", "WEDGE_COMPACTION"])
    if pick(rng, 0.3):
        lo["elk.radial.compactionStepSize"] = str(rng.choice([1, 2, 5]))
    if pick(rng, 0.4):
        lo["elk.radial.sorter"] = rng.choice(["NONE", "POLAR_COORDINATE", "ID"])
    if pick(rng, 0.4):
        lo["elk.radial.wedgeCriteria"] = rng.choice(["LEAF_NUMBER", "NODE_SIZE"])
    if pick(rng, 0.4):
        lo["elk.radial.optimizationCriteria"] = rng.choice(
            ["NONE", "EDGE_LENGTH", "EDGE_LENGTH_BY_POSITION", "CROSSING_MINIMIZATION_BY_POSITION"])
    if pick(rng, 0.3):
        lo["elk.radial.rotate"] = "true"
        if pick(rng, 0.5):
            lo["elk.radial.rotation.targetAngle"] = str(rng.choice([0.0, 0.5, 1.5, 3.0]))
        if pick(rng, 0.5):
            lo["elk.radial.rotation.computeAdditionalWedgeSpace"] = "true"
    if pick(rng, 0.2):
        lo["elk.radial.rotation.outgoingEdgeAngles"] = "true"
    if pick(rng, 0.2):
        lo["elk.radial.centerOnRoot"] = "true"
    if pick(rng, 0.2):
        lo["elk.radial.radius"] = str(rng.choice([20, 50, 100]))
    if pick(rng, 0.2):
        lo["elk.spacing.nodeNode"] = str(rng.choice([5, 20, 40]))
    return lo


def opts_mrtree(rng):
    lo = {}
    if pick(rng, 0.4):
        lo["elk.mrtree.weighting"] = rng.choice(["MODEL_ORDER", "DESCENDANTS", "FAN", "CONSTRAINT"])
    if pick(rng, 0.4):
        lo["elk.mrtree.edgeRoutingMode"] = rng.choice(["NONE", "MIDDLE_TO_MIDDLE", "AVOID_OVERLAP"])
    if pick(rng, 0.4):
        lo["elk.mrtree.searchOrder"] = rng.choice(["DFS", "BFS"])
    if pick(rng, 0.3):
        lo["elk.mrtree.compaction"] = rng.choice(["true", "false"])
    if pick(rng, 0.3):
        lo["elk.direction"] = rng.choice(["RIGHT", "DOWN", "LEFT", "UP"])
    if pick(rng, 0.2):
        lo["elk.spacing.nodeNode"] = str(rng.choice([5, 20, 40]))
    if pick(rng, 0.2):
        lo["elk.spacing.edgeNode"] = str(rng.choice([1, 3, 10]))
    if pick(rng, 0.2):
        lo["elk.mrtree.edgeEndTextureLength"] = str(rng.choice([0, 7, 15]))
    return lo


def opts_rectpacking(rng):
    lo = {}
    if pick(rng, 0.4):
        lo["elk.rectpacking.widthApproximation.strategy"] = rng.choice(["GREEDY", "TARGET_WIDTH"])
        if lo["elk.rectpacking.widthApproximation.strategy"] == "TARGET_WIDTH" or pick(rng, 0.3):
            lo["elk.rectpacking.widthApproximation.targetWidth"] = str(rng.choice([50, 150, 400]))
    if pick(rng, 0.4):
        lo["elk.rectpacking.widthApproximation.optimizationGoal"] = rng.choice(
            ["ASPECT_RATIO_DRIVEN", "MAX_SCALE_DRIVEN", "AREA_DRIVEN"])
    if pick(rng, 0.4):
        lo["elk.rectpacking.packing.strategy"] = rng.choice(["COMPACTION", "SIMPLE", "NONE"])
    if pick(rng, 0.4):
        lo["elk.rectpacking.whiteSpaceElimination.strategy"] = rng.choice(
            ["EQUAL_BETWEEN_STRUCTURES", "TO_ASPECT_RATIO", "NONE"])
    if pick(rng, 0.2):
        lo["elk.rectpacking.trybox"] = "true"
    if pick(rng, 0.2):
        lo["elk.rectpacking.orderBySize"] = "true"
    if pick(rng, 0.2):
        lo["elk.aspectRatio"] = str(rng.choice([0.5, 1.3, 2.0]))
    if pick(rng, 0.2):
        lo["elk.spacing.nodeNode"] = str(rng.choice([0, 5, 15, 30]))
    return lo


def opts_vertiflex(rng):
    lo = {}
    if pick(rng, 0.6):
        lo["elk.vertiflex.layoutStrategy"] = rng.choice(["STRAIGHT", "BEND"])
    if pick(rng, 0.3):
        lo["elk.vertiflex.layerDistance"] = str(rng.choice([20, 50, 80]))
    if pick(rng, 0.3):
        lo["elk.vertiflex.considerNodeModelOrder"] = rng.choice(["true", "false"])
    if pick(rng, 0.2):
        lo["elk.spacing.nodeNode"] = str(rng.choice([5, 20, 40]))
    return lo


def opts_spore(rng):
    lo = {}
    if pick(rng, 0.4):
        lo["elk.processingOrder.treeConstruction"] = rng.choice(["MINIMUM_SPANNING_TREE", "MAXIMUM_SPANNING_TREE"])
    if pick(rng, 0.4):
        lo["elk.processingOrder.spanningTreeCostFunction"] = rng.choice(
            ["CENTER_DISTANCE", "CIRCLE_UNDERLAP", "RECTANGLE_UNDERLAP", "INVERTED_OVERLAP", "MINIMUM_ROOT_DISTANCE"])
    if pick(rng, 0.3):
        lo["elk.processingOrder.rootSelection"] = rng.choice(["FIXED", "CENTER_NODE"])
    if pick(rng, 0.2):
        lo["elk.compaction.orthogonal"] = "true"
    if pick(rng, 0.2):
        lo["elk.spacing.nodeNode"] = str(rng.choice([2, 8, 20]))
    return lo


ALGS = [
    ("force", opts_force, any_edges),
    ("stress", opts_stress, any_edges),
    ("radial", opts_radial, tree_edges),
    ("radial", opts_radial, tree_edges),
    ("mrtree", opts_mrtree, tree_edges),
    ("mrtree", opts_mrtree, any_edges),
    ("rectpacking", opts_rectpacking, lambda rng, n: []),
    ("vertiflex", opts_vertiflex, tree_edges),
    ("sporeCompaction", opts_spore, any_edges),
    ("sporeOverlap", opts_spore, any_edges),
]


def make_graph(rng):
    alg, opts, edges_of = rng.choice(ALGS)
    n = rng.randint(2, 12)
    lo = {"elk.algorithm": alg}
    if not pick(rng, 1 / 6):
        lo.update(opts(rng))
    children = []
    for i in range(n):
        node = {"id": f"n{i}", "width": round(rng.uniform(10, 60), 1), "height": round(rng.uniform(10, 40), 1)}
        if alg == "vertiflex" and pick(rng, 0.2):
            node["layoutOptions"] = {"elk.vertiflex.verticalConstraint": str(rng.choice([0, 50, 120]))}
        if alg == "radial" and lo.get("elk.radial.sorter") == "ID":
            node.setdefault("layoutOptions", {})["elk.radial.orderId"] = str(rng.randint(0, n))
        if alg == "mrtree" and lo.get("elk.mrtree.weighting") == "CONSTRAINT" and pick(rng, 0.5):
            node.setdefault("layoutOptions", {})["elk.mrtree.positionConstraint"] = str(rng.randint(-1, 3))
        if pick(rng, 0.2):
            node["labels"] = [{"id": f"n{i}l", "text": "l", "width": round(rng.uniform(5, 30), 1),
                               "height": round(rng.uniform(5, 15), 1)}]
        children.append(node)
    edges = [{"id": f"e{k}", "sources": [f"n{s}"], "targets": [f"n{t}"]}
             for k, (s, t) in enumerate(edges_of(rng, n))]
    g = {"id": "root", "layoutOptions": lo, "children": children}
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
        rng = random.Random(seed * 200003 + k)
        with open(os.path.join(out, f"g{k:04d}.json"), "w") as f:
            json.dump(make_graph(rng), f, indent=1)
    print(f"wrote {count} graphs to {out}")


if __name__ == "__main__":
    main()
