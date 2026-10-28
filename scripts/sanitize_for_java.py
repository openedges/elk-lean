#!/usr/bin/env python3
"""Makes `gen_nodesize_graphs.py` inputs acceptable to ELK Java's node size calculator ("v" sets).

    python3 -I scripts/sanitize_for_java.py <in_dir> <out_dir> [--explicit-defaults]

ELK Java 0.12.0 validates the inputs of `NodeLabelAndSizeCalculator` (used by layered's
`LabelAndNodeSizeProcessor` and by `NodeMicroLayout` of the other algorithms); elk-lean and elk-rs do
not port that validation (`docs/robustness-random-graphs.md` 7.1). About 80% of the generated graphs
fail it in Java, so the random parity runs a sanitised copy of every graph next to the generated one.
Only these changes are made, everything else (and the JSON key order) is kept:

1. A port without `elk.port.side` gets a side chosen from its id (`zlib.crc32(id) % 4` over
   NORTH, SOUTH, EAST, WEST). Java: `PortContextCreator.createPortContexts` throws
   `IllegalArgumentException: Label and node size calculator can only be used with ports that have
   port sides assigned.`, and the port comparator of `FIXED_ORDER` nodes throws
   `IllegalStateException: Port side is undefined`.
2. A port label placement (node or port level) with more than one of `ALWAYS_SAME_SIDE`,
   `ALWAYS_OTHER_SAME_SIDE`, `SPACE_EFFICIENT` loses `SPACE_EFFICIENT` (Java
   `PortLabelPlacement.isValid` -> `UnsupportedConfigurationException: Invalid port label placement`).
3. The deprecated size option `SPACE_EFFICIENT_PORT_LABELS` is dropped from `elk.nodeSize.options`
   where the placement has `ALWAYS_SAME_SIDE`/`ALWAYS_OTHER_SAME_SIDE` (`DeprecatedLayoutOptionReplacer`
   turns it into `SPACE_EFFICIENT`, which would make the placement invalid again); the option key is
   removed when nothing is left.

Every node and port ends up with a `layoutOptions` object (possibly empty), as in agent HX's sets.

`--explicit-defaults` ("d" sets, an experiment): additionally writes ELK Java's algorithm specific
option defaults (`supports <option> = <value>` in the algorithm's `.melk`, which Java reads through
the redeclared `<Algorithm>Options` property constants) onto every node with children whose own
`elk.algorithm` is one of `ALGORITHM_DEFAULTS`, where the option is not set. Both sides then see the
same values, so the drop of the mismatches against the "v" set measures how much of the difference
comes from defaults elk-lean (like elk-rs) does not apply.
"""
import json
import os
import sys
import zlib

SIDES = ["NORTH", "SOUTH", "EAST", "WEST"]
EXCLUSIVE = {"ALWAYS_SAME_SIDE", "ALWAYS_OTHER_SAME_SIDE", "SPACE_EFFICIENT"}


def _pad(p):
    return f"[top={p},left={p},bottom={p},right={p}]"


# ELK 0.12.0 .melk `supports` defaults that differ from the CoreOptions defaults (padding 12,
# spacing.nodeNode 20, spacing.edgeNode 10, spacing.edgeLabel 2)
ALGORITHM_DEFAULTS = {
    "box": {"elk.padding": _pad(15), "elk.spacing.nodeNode": "15", "elk.aspectRatio": "1.3"},
    "fixed": {"elk.padding": _pad(15)},
    "force": {"elk.padding": _pad(50), "elk.spacing.nodeNode": "80", "elk.spacing.edgeLabel": "5",
              "elk.aspectRatio": "1.6"},
    "mrtree": {"elk.padding": _pad(20), "elk.spacing.nodeNode": "20", "elk.spacing.edgeNode": "3",
               "elk.aspectRatio": "1.6"},
    "rectpacking": {"elk.padding": _pad(15), "elk.spacing.nodeNode": "15", "elk.aspectRatio": "1.3"},
}


def add_defaults(node):
    if node.get("children"):
        lo = node.setdefault("layoutOptions", {})
        alg = str(lo.get("elk.algorithm", "layered"))
        alg = alg[len("org.eclipse.elk."):] if alg.startswith("org.eclipse.elk.") else alg
        for k, v in ALGORITHM_DEFAULTS.get(alg, {}).items():
            if k not in lo and k[4:] not in lo:
                lo[k] = v
    for child in node.get("children", []):
        add_defaults(child)


def fix_placement(lo):
    placement = lo.get("elk.portLabels.placement")
    options = lo.get("elk.nodeSize.options", "").split()
    parts = placement.split() if placement else []
    if "SPACE_EFFICIENT_PORT_LABELS" in options and (
            "ALWAYS_SAME_SIDE" in parts or "ALWAYS_OTHER_SAME_SIDE" in parts):
        options = [o for o in options if o != "SPACE_EFFICIENT_PORT_LABELS"]
        if options:
            lo["elk.nodeSize.options"] = " ".join(options)
        else:
            lo.pop("elk.nodeSize.options", None)
    if len([x for x in parts if x in EXCLUSIVE]) > 1:
        parts = [x for x in parts if x != "SPACE_EFFICIENT"]
        lo["elk.portLabels.placement"] = " ".join(parts)


def walk(node):
    fix_placement(node.setdefault("layoutOptions", {}))
    for port in node.get("ports", []):
        lo = port.setdefault("layoutOptions", {})
        if "elk.port.side" not in lo:
            lo["elk.port.side"] = SIDES[zlib.crc32(port["id"].encode()) % 4]
        fix_placement(lo)
    for child in node.get("children", []):
        walk(child)


def main():
    args = [a for a in sys.argv[1:] if a != "--explicit-defaults"]
    explicit = len(args) != len(sys.argv) - 1
    if len(args) != 2:
        sys.exit(__doc__)
    src, dst = args
    os.makedirs(dst, exist_ok=True)
    n = 0
    for name in sorted(os.listdir(src)):
        if name.endswith(".json"):
            with open(os.path.join(src, name), encoding="utf-8") as f:
                graph = json.load(f)
            walk(graph)
            if explicit:
                add_defaults(graph)
            with open(os.path.join(dst, name), "w", encoding="utf-8") as f:
                json.dump(graph, f, indent=1)
            n += 1
    print(f"sanitised {n} graphs into {dst}")


if __name__ == "__main__":
    main()
