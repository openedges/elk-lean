#!/usr/bin/env python3
"""Checks elk-lean outputs against the set of outcomes ELK Java produced in several JVM contexts.

ELK Java's result for some models depends on identity hash codes (iteration order of HashMap/HashSet
keyed by objects without hashCode), i.e. on what ran before in the JVM. For such models the
reference is the set of outputs observed over several runs (forward, reverse, shuffled corpus runs
and a single-model run); elk-lean must reproduce one of them.

    python3 scripts/java_outcomes.py --models varying.txt --lean-dir out/lean \\
        --run forward=.reference/java-baseline/corpus/java_manifest.tsv \\
        --run reverse=.reference/java-baseline/corpus_reverse/java_manifest.tsv \\
        [--run s11=.../java_manifest.tsv ...] [--singles-dir DIR --singles-placeholder PATH]

`--singles-dir` holds one copied baseline directory per model (named with `/` replaced by `_`); the
manifests inside still mention the directory they were produced in (`--singles-placeholder`), which
is remapped. Numbers are compared by value (Gson `12.0` equals `12`); `NaN`/`Infinity` tokens of
Gson are accepted.
"""
import argparse
import csv
import json
import math
import os
import sys


def load_manifest(path, remap=None):
    if not os.path.exists(path):
        return {}
    rows = {}
    with open(path, encoding="utf-8") as f:
        for r in csv.DictReader(f, delimiter="\t"):
            if remap:
                r = {k: (v.replace(remap[0], remap[1]) if isinstance(v, str) else v) for k, v in r.items()}
            rows[r["model_rel_path"]] = r
    return rows


def canon(x):
    if isinstance(x, dict):
        return {k: canon(v) for k, v in x.items()}
    if isinstance(x, list):
        return [canon(v) for v in x]
    if isinstance(x, bool):
        return x
    if isinstance(x, (int, float)):
        if isinstance(x, float) and math.isnan(x):
            return "NaN"
        if isinstance(x, float) and math.isinf(x):
            return "Inf" if x > 0 else "-Inf"
        return float(x)
    return x


def load_json(path):
    txt = open(path, encoding="utf-8").read()
    try:
        return canon(json.loads(txt))
    except ValueError:
        txt = txt.replace("-Infinity", '"-Inf"').replace("Infinity", '"Inf"').replace("NaN", '"NaN"')
        return canon(json.loads(txt))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--models", required=True, help="file with one model_rel_path per line")
    ap.add_argument("--lean-dir", required=True, help="elk batch --layout-dir of the same inputs")
    ap.add_argument("--run", action="append", default=[], help="name=java_manifest.tsv (repeatable)")
    ap.add_argument("--singles-dir")
    ap.add_argument("--singles-placeholder")
    a = ap.parse_args()
    models = [l.strip() for l in open(a.models) if l.strip()]
    runs = {}
    for spec in a.run:
        name, path = spec.split("=", 1)
        runs[name] = load_manifest(path)
    in_set = 0
    not_in = []
    hist = {}
    for m in models:
        outs = {}
        for name, man in runs.items():
            r = man.get(m)
            if r and r["java_status"] == "ok":
                outs[name] = load_json(r["java_layout_json"])
        if a.singles_dir:
            sd = os.path.join(a.singles_dir, m.replace("/", "_"))
            remap = (a.singles_placeholder, sd) if a.singles_placeholder else None
            sm = load_manifest(os.path.join(sd, "java_manifest.tsv"), remap)
            if m in sm and sm[m]["java_status"] == "ok":
                outs["single"] = load_json(sm[m]["java_layout_json"])
        distinct = []
        for v in outs.values():
            if not any(v == d for d in distinct):
                distinct.append(v)
        hist[len(distinct)] = hist.get(len(distinct), 0) + 1
        lp = os.path.join(a.lean_dir, m + ".json")
        if not os.path.exists(lp):
            not_in.append((m, "no elk-lean output"))
            continue
        lean = load_json(lp)
        if any(lean == d for d in distinct):
            in_set += 1
        else:
            not_in.append((m, f"{len(distinct)} distinct Java outputs over {len(outs)} runs"))
    print(f"models: {len(models)} | elk-lean equals an observed Java outcome: {in_set} | not: {len(not_in)}")
    print("distinct Java outputs per model:", dict(sorted(hist.items())))
    for m, why in not_in:
        print(f"  NOT: {m} - {why}")
    return 1 if not_in else 0


if __name__ == "__main__":
    sys.exit(main())
