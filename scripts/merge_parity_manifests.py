#!/usr/bin/env python3
"""Merge the oracle (elk-rs) and elk-lean batch manifests into the manifest
`compare_model_parity_layouts.py` expects: the oracle fills the "java" columns,
elk-lean fills the "rust" columns.

Usage: merge_parity_manifests.py <oracle_manifest.tsv> <lean_manifest.tsv> <out.tsv>
"""
import csv
import sys


def read(path):
    with open(path, encoding="utf-8") as fh:
        rows = list(csv.DictReader(fh, delimiter="\t"))
    return {r["model_rel_path"]: r for r in rows}


def main() -> int:
    oracle = read(sys.argv[1])
    lean = read(sys.argv[2])
    cols = ["model_rel_path", "input_json", "java_layout_json", "java_status", "java_error",
            "rust_layout_json", "rust_status", "rust_error"]
    with open(sys.argv[3], "w", encoding="utf-8", newline="") as fh:
        w = csv.writer(fh, delimiter="\t", lineterminator="\n")
        w.writerow(cols)
        for rel in sorted(set(oracle) | set(lean)):
            o = oracle.get(rel, {})
            l = lean.get(rel, {})
            w.writerow([
                rel,
                o.get("input_json") or l.get("input_json", ""),
                o.get("rust_layout_json", ""),
                o.get("rust_status", "missing"),
                o.get("rust_error", ""),
                l.get("rust_layout_json", ""),
                l.get("rust_status", "missing"),
                l.get("rust_error", ""),
            ])
    print(f"merged manifest: {sys.argv[3]} ({len(set(oracle) | set(lean))} rows)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
