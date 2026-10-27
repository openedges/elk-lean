#!/usr/bin/env python3
"""Build a parity input manifest (elk-rs Java manifest format) from the corpus.

Usage: make_json_manifest.py <models_dir> <out_manifest.tsv> [--glob '*.json'] [--limit N]

Rows: model_rel_path, input_json (absolute), java_layout_json (empty), java_status (ok), java_error.
Only `.json` models are listed until the `.elkt` converter exists (PLAN.md Phase 6).
"""
import argparse
import os
import sys


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("models_dir")
    ap.add_argument("out_manifest")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--filter", default="", help="substring filter on the relative path")
    args = ap.parse_args()
    root = os.path.abspath(args.models_dir)
    rows = []
    for dirpath, _dirs, files in os.walk(root):
        for name in sorted(files):
            if not name.endswith(".json"):
                continue
            full = os.path.join(dirpath, name)
            rel = os.path.relpath(full, root)
            if args.filter and args.filter not in rel:
                continue
            rows.append((rel, full))
    rows.sort()
    if args.limit:
        rows = rows[: args.limit]
    os.makedirs(os.path.dirname(os.path.abspath(args.out_manifest)) or ".", exist_ok=True)
    with open(args.out_manifest, "w", encoding="utf-8") as fh:
        fh.write("model_rel_path\tinput_json\tjava_layout_json\tjava_status\tjava_error\n")
        for rel, full in rows:
            fh.write(f"{rel}\t{full}\t\tok\t\n")
    print(f"manifest: {args.out_manifest} ({len(rows)} models)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
