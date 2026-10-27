#!/usr/bin/env python3
"""Build a parity input manifest (elk-rs Java manifest format) from the corpus.

Usage: make_json_manifest.py <models_dir> <out_manifest.tsv> [--limit N] [--filter S]
                             [--include-elkt --elk-bin BIN --elkt-cache DIR]

Rows: model_rel_path, input_json (absolute), java_layout_json (empty), java_status (ok), java_error.
`.json` models are listed directly. With `--include-elkt`, `.elkt` models are converted to JSON
with `elk convert` (no defaults applied, like the Java EMF export) into `--elkt-cache` and the
converted file is listed as the input; a failed conversion is listed with `java_status = error`
so both runners skip it. `.elkg` (XMI) models are not supported yet.
"""
import argparse
import os
import subprocess
import sys


def convert_elkt(elk_bin: str, src: str, dst: str) -> str:
    """Converts `src` to `dst` unless the cached file is newer; returns an error message or ''."""
    if os.path.exists(dst) and os.path.getmtime(dst) >= os.path.getmtime(src):
        return ""
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    proc = subprocess.run([elk_bin, "convert", src, "-o", dst], capture_output=True, text=True)
    if proc.returncode != 0:
        if os.path.exists(dst):
            os.remove(dst)
        msg = (proc.stderr or proc.stdout).strip().splitlines()
        return (msg[0] if msg else f"elk convert exit {proc.returncode}").replace("\t", " ")
    return ""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("models_dir")
    ap.add_argument("out_manifest")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--filter", default="", help="substring filter on the relative path")
    ap.add_argument("--include-elkt", action="store_true", help="also list .elkt models (converted with elk convert)")
    ap.add_argument("--elk-bin", default=".lake/build/bin/elk")
    ap.add_argument("--elkt-cache", default="", help="directory for the converted .elkt models")
    args = ap.parse_args()
    root = os.path.abspath(args.models_dir)
    rows = []
    for dirpath, _dirs, files in os.walk(root):
        for name in sorted(files):
            if name.endswith(".json"):
                kind = "json"
            elif args.include_elkt and name.endswith(".elkt"):
                kind = "elkt"
            else:
                continue
            full = os.path.join(dirpath, name)
            rel = os.path.relpath(full, root)
            if args.filter and args.filter not in rel:
                continue
            rows.append((rel, full, kind))
    rows.sort()
    if args.limit:
        rows = rows[: args.limit]
    cache = os.path.abspath(args.elkt_cache) if args.elkt_cache else os.path.abspath("tests/tmp/elkt_json")
    out_rows = []
    failed = 0
    for rel, full, kind in rows:
        if kind == "json":
            out_rows.append((rel, full, "ok", ""))
        else:
            dst = os.path.join(cache, rel + ".json")
            err = convert_elkt(os.path.abspath(args.elk_bin), full, dst)
            if err:
                failed += 1
                out_rows.append((rel, dst, "error", err))
            else:
                out_rows.append((rel, dst, "ok", ""))
    os.makedirs(os.path.dirname(os.path.abspath(args.out_manifest)) or ".", exist_ok=True)
    with open(args.out_manifest, "w", encoding="utf-8") as fh:
        fh.write("model_rel_path\tinput_json\tjava_layout_json\tjava_status\tjava_error\n")
        for rel, full, status, err in out_rows:
            fh.write(f"{rel}\t{full}\t\t{status}\t{err}\n")
    print(f"manifest: {args.out_manifest} ({len(out_rows)} models, {failed} conversion failures)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
