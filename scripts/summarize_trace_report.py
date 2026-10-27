#!/usr/bin/env python3
"""Summarize a `compare_phase_traces.py --batch --json` report into Markdown.

Usage: summarize_trace_report.py <trace_report.json> <lean.tsv> <out.md> [--list N]
"""
import collections
import json
import sys


def main() -> int:
    args = sys.argv[1:]
    list_n = 40
    if "--list" in args:
        i = args.index("--list")
        list_n = int(args[i + 1])
        del args[i : i + 2]
    report_path, lean_tsv, out_md = args[:3]
    try:
        with open(report_path, encoding="utf-8") as fh:
            report = json.load(fh)
    except (OSError, ValueError) as exc:
        report = {"models": [], "error": str(exc)}
    models = report.get("models", [])
    lean_status = {}
    lean_error = collections.Counter()
    try:
        with open(lean_tsv, encoding="utf-8") as fh:
            header = fh.readline().rstrip("\n").split("\t")
            for line in fh:
                cols = line.rstrip("\n").split("\t")
                if len(cols) < len(header):
                    continue
                row = dict(zip(header, cols))
                lean_status[row["model_rel_path"]] = row.get("rust_status", "")
                if row.get("rust_status") != "ok":
                    lean_error[row.get("rust_error", "")[:90]] += 1
    except OSError:
        pass
    total = len(models)
    matched = [m for m in models if m.get("first_divergence_step") is None and m.get("rust_steps", 0) > 0
               and m.get("java_steps") == m.get("rust_steps")]
    diverged = [m for m in models if m.get("first_divergence_step") is not None]
    missing_lean = [m for m in models if not m.get("rust_steps")]
    step_mismatch = [m for m in models if m.get("first_divergence_step") is None and m.get("rust_steps")
                     and m.get("java_steps") != m.get("rust_steps")]
    histogram = collections.Counter(m.get("first_divergence_processor") or "?" for m in diverged)
    lines = ["# Phase-step trace parity", "",
             f"- models compared: {total}",
             f"- full match (all steps, same step count): {len(matched)}",
             f"- diverged: {len(diverged)}",
             f"- same steps but different step count (oracle vs lean): {len(step_mismatch)}",
             f"- no lean trace (layout error or unsupported): {len(missing_lean)}",
             f"- lean batch statuses: " + ", ".join(f"{k}={v}" for k, v in collections.Counter(lean_status.values()).items()),
             ""]
    if lean_error:
        lines.append("## elk-lean errors (top)")
        for msg, n in lean_error.most_common(8):
            lines.append(f"- {n} × `{msg}`")
        lines.append("")
    if histogram:
        lines.append("## First divergent processor (histogram)")
        for proc, n in histogram.most_common():
            lines.append(f"- {proc}: {n}")
        lines.append("")
    if diverged:
        lines.append(f"## Diverged models (first {list_n})")
        for m in sorted(diverged, key=lambda m: (m.get('first_divergence_step') or 0, m.get('model', '')))[:list_n]:
            lines.append(f"- {m.get('model')}: step {m.get('first_divergence_step')} {m.get('first_divergence_processor')}"
                         f" (oracle {m.get('java_steps')} / lean {m.get('rust_steps')} steps)")
        lines.append("")
    if step_mismatch:
        lines.append(f"## Step-count mismatches (first {list_n})")
        for m in step_mismatch[:list_n]:
            lines.append(f"- {m.get('model')}: oracle {m.get('java_steps')} / lean {m.get('rust_steps')} steps")
        lines.append("")
    import os
    trace_root = os.path.join(os.path.dirname(os.path.abspath(report_path)), "lean_trace")
    unported = collections.Counter()
    for dirpath, _dirs, files in os.walk(trace_root):
        for name in files:
            if "_Unported_" in name:
                unported[name.split("_Unported_", 1)[1].rsplit(".json", 1)[0]] += 1
    if unported:
        lines.append("## Unported stand-ins hit by elk-lean (`ELK_LEAN_SKIP_UNPORTED`)")
        for name, n in unported.most_common():
            lines.append(f"- {name}: {n} runs")
        lines.append("")
    with open(out_md, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
