#!/usr/bin/env python3
"""Performance report: elk-lean (`lean_api`) against the elk-rs oracle (`rust_api`, `rust_native`).

Reads every `<results_dir>/*.csv` in the elk-rs `perf_benchmark` format
(`timestamp,engine,scenario,iterations,warmup,elapsed_nanos,avg_ms,ops_per_sec`; the last row per
engine/scenario wins), writes a markdown report with per-scenario times and the lean/rust ratio and,
with `--baseline CSV`, applies the 5% regression gate of AGENTS.md to the lean_api rows
(exit code 1 when a scenario got slower than `--threshold`).

    python3 scripts/compare_perf.py tests/perf tests/perf/report.md [--baseline B.csv] [--threshold 0.05]
"""
import argparse
import csv
import math
import platform
import subprocess
import sys
from pathlib import Path

ORDER = [
    "layered_small", "layered_medium", "layered_large", "layered_xlarge",
    "force_medium", "force_large", "force_xlarge",
    "stress_medium", "stress_large", "stress_xlarge",
    "mrtree_medium", "mrtree_large", "mrtree_xlarge",
    "radial_medium", "radial_large", "radial_xlarge",
    "rectpacking_medium", "rectpacking_large", "rectpacking_xlarge",
    "routing_polyline", "routing_orthogonal", "routing_splines",
    "crossmin_layer_sweep", "crossmin_none", "hierarchy_flat", "hierarchy_nested",
]


def load(path: Path) -> dict:
    rows = {}
    with path.open(encoding="utf-8") as f:
        for r in csv.DictReader(f):
            try:
                rows[(r["engine"], r["scenario"])] = float(r["avg_ms"])
            except (KeyError, ValueError):
                continue
    return rows


def machine() -> str:
    def sysctl(key):
        try:
            return subprocess.run(["sysctl", "-n", key], capture_output=True, text=True, check=True).stdout.strip()
        except Exception:
            return "?"
    if platform.system() == "Darwin":
        mem = sysctl("hw.memsize")
        mem = f"{int(mem) / 2**30:.0f} GiB" if mem.isdigit() else mem
        return f"{sysctl('machdep.cpu.brand_string')}, {sysctl('hw.ncpu')} cores, {mem}, macOS {platform.mac_ver()[0]}"
    return f"{platform.processor() or platform.machine()}, {platform.system()} {platform.release()}"


def geomean(xs):
    xs = [x for x in xs if x > 0]
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else float("nan")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("results_dir")
    ap.add_argument("output")
    ap.add_argument("--baseline")
    ap.add_argument("--threshold", type=float, default=0.05)
    a = ap.parse_args()
    data = {}
    for p in sorted(Path(a.results_dir).glob("*.csv")):
        if p.name.startswith("baseline"):
            continue
        data.update(load(p))
    engines = [e for e in ["rust_native", "rust_api", "lean_api"] if any(k[0] == e for k in data)]
    scenarios = [s for s in ORDER if any(k[1] == s for k in data)]
    scenarios += sorted({k[1] for k in data} - set(scenarios))
    base = load(Path(a.baseline)) if a.baseline else {}
    lines = ["# Performance report", "", f"- machine: {machine()}", f"- engines: {', '.join(engines)}", ""]
    hdr = "| scenario | " + " | ".join(f"{e} ms" for e in engines) + " | lean/rust_api |"
    if base:
        hdr += " lean vs baseline |"
    lines += [hdr, "|" + "---|" * (len(engines) + 2 + (1 if base else 0))]
    ratios, regressions = [], []
    for s in scenarios:
        cells = [f"{data[(e, s)]:.3f}" if (e, s) in data else "-" for e in engines]
        lean, rust = data.get(("lean_api", s)), data.get(("rust_api", s))
        ratio = lean / rust if lean and rust else None
        if ratio:
            ratios.append(ratio)
        row = f"| {s} | " + " | ".join(cells) + f" | {f'{ratio:.2f}x' if ratio else '-'} |"
        if base:
            b = base.get(("lean_api", s))
            if lean and b:
                change = lean / b - 1.0
                flag = " ⚠" if change > a.threshold else ""
                if change > a.threshold:
                    regressions.append((s, change))
                row += f" {change * 100:+.1f}%{flag} |"
            else:
                row += " - |"
        lines.append(row)
    lines += ["", f"- geometric mean lean/rust_api: {geomean(ratios):.2f}x over {len(ratios)} scenarios"]
    if base:
        if regressions:
            lines.append(f"- regression gate ({a.threshold * 100:.0f}%): FAIL — " +
                         ", ".join(f"{s} {c * 100:+.1f}%" for s, c in regressions))
        else:
            lines.append(f"- regression gate ({a.threshold * 100:.0f}%): pass")
    Path(a.output).parent.mkdir(parents=True, exist_ok=True)
    Path(a.output).write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    return 1 if regressions else 0


if __name__ == "__main__":
    sys.exit(main())
