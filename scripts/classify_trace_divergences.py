#!/usr/bin/env python3
"""Classifies the diverged models of a Java phase-step trace run by their first difference.

    python3 scripts/classify_trace_divergences.py <java_trace_out_dir>   # from run_java_trace_parity.sh

Classes: `java-nonfinite` (the Java snapshot holds a non-finite coordinate — ELK's zero-size resize
defect leaves NaN port coordinates that later processors overwrite), `selfloop-order` and
`partition-order` (Java iterates HashMap/HashSet keyed by identity hash codes, so its order is
run-dependent), `other:<Processor>`. Writes <dir>/divergence_classes.json.
"""
import collections
import json
import os
import re
import subprocess
import sys


def main():
    d = sys.argv[1]
    here = os.path.dirname(os.path.abspath(__file__))
    rep = json.load(open(os.path.join(d, "trace_report.json")))
    cats = collections.Counter()
    classes = {}
    for r in rep["models"]:
        if r.get("first_divergence_step") is None:
            continue
        m = r["model"]
        out = subprocess.run([sys.executable, os.path.join(here, "compare_phase_traces.py"), "--strict-order",
                              "--tolerance", "0", "--stop-at-first",
                              os.path.join(d, "java", "trace", m), os.path.join(d, "lean_trace", m)],
                             capture_output=True, text=True).stdout
        block = out[out.find("DRIFT"):]
        diffs = [l.strip() for l in block.split("\n")[1:] if l.startswith("  ") and ":" in l][:8]
        proc = r["first_divergence_processor"]
        if any(re.search(r"valid trace field required|\bnan\b|\binf\b|NaN|Infinity", x) for x in diffs):
            cat = "java-nonfinite"
        elif proc == "SelfLoopRouter":
            cat = "selfloop-order"
        elif proc == "PartitionMidprocessor":
            cat = "partition-order"
        else:
            cat = f"other:{proc}"
        cats[cat] += 1
        classes.setdefault(cat, []).append({"model": m, "step": r["first_divergence_step"], "processor": proc,
                                            "first_diffs": diffs[:3]})
    json.dump(classes, open(os.path.join(d, "divergence_classes.json"), "w"), indent=1)
    print("diverged:", sum(cats.values()), dict(cats))
    for cat, items in classes.items():
        print(f"== {cat}: {len(items)}")
        for it in items[:2]:
            print(f"   {it['model']} step {it['step']} {it['processor']}: {'; '.join(it['first_diffs'])[:160]}")


if __name__ == "__main__":
    main()
