"""ELK Text loader parity: `elk convert` (Lean `.elkt` loader + JSON exporter) against ELK Java's own
JSON export of the same `.elkt` model (the `inputs/*.elkt.json` files that scripts/run_java_baseline.sh
writes after loading the model through EMF). Semantic comparison, tolerance 0, after normalising what
the two exporters print differently by design:
  * option keys: Lean's short keys (`elk.x`) become Java's full ids (`org.eclipse.x`), and the layered
    options, which elk-lean registers as `org.eclipse.elk.alg.layered.*` with the Java id
    `org.eclipse.elk.layered.*` as legacy id, are compared under the Java id;
  * numbers inside option strings: Java `10.0` / Lean `10` (both become `10`);
  * zero geometry: Java writes `x`/`y`/`width`/`height` = 0, Lean omits them (dropped on both sides);
  * generated ids of duplicate identifiers: Java `p_g123456`, Lean `p_g000000` (suffix dropped);
  * `org.eclipse.elk.randomSeed` on the root: set by the Java baseline driver, not by the model;
  * unresolved option keys (a key that is no option id, e.g. `spacing.labelPort`, `minimalNodeSize`):
    Java's text loader keeps them as `LayoutOptionProxy` and the baseline driver exports them with
    `omitUnknownLayoutOptions(false)`; ELK's JSON export omits them by default and so does
    `elk convert`, hence they are dropped from the Java side here. Unparsable values of known options
    (`edgeLabels.placement: UNDEFINED`) stay on both sides (proxy under the option id).
    python3 scripts/compare_elkt_conversion.py --java-manifest <java_manifest.tsv> --lean-dir <dir of elk convert outputs> \
        --report <report.md> --details <details.tsv> [--max-diffs-per-model N]
The lean dir holds `<model_rel_path>.json` for every `.elkt` row of the manifest (scripts/run_elkt_loader_parity.sh).
SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
"""
from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from compare_model_parity_layouts import compare_json  # noqa: E402

GENERATED_ID = re.compile(r"_g\d{6}\b")
TRAILING_ZERO = re.compile(r"(?<![\d.])(-?\d+)\.0(?![\d.])")
GEOMETRY = ("x", "y", "width", "height")


def normalize_string(s: str) -> str:
    return TRAILING_ZERO.sub(r"\1", GENERATED_ID.sub("", s))


def canonical_key(k: str) -> str:
    """Java's full option id for a key as `elk convert` (short keys) or ELK Java (full ids) writes it."""
    full = "org.eclipse." + k if k.startswith("elk.") else k
    if full.startswith("org.eclipse.elk.alg.layered."):
        full = "org.eclipse.elk.layered." + full[len("org.eclipse.elk.alg.layered."):]
    return full


def normalize(value, is_root: bool = False):
    if isinstance(value, dict):
        out = {}
        for key, item in value.items():
            if key in GEOMETRY and isinstance(item, (int, float)) and item == 0:
                continue
            if key in ("layoutOptions", "properties", "individualSpacings") and isinstance(item, dict):
                opts = {}
                for k, v in item.items():
                    full = canonical_key(k)
                    if is_root and full == "org.eclipse.elk.randomSeed":
                        continue
                    if not full.startswith("org.eclipse."):
                        continue  # an unresolved key kept by Java's proxy mechanism (see the module doc)
                    opts[full] = normalize_string(v) if isinstance(v, str) else normalize(v)
                if opts:
                    out["layoutOptions" if key == "properties" else key] = opts
                continue
            out[key] = normalize(item)
        return out
    if isinstance(value, list):
        return [normalize(v) for v in value]
    if isinstance(value, str):
        return normalize_string(value)
    return value


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--java-manifest", required=True)
    parser.add_argument("--lean-dir", required=True)
    parser.add_argument("--report", required=True)
    parser.add_argument("--details", required=True)
    parser.add_argument("--max-diffs-per-model", type=int, default=20)
    args = parser.parse_args()

    lean_dir = Path(args.lean_dir)
    rows = []
    with open(args.java_manifest, encoding="utf-8") as f:
        for row in csv.DictReader(f, delimiter="\t"):
            if row["model_rel_path"].lower().endswith(".elkt"):
                rows.append(row)
    total = len(rows)
    compared = identical = differing = skipped = 0
    details = []
    categories: dict[str, int] = {}
    for row in rows:
        rel = row["model_rel_path"]
        java_path = Path(row["input_json"])
        lean_path = lean_dir / (rel + ".json")
        if row["java_status"] != "ok" or not java_path.is_file() or not lean_path.is_file():
            skipped += 1
            details.append((rel, "skipped", 0, "", "java %s, lean %s" % (row["java_status"], "present" if lean_path.is_file() else "missing")))
            continue
        try:
            java = normalize(json.loads(java_path.read_text(encoding="utf-8")), True)
            lean = normalize(json.loads(lean_path.read_text(encoding="utf-8")), True)
        except Exception as e:  # noqa: BLE001
            skipped += 1
            details.append((rel, "error", 0, "", str(e)))
            continue
        diffs: list[str] = []
        compare_json(java, lean, "", 0.0, args.max_diffs_per_model, diffs, set())
        compared += 1
        if diffs:
            differing += 1
            top = re.sub(r"\[\d+\]", "[*]", diffs[0].split(":")[0]).split("/")[-1] or "root"
            categories[top] = categories.get(top, 0) + 1
            details.append((rel, "differs", len(diffs), top, " | ".join(diffs[:5])))
        else:
            identical += 1
            details.append((rel, "identical", 0, "", ""))

    Path(args.details).parent.mkdir(parents=True, exist_ok=True)
    with open(args.details, "w", encoding="utf-8") as f:
        f.write("model_rel_path\tstatus\tdiff_count\tfirst_diff_field\tdiffs\n")
        for d in details:
            f.write("\t".join(str(x).replace("\t", " ").replace("\n", " ") for x in d) + "\n")
    with open(args.report, "w", encoding="utf-8") as f:
        f.write("# ELK Text loader parity (`elk convert` vs ELK Java's JSON export of the same `.elkt`)\n\n")
        f.write(f"- java manifest: `{args.java_manifest}`\n- lean outputs: `{lean_dir}`\n")
        f.write(f"- .elkt models: {total}\n- compared: {compared}\n- identical: {identical}\n- differing: {differing}\n- skipped: {skipped}\n")
        if categories:
            f.write("\n## First differing field\n\n| field | models |\n|---|---:|\n")
            for k, v in sorted(categories.items(), key=lambda kv: -kv[1]):
                f.write(f"| `{k}` | {v} |\n")
        f.write("\n## Differing models\n\n")
        for d in details:
            if d[1] == "differs":
                f.write(f"- `{d[0]}` ({d[2]} diffs): {d[4]}\n")
    print(f"elkt loader parity: models={total} compared={compared} identical={identical} differing={differing} skipped={skipped}")
    return 0 if differing == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
