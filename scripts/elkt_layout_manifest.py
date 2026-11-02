"""Builds the merged manifest of scripts/run_elkt_layout_parity.sh: for every `.elkt` row of a Java
baseline manifest (run with `--live-defaults true`) it reads the Java layout and the elk-lean layout of
`elk layout --defaults <model.elkt>`, writes normalised copies (geometry only: option maps dropped,
generated ids of duplicate identifiers `_g123456` / `_g000000` dropped) and the elk-rs style manifest
that compare_model_parity_layouts.py consumes.
    python3 scripts/elkt_layout_manifest.py <java_manifest.tsv> <lean_dir> <out_dir>
SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
"""
from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from compare_elkt_conversion import normalize_string  # noqa: E402


def normalize(value, is_root: bool = False):
    """Geometry only: `layoutOptions` / `properties` / `individualSpacings` are dropped on both sides
    (the options are compared by scripts/compare_elkt_conversion.py; ELK Java's export of the laid-out
    graph also carries result properties such as `layering.layerId` that elk-lean's output, which
    echoes the input options, does not). Generated ids of duplicate identifiers are dropped."""
    if isinstance(value, dict):
        out = {}
        for k, v in value.items():
            if k in ("layoutOptions", "properties", "individualSpacings"):
                continue
            if k == "container":
                # written by `transferLayout` (JSON path, Java and elk-lean alike) but not by ELK's export of
                # the laid-out EMF graph; the edge's place in its container's `edges` array is compared anyway
                continue
            if k == "sections" and isinstance(v, list):
                # generated section ids differ by construction (ELK's exporter: `s<n>`; transferLayout and
                # elk-lean: `<edge>_s<n>`); the sections are compared in order by their geometry and shapes
                out[k] = [{kk: normalize(vv) for kk, vv in sec.items() if kk not in ("id", "incomingSections", "outgoingSections")}
                          if isinstance(sec, dict) else normalize(sec) for sec in v]
                continue
            out[k] = normalize(v)
        return out
    if isinstance(value, list):
        return [normalize(v) for v in value]
    if isinstance(value, str):
        return normalize_string(value)
    return value


def main() -> int:
    java_manifest, lean_dir, out_dir = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
    norm = out_dir / "normalized"
    rows_out = ["model_rel_path\tinput_json\tjava_layout_json\tjava_status\tjava_error\trust_layout_json\trust_status\trust_error"]
    with java_manifest.open(encoding="utf-8") as f:
        for row in csv.DictReader(f, delimiter="\t"):
            rel = row["model_rel_path"]
            if not rel.lower().endswith(".elkt"):
                continue
            java_out = norm / "java" / (rel + ".json")
            lean_out = norm / "lean" / (rel + ".json")
            java_out.parent.mkdir(parents=True, exist_ok=True)
            lean_out.parent.mkdir(parents=True, exist_ok=True)
            if row["java_status"] == "ok":
                java_out.write_text(json.dumps(normalize(json.loads(Path(row["java_layout_json"]).read_text(encoding="utf-8")), True)), encoding="utf-8")
            lean_src = lean_dir / (rel + ".json")
            err_src = lean_dir / (rel + ".err")
            if lean_src.is_file():
                lean_out.write_text(json.dumps(normalize(json.loads(lean_src.read_text(encoding="utf-8")), True)), encoding="utf-8")
                rust_status, rust_error = "ok", ""
            else:
                rust_status = "error"
                rust_error = err_src.read_text(encoding="utf-8").strip().replace("\t", " ").replace("\n", " ") if err_src.is_file() else "no output"
            rows_out.append("\t".join([rel, row["input_json"], str(java_out), row["java_status"], row["java_error"], str(lean_out), rust_status, rust_error]))
    (out_dir / "merged.tsv").write_text("\n".join(rows_out) + "\n", encoding="utf-8")
    print(f"merged manifest: {len(rows_out) - 1} .elkt models -> {out_dir / 'merged.tsv'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
