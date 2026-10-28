#!/usr/bin/env python3
"""Driver of `scripts/run_random_java_parity.sh` (see there for the usage).

Stages (each skipped when its result is already in <out_dir> unless --force):
  gen    <out>/gen/s<seed> (gen_nodesize_graphs.py OUT COUNT SEED), <out>/gen/v<seed> (sanitize_for_java.py)
  java   <out>/java/<set>/ : ELK Java 0.12.0 (`ElkJavaBaseline`), one JVM per set with a watchdog: a
         model that makes no progress for --java-timeout seconds is recorded as `timeout`, the JVM is
         killed and restarted on the remaining models (chunk directories of symlinks); a per-set alarm
         (--java-set-timeout) records everything left as `timeout`. outcomes.tsv: file, outcome, error.
  lean   <out>/lean/<set>/ : `elk layout` per input (one process each, --jobs in parallel, --timeout
         seconds): ok / exception (first stderr line) / timeout / overflow (`Stack overflow detected`)
         / crash (other signal). outcomes.tsv + the layouts.
  rs     (--with-oracle) <out>/rs/<set>/ : elk-rs `model_parity_layout_runner`, one process per input.
  report details.tsv, report.md (and compare/<set>/ with the compare_model_parity_layouts.py output
         at tol 0 and 1e-6).
"""
from __future__ import annotations

import argparse
import collections
import concurrent.futures as cf
import csv
import importlib.util
import json
import os
import shutil
import signal
import subprocess
import sys
import time

csv.field_size_limit(64 * 1024 * 1024)
HERE = os.path.dirname(os.path.abspath(__file__))
JAVA_HEADER = "model_rel_path\tinput_json\tjava_layout_json\tjava_status\tjava_error"


def load_classifier():
    spec = importlib.util.spec_from_file_location("classify_random_parity",
                                                  os.path.join(HERE, "classify_random_parity.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def clean(s, n=2000):
    return (s or "").replace("\t", " ").replace("\r", " ").replace("\n", " ")[:n]


def inputs_of(d):
    return sorted(f for f in os.listdir(d) if f.endswith(".json"))


def read_outcomes(path):
    out = {}
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            for line in f:
                p = line.rstrip("\n").split("\t")
                if len(p) >= 3 and p[0] != "input":
                    out[p[0]] = (p[1], p[2], p[3] if len(p) > 3 else "")
    return out


def write_outcomes(path, rows):
    with open(path, "w", encoding="utf-8") as f:
        f.write("input\toutcome\terror\tlayout\n")
        for k in sorted(rows):
            o, e, lay = rows[k]
            f.write(f"{k}\t{o}\t{clean(e)}\t{lay}\n")


# ------------------------------------------------------------------------------------------- gen

def stage_gen(a, seeds, sets):
    for seed in seeds:
        s_dir = os.path.join(a.out, "gen", f"s{seed}")
        if a.force or not os.path.isdir(s_dir) or len(inputs_of(s_dir)) != a.count:
            shutil.rmtree(s_dir, ignore_errors=True)
            subprocess.run([sys.executable, "-I", os.path.join(HERE, "gen_nodesize_graphs.py"), s_dir,
                            str(a.count), str(seed)], check=True, stdout=subprocess.DEVNULL)
        for kind, extra in (("v", []), ("d", ["--explicit-defaults"])):
            if kind not in sets:
                continue
            k_dir = os.path.join(a.out, "gen", f"{kind}{seed}")
            if a.force or not os.path.isdir(k_dir) or len(inputs_of(k_dir)) != a.count:
                shutil.rmtree(k_dir, ignore_errors=True)
                subprocess.run([sys.executable, "-I", os.path.join(HERE, "sanitize_for_java.py"), s_dir, k_dir]
                               + extra, check=True, stdout=subprocess.DEVNULL)


# ------------------------------------------------------------------------------------------ java

def java_outcome(status, err):
    if status == "ok":
        return "ok"
    if "StackOverflowError" in err:
        return "overflow"
    return "exception"


def run_java_set(a, set_name):
    src = os.path.join(a.out, "gen", set_name)
    dst = os.path.join(a.out, "java", set_name)
    res_path = os.path.join(dst, "outcomes.tsv")
    if not a.force and os.path.exists(res_path) and len(read_outcomes(res_path)) == len(inputs_of(src)):
        return set_name, "cached"
    shutil.rmtree(dst, ignore_errors=True)
    os.makedirs(dst)
    remaining = inputs_of(src)
    results = {}
    t_set = time.time()
    chunk = 0
    notes = []
    while remaining:
        cdir = os.path.join(dst, f"chunk{chunk}")
        cin, cout = os.path.join(cdir, "in"), os.path.join(cdir, "out")
        os.makedirs(cin)
        for f in remaining:
            os.symlink(os.path.abspath(os.path.join(src, f)), os.path.join(cin, f))
        log = open(os.path.join(cdir, "java.log"), "w")
        xss = [f"-Xss{a.java_xss}"] if a.java_xss else []
        proc = subprocess.Popen([a.java] + xss + ["-cp", a.java_cp,
                                 "org.eclipse.elk.lean.baseline.ElkJavaBaseline", cin, cout],
                                stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        manifest = os.path.join(cout, "java_manifest.tsv")
        last_rows, last_change = -1, time.time()
        reason = None
        while True:
            time.sleep(0.25)
            rows = 0
            if os.path.exists(manifest):
                with open(manifest, "rb") as m:
                    rows = m.read().count(b"\n")
            if rows != last_rows:
                last_rows, last_change = rows, time.time()
            if proc.poll() is not None:
                break
            # JVM start-up and the first model share the first window
            if time.time() - last_change > a.java_timeout + (15 if rows <= 1 else 0):
                reason = "timeout"
            elif time.time() - t_set > a.java_set_timeout:
                reason = "alarm"
            if reason:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
                break
        log.close()
        done = []
        if os.path.exists(manifest):
            with open(manifest, encoding="utf-8") as m:
                for r in csv.DictReader(m, delimiter="\t"):
                    if r.get("java_status") is None:
                        continue
                    err = r.get("java_error") or ""
                    results[r["model_rel_path"]] = (java_outcome(r["java_status"], err), err,
                                                    r["java_layout_json"] if r["java_status"] == "ok" else "")
                    done.append(r["model_rel_path"])
        dset = set(done)
        remaining = [f for f in remaining if f not in dset]
        if reason == "timeout" and remaining:
            results[remaining[0]] = ("timeout", f"no progress for {a.java_timeout:g}s", "")
            notes.append(f"{remaining[0]}: timeout")
            remaining = remaining[1:]
        elif reason == "alarm":
            for f in remaining:
                results[f] = ("timeout", f"set alarm {a.java_set_timeout:g}s", "")
            notes.append(f"set alarm: {len(remaining)} models not run")
            remaining = []
        elif remaining:
            with open(os.path.join(cdir, "java.log"), encoding="utf-8", errors="replace") as lg:
                tail = " ".join(lg.read().strip().splitlines()[-3:])
            results[remaining[0]] = ("crash", f"JVM exit {proc.returncode}: {tail[-300:]}", "")
            notes.append(f"{remaining[0]}: JVM crash")
            remaining = remaining[1:]
        chunk += 1
    write_outcomes(res_path, results)
    return set_name, f"{time.time() - t_set:.0f}s chunks={chunk}" + (f" ({'; '.join(notes)})" if notes else "")


# ------------------------------------------------------------------------------------------ lean

def run_lean_one(a, src, dst, f):
    out = os.path.join(dst, "layouts", f)
    try:
        r = subprocess.run([a.lean, "layout", os.path.join(src, f), "--pretty", "--sort-keys", "-o", out],
                           capture_output=True, timeout=a.timeout)
    except subprocess.TimeoutExpired:
        return f, "timeout", f"timeout {a.timeout:g}s", ""
    err = (r.stderr.decode("utf-8", "replace") + r.stdout.decode("utf-8", "replace")).strip()
    if r.returncode == 0:
        return f, "ok", "", out
    if "Stack overflow" in err:
        return f, "overflow", "Stack overflow detected. Aborting.", ""
    if r.returncode < 0:
        return f, "crash", f"signal {-r.returncode}: {err[:200]}", ""
    return f, "exception", err.splitlines()[0] if err else f"exit {r.returncode}", ""


def run_lean_set(a, set_name):
    src = os.path.join(a.out, "gen", set_name)
    dst = os.path.join(a.out, "lean", set_name)
    res_path = os.path.join(dst, "outcomes.tsv")
    if not a.force and os.path.exists(res_path) and len(read_outcomes(res_path)) == len(inputs_of(src)):
        return set_name, "cached"
    shutil.rmtree(dst, ignore_errors=True)
    os.makedirs(os.path.join(dst, "layouts"))
    t0 = time.time()
    results = {}
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        for f, o, e, lay in ex.map(lambda f: run_lean_one(a, src, dst, f), inputs_of(src)):
            results[f] = (o, e, lay)
    write_outcomes(res_path, results)
    return set_name, f"{time.time() - t0:.0f}s"


# -------------------------------------------------------------------------------------------- rs

def run_rs_one(a, src, dst, f):
    d = os.path.join(dst, "work", f[:-5])
    shutil.rmtree(d, ignore_errors=True)
    os.makedirs(d)
    with open(os.path.join(d, "m.tsv"), "w") as m:
        m.write(JAVA_HEADER + "\n")
        m.write(f"{f}\t{os.path.abspath(os.path.join(src, f))}\t\tok\t\n")
    env = dict(os.environ, MODEL_PARITY_TIMEOUT_SECS=str(int(a.timeout)))
    try:
        r = subprocess.run([a.rs, "--input-manifest", os.path.join(d, "m.tsv"), "--output-manifest",
                            os.path.join(d, "o.tsv"), "--rust-layout-dir", os.path.join(d, "layout"),
                            "--pretty-print", "true"], capture_output=True, timeout=a.timeout + 10, env=env)
    except subprocess.TimeoutExpired:
        return f, "timeout", "killed", ""
    se = r.stderr.decode("utf-8", "replace")
    if "overflowed its stack" in se:
        return f, "overflow", "", ""
    try:
        with open(os.path.join(d, "o.tsv"), encoding="utf-8") as o:
            row = next(csv.DictReader(o, delimiter="\t"))
        st, err, lay = row.get("rust_status", ""), row.get("rust_error", "") or "", row.get("rust_layout_json", "")
    except Exception:  # noqa: BLE001
        return f, "crash", f"exit {r.returncode}: {' '.join(se.strip().splitlines()[-2:])[:300]}", ""
    if st == "ok":
        return f, "ok", "", lay
    if err == "timeout" or err.startswith("exceeded"):
        return f, "timeout", "runner timeout", ""
    return f, "exception", err, ""


def run_rs_set(a, set_name):
    src = os.path.join(a.out, "gen", set_name)
    dst = os.path.join(a.out, "rs", set_name)
    res_path = os.path.join(dst, "outcomes.tsv")
    if not a.force and os.path.exists(res_path) and len(read_outcomes(res_path)) == len(inputs_of(src)):
        return set_name, "cached"
    shutil.rmtree(dst, ignore_errors=True)
    os.makedirs(dst)
    t0 = time.time()
    results = {}
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        for f, o, e, lay in ex.map(lambda f: run_rs_one(a, src, dst, f), inputs_of(src)):
            results[f] = (o, e, lay)
    write_outcomes(res_path, results)
    return set_name, f"{time.time() - t0:.0f}s"


# ---------------------------------------------------------------------------------------- report

def compare(a, set_name, left_name, left, right_name, right, tol, tag):
    """compare_model_parity_layouts.py on the inputs both sides laid out -> {input: (status, top, first)}"""
    d = os.path.join(a.out, "compare", set_name)
    os.makedirs(d, exist_ok=True)
    man = os.path.join(d, f"{tag}.manifest.tsv")
    with open(man, "w", encoding="utf-8") as m:
        m.write("model_rel_path\tjava_layout_json\tjava_status\trust_layout_json\trust_status\n")
        for f in sorted(left):
            if f in right and left[f][0] == "ok" and right[f][0] == "ok":
                m.write(f"{f}\t{left[f][2]}\tok\t{right[f][2]}\tok\n")
    details = os.path.join(d, f"{tag}.details.tsv")
    cmd = [sys.executable, "-I", os.path.join(HERE, "compare_model_parity_layouts.py"), "--manifest", man,
           "--report", os.path.join(d, f"{tag}.report.md"), "--details", details, "--abs-tol", str(tol),
           "--max-diffs-per-model", "50"]
    subprocess.run(cmd, check=False, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    out = {}
    if os.path.exists(details):
        with open(details, encoding="utf-8") as f:
            for r in csv.DictReader(f, delimiter="\t"):
                out[r["model_rel_path"]] = (r["status"], r["top_category"], r["first_diff"])
    return out


def err_class(msg):
    head = msg.split(": ", 1)[0].strip()
    return head if head and " " not in head else msg[:60]


WRAPPER = "org.eclipse.elk.core.UnsupportedConfigurationException: "


def match_class(lo, le, jo, je, exact, tol6):
    if lo == "ok" and jo == "ok":
        st = exact[0] if exact else "skip"
        if st == "match":
            return "exact"
        if tol6 and tol6[0] == "match":
            return "tol1e-6"
        if st == "drift":
            return f"drift:{exact[1] or 'other'}"
        return "compare_error"
    if lo == "exception" and jo == "exception":
        if le == je:
            return "error_equal"
        if le == WRAPPER + je:
            return "error_wrapped"
        if err_class(le) == err_class(je):
            return "error_class_equal"
        return "error_differs"
    if lo == jo:
        return f"{lo}_both"
    return f"outcome:{lo}/{jo}"


def stage_report(a, set_names):
    cl = load_classifier()
    rows = []
    for s in set_names:
        lean = read_outcomes(os.path.join(a.out, "lean", s, "outcomes.tsv"))
        java = read_outcomes(os.path.join(a.out, "java", s, "outcomes.tsv"))
        rs = read_outcomes(os.path.join(a.out, "rs", s, "outcomes.tsv")) if a.with_oracle else {}
        exact = compare(a, s, "java", java, "lean", lean, 0, "exact")
        tol6 = compare(a, s, "java", java, "lean", lean, 1e-6, "tol6")
        rs_lean = compare(a, s, "rs", rs, "lean", lean, 1e-6, "rs_lean") if rs else {}
        rs_java = compare(a, s, "java", java, "rs", rs, 0, "rs_java") if rs else {}
        for f in inputs_of(os.path.join(a.out, "gen", s)):
            path = os.path.abspath(os.path.join(a.out, "gen", s, f))
            with open(path, encoding="utf-8") as fh:
                g = json.load(fh)
            alg, child, opts = cl.options_summary(g)
            lo, le, ll = lean.get(f, ("missing", "", ""))
            jo, je, jl = java.get(f, ("missing", "", ""))
            ro = rs.get(f, ("-", "", ""))[0] if rs else "-"
            mc = match_class(lo, le, jo, je, exact.get(f), tol6.get(f))
            rvl = ""
            if f in rs_lean:
                rvl = "same" if rs_lean[f][0] == "match" else "differs"
            rvj = ""
            if f in rs_java:
                rvj = "exact" if rs_java[f][0] == "match" else "differs"
            rows.append({
                "set": s, "input": f, "algorithm": alg, "child_algorithms": child, "options": opts,
                "lean_outcome": lo, "java_outcome": jo, "rs_outcome": ro, "match_class": mc,
                "rs_vs_lean": rvl, "rs_vs_java": rvj,
                "lean_error": clean(le, 600), "java_error": clean(je, 600),
                "first_diff": clean((exact.get(f) or ("", "", ""))[2], 300),
                "input_path": path, "java_layout": jl, "lean_layout": ll,
            })
    cols = ["set", "input", "algorithm", "child_algorithms", "options", "lean_outcome", "java_outcome",
            "rs_outcome", "match_class", "rs_vs_lean", "rs_vs_java", "lean_error", "java_error", "first_diff",
            "input_path", "java_layout", "lean_layout"]
    with open(os.path.join(a.out, "details.tsv"), "w", encoding="utf-8") as f:
        f.write("\t".join(cols) + "\n")
        for r in rows:
            f.write("\t".join(r[c] for c in cols) + "\n")
    write_report(a, rows, set_names)


def write_report(a, rows, set_names):
    L = []
    w = L.append
    w("# Random-graph ELK Java parity")
    w("")
    w(f"Generated by `scripts/run_random_java_parity.sh` (seeds {a.seeds}, {a.count} graphs per seed, sets "
      f"{a.sets}, elk-lean limit {a.timeout:g}s per input, Java watchdog {a.java_timeout:g}s per model"
      f"{', elk-rs oracle' if a.with_oracle else ''}). `s` = `gen_nodesize_graphs.py` output as generated, "
      "`v` = the same graphs sanitised for ELK Java's node size validation (`sanitize_for_java.py`), "
      "`d` (experiment) = `v` plus ELK Java's algorithm specific option defaults written explicitly "
      "(`sanitize_for_java.py --explicit-defaults`).")
    w("")
    w("## Per set")
    w("")
    w("| set | inputs | Lean ok/exc/timeout/overflow/crash | Java ok/exc/timeout/overflow | both ok | exact (tol 0) "
      "| 1e-6 | both exception | error text equal |" + (" elk-rs = Java exact |" if a.with_oracle else ""))
    w("|---|---:|---|---|---:|---:|---:|---:|---:|" + ("---:|" if a.with_oracle else ""))
    tot = collections.Counter()

    def counts(rs, key, order):
        c = collections.Counter(r[key] for r in rs)
        return "/".join(str(c[o]) for o in order)

    kinds = collections.OrderedDict()
    for s in set_names:
        kinds.setdefault(s[0], []).append(s)
    for s in set_names + [f"{k} (all)" for k in kinds] + ["all"]:
        if s == "all":
            rs = rows
        elif s.endswith("(all)"):
            rs = [r for r in rows if r["set"][0] == s[0]]
        else:
            rs = [r for r in rows if r["set"] == s]
        both = [r for r in rs if r["lean_outcome"] == "ok" and r["java_outcome"] == "ok"]
        ex = sum(r["match_class"] == "exact" for r in both)
        t6 = sum(r["match_class"] in ("exact", "tol1e-6") for r in both)
        be = [r for r in rs if r["lean_outcome"] == "exception" and r["java_outcome"] == "exception"]
        ee = sum(r["match_class"] == "error_equal" for r in be)
        line = (f"| {s} | {len(rs)} | {counts(rs, 'lean_outcome', ['ok', 'exception', 'timeout', 'overflow', 'crash'])} "
                f"| {counts(rs, 'java_outcome', ['ok', 'exception', 'timeout', 'overflow'])} | {len(both)} | {ex} | {t6} "
                f"| {len(be)} | {ee} |")
        if a.with_oracle:
            line += f" {sum(r['rs_vs_java'] == 'exact' for r in both)} |"
        w(line)
    w("")
    for k, sets in kinds.items():
        rs = [r for r in rows if r["set"][0] == k]
        w(f"## Outcome matrix, {k} sets (rows elk-lean, columns ELK Java)")
        w("")
        cols = ["ok", "exception", "timeout", "overflow", "crash", "missing"]
        m = collections.Counter((r["lean_outcome"], r["java_outcome"]) for r in rs)
        used_c = [c for c in cols if any(m[(x, c)] for x in cols)]
        used_r = [x for x in cols if any(m[(x, c)] for c in cols)]
        w("| Lean \\ Java | " + " | ".join(used_c) + " |")
        w("|---|" + "---:|" * len(used_c))
        for x in used_r:
            w(f"| {x} | " + " | ".join(str(m[(x, c)]) for c in used_c) + " |")
        w("")
    w("## Match classes")
    w("")
    w("`exact`: equal at tol 0; `tol1e-6`: equal only at 1e-6; `drift:<category>`: different (top category of "
      "`compare_model_parity_layouts.py`); `error_equal`: both threw the same text (class included); "
      "`error_wrapped`: equal after the old API wrapper `UnsupportedConfigurationException: ` in front of Lean's text; "
      "`error_class_equal` / `error_differs`; `outcome:<lean>/<java>`: different outcomes.")
    w("")
    mc = collections.Counter((r["set"][0], r["match_class"]) for r in rows)
    w("| match class | " + " | ".join(kinds) + " |")
    w("|---|" + "---:|" * len(kinds))
    for c in sorted({k[1] for k in mc}, key=lambda c: -sum(mc[(k, c)] for k in kinds)):
        w(f"| {c} | " + " | ".join(str(mc[(k, c)]) for k in kinds) + " |")
    w("")
    w("## Error agreement (both threw)")
    w("")
    import re
    norm = lambda m: re.sub(r"\d+(\.\d+)?", "N", re.sub(r"\[[^\]]*\]", "[..]", m))[:120]
    pairs = collections.Counter()
    for r in rows:
        if r["lean_outcome"] == "exception" and r["java_outcome"] == "exception":
            pairs[(r["match_class"], norm(r["java_error"]), "" if r["match_class"] == "error_equal" else norm(r["lean_error"]))] += 1
    w("| count | class | Java (normalised) | Lean when different |")
    w("|---:|---|---|---|")
    for (c, j, l), n in pairs.most_common(30):
        w(f"| {n} | {c} | `{j}` | {('`' + l + '`') if l else ''} |")
    w("")
    w("## Different outcomes")
    w("")
    oc = collections.Counter()
    for r in rows:
        if r["match_class"].startswith("outcome:"):
            side = r["java_error"] if r["java_outcome"] != "ok" else r["lean_error"]
            oc[(r["set"][0], r["match_class"], norm(side))] += 1
    w("| set kind | outcome Lean/Java | count | error of the failing side (normalised) |")
    w("|---|---|---:|---|")
    for (k, c, e), n in sorted(oc.items(), key=lambda kv: (kv[0][0], -kv[1])):
        w(f"| {k} | {c} | {n} | `{e}` |")
    w("")
    with open(os.path.join(a.out, "report.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(L) + "\n")


# ------------------------------------------------------------------------------------------ main

def parse_seeds(spec):
    out = []
    for part in spec.split(","):
        if "-" in part:
            x, y = part.split("-")
            out.extend(range(int(x), int(y) + 1))
        elif part:
            out.append(int(part))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--seeds", default="1-10")
    ap.add_argument("--count", type=int, default=600)
    ap.add_argument("--sets", default="s,v")
    ap.add_argument("--timeout", type=float, default=15)
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--java-jobs", type=int, default=2)
    ap.add_argument("--java-timeout", type=float, default=60)
    ap.add_argument("--java-set-timeout", type=float, default=1800)
    ap.add_argument("--java-xss", default="", help="JVM thread stack size (default: the JVM default)")
    ap.add_argument("--with-oracle", action="store_true")
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--stages", default="gen,java,lean,rs,report")
    ap.add_argument("--lean", required=True)
    ap.add_argument("--java")
    ap.add_argument("--java-cp")
    ap.add_argument("--rs")
    a = ap.parse_args()
    a.out = os.path.abspath(a.out)
    seeds = parse_seeds(a.seeds)
    sets = [s.strip() for s in a.sets.split(",") if s.strip()]
    set_names = [f"{k}{seed}" for k in sets for seed in seeds]
    stages = set(a.stages.split(","))
    os.makedirs(a.out, exist_ok=True)
    t0 = time.time()
    if "gen" in stages:
        stage_gen(a, seeds, sets)
        print(f"[gen] {len(set_names)} sets x {a.count}", flush=True)
    # the JVMs (--java-jobs sets at a time) run next to the Lean sets (one after the other, each with
    # --jobs processes)
    with cf.ThreadPoolExecutor(max(1, a.java_jobs)) as jex, cf.ThreadPoolExecutor(1) as lex:
        jobs = {}
        if "java" in stages:
            jobs.update({jex.submit(run_java_set, a, s): "java" for s in set_names})
        if "lean" in stages:
            jobs.update({lex.submit(run_lean_set, a, s): "lean" for s in set_names})
        for j in cf.as_completed(jobs):
            s, msg = j.result()
            print(f"[{jobs[j]}] {s} {msg} ({time.time() - t0:.0f}s)", flush=True)
    if a.with_oracle and "rs" in stages:
        for s in set_names:
            print(f"[rs] {s} {run_rs_set(a, s)[1]}", flush=True)
    if "report" in stages:
        stage_report(a, set_names)
        print(f"[report] {os.path.join(a.out, 'report.md')}", flush=True)
    print(f"done in {time.time() - t0:.0f}s", flush=True)


if __name__ == "__main__":
    main()
