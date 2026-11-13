#!/usr/bin/env python3
"""Summarize a running or completed instrumented build without polling it."""
import argparse
import json
from pathlib import Path
import re
import time

p = argparse.ArgumentParser()
p.add_argument("label")
p.add_argument("--total-axiom-modules", type=int, default=12769)
a = p.parse_args()
root = Path(__file__).resolve().parents[1]
run = root / ".lake/measurements" / a.label
compiled = {"StacksCore": 0, "StacksFrontier": 0, "Mordell": 0, "other": 0}
failed = []
user = system = maxrss = 0.0
largest = ""
module_times = []
for f in (run / "modules").glob("*.time"):
    source_file = f.with_suffix(".source")
    exit_file = f.with_suffix(".exit")
    if not source_file.exists() or not exit_file.exists():
        continue
    source = source_file.read_text().splitlines()[-1]
    text = f.read_text()
    def number(label):
        m = re.search(re.escape(label) + r":\s*([\d.]+)", text)
        return float(m[1]) if m else 0.0
    u, s, rss = number("User time (seconds)"), number("System time (seconds)"), number("Maximum resident set size (kbytes)")
    if rss > maxrss:
        largest, maxrss = source, rss
    if exit_file.read_text().strip() != "0":
        failed.append(source)
        continue
    pkg = next((k for k in compiled if k in Path(source).parts or Path(source).stem == k), "other")
    compiled[pkg] += 1
    if pkg != "other":
        user += u
        system += s
        module_times.append(u + s)
resources = [json.loads(l) for l in (run / "resources.jsonl").read_text().splitlines()]
axiom_done = sum(compiled[k] for k in ("StacksCore", "StacksFrontier", "Mordell"))
summary_file = run / "summary.json"
elapsed = (json.loads(summary_file.read_text())["elapsed_seconds"] if summary_file.exists()
           else time.time() - resources[0]["unix"] if resources else 0)
result = {"compiled": compiled, "axiom_done": axiom_done, "failed": failed,
          "elapsed_seconds": elapsed, "axiom_user_seconds": user, "axiom_system_seconds": system,
          "axiom_cpu_seconds_per_module": (user + system) / axiom_done if axiom_done else None,
          "largest_peak_rss_kib": maxrss, "largest_module": largest,
          "sampled_peak_process_group_rss_bytes": max((r["rss_bytes"] for r in resources), default=0),
          "max_concurrent_compilers": max((r["compilers"] for r in resources), default=0),
          "min_available_memory_bytes": min((r["mem_available_bytes"] for r in resources), default=0),
          "min_available_disk_bytes": min((r["disk_available_bytes"] for r in resources), default=0),
          "projection_from_throughput_seconds": elapsed * a.total_axiom_modules / axiom_done if axiom_done else None,
          "projection_cpu_four_vcpu_lower_bound_seconds": (user + system) * a.total_axiom_modules / axiom_done / 4 if axiom_done else None,
          "projection_caveat": "Early-module averages do not bound later complexity; CPU speeds, IO and critical paths differ."}
print(json.dumps(result, indent=2))
