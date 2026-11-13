#!/usr/bin/env python3
"""Measure a Lake build, gating actual Lean compiler subprocesses to --jobs slots.

Lake 5.0.0 has no `lake build -j` option. LEAN_NUM_THREADS alone is not a
process-count contract, so a directory-local FIFO enforces the limit. An overlay
of symlinks leaves the installed toolchain unchanged. Each compiler runs with
LEAN_NUM_THREADS=1. This monitors this build's process group, not other users' work.
Run the script itself under /usr/bin/time -v to record cumulative CPU and wall time.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument("--jobs", type=int, default=4)
parser.add_argument("--label", required=True)
parser.add_argument("--cwd", type=Path, help="Package directory (defaults to this bridge)")
parser.add_argument("targets", nargs="+")
args = parser.parse_args()
if not 1 <= args.jobs <= 4:
    parser.error("jobs must be between 1 and 4")
root = Path(__file__).resolve().parents[1]
real_root = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
real_lean = real_root / "bin/lean"
run = root / ".lake/measurements" / args.label
run.mkdir(parents=True, exist_ok=False)
stats = run / "modules"
stats.mkdir()
overlay = run / "toolchain"
overlay.mkdir()
for item in real_root.iterdir():
    if item.name != "bin":
        (overlay / item.name).symlink_to(item, target_is_directory=item.is_dir())
(overlay / "bin").mkdir()
for item in (real_root / "bin").iterdir():
    (overlay / "bin" / item.name).symlink_to(
        root / "scripts/lean_slot.py" if item.name == "lean" else item)
(root / "scripts/lean_slot.py").chmod(0o755)
fifo = run / "slots"
os.mkfifo(fifo)
fd = os.open(fifo, os.O_RDWR)
os.write(fd, b"x" * args.jobs)
env = dict(os.environ, LEAN_SYSROOT=str(overlay), LAKE_OVERRIDE_LEAN="true", LEAN_NUM_THREADS=str(args.jobs),
           AXIOM_REAL_LEAN=str(real_lean), AXIOM_SLOT_FIFO=str(fifo), AXIOM_STATS_DIR=str(stats))
command = [str(real_root / "bin/lake"), "--no-cache", "--no-ansi", "build", *args.targets]
result = {"command": command, "jobs": args.jobs, "compiler_threads": 1,
          "cpu_count": os.cpu_count(), "started_unix": time.time(),
          "peak_process_group_rss_bytes": 0, "max_concurrent_compilers": 0,
          "min_mem_available_bytes": 2**64, "min_disk_available_bytes": 2**64}
page = os.sysconf("SC_PAGE_SIZE")
with (run / "build.log").open("w") as log, (run / "resources.jsonl").open("w") as samples:
    proc = subprocess.Popen(command, cwd=(args.cwd or root).resolve(), env=env, stdout=log, stderr=subprocess.STDOUT,
                            start_new_session=True)
    while True:
        rss, compilers = 0, 0
        for p in Path("/proc").iterdir():
            if not p.name.isdigit():
                continue
            try:
                fields = (p / "stat").read_text().rsplit(")", 1)[1].split()
                if int(fields[2]) != proc.pid:
                    continue
                rss += int(fields[21]) * page
                if Path(os.readlink(p / "exe")) == real_lean:
                    compilers += 1
            except (OSError, ValueError, IndexError):
                pass
        mem = next(int(line.split()[1]) * 1024 for line in Path("/proc/meminfo").read_text().splitlines()
                   if line.startswith("MemAvailable:"))
        disk = os.statvfs(root)
        avail = disk.f_bavail * disk.f_frsize
        samples.write(json.dumps({"unix": time.time(), "rss_bytes": rss,
                                  "compilers": compilers, "mem_available_bytes": mem,
                                  "disk_available_bytes": avail}) + "\n")
        samples.flush()
        result["peak_process_group_rss_bytes"] = max(result["peak_process_group_rss_bytes"], rss)
        result["max_concurrent_compilers"] = max(result["max_concurrent_compilers"], compilers)
        result["min_mem_available_bytes"] = min(result["min_mem_available_bytes"], mem)
        result["min_disk_available_bytes"] = min(result["min_disk_available_bytes"], avail)
        try:
            rc = proc.wait(timeout=5)
            break
        except subprocess.TimeoutExpired:
            pass
os.close(fd)
fifo.unlink()
result.update(exit_code=rc, elapsed_seconds=time.time() - result["started_unix"])
(run / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
if result["max_concurrent_compilers"] > args.jobs:
    raise RuntimeError("compiler process limit was exceeded")
raise SystemExit(rc)
