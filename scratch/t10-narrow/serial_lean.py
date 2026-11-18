#!/usr/bin/env python3
"""Refresh a copied Lean cache, then check files, with one Lean job at a time.

Run from the repository root. For a current cache, omit --cache-base.
The optional --package-cache supplies the build of the unchanged lean/ package.
Only ignored .lake artifacts are written for module compilation.
"""
import argparse
import os
from pathlib import Path
import re
import subprocess
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--cache-base", help="revision of the copied build")
parser.add_argument("--package-cache", type=Path)
parser.add_argument("--plan", action="store_true")
parser.add_argument("--module", action="append", default=[])
parser.add_argument("check", nargs="*", type=Path)
args = parser.parse_args()
cache = Path(".lake/build/lib/lean")
local = Path("lean/.lake/build/lib/lean")
seen = set()
updated = set()
env = os.environ.copy()
if args.package_cache:
    env["LEAN_PATH"] = os.pathsep.join(
        filter(None, (str(args.package_cache.resolve()), env.get("LEAN_PATH")))
    )
changed = set()
if args.cache_base:
    subprocess.run(["git", "merge-base", "--is-ancestor", args.cache_base, "HEAD"], check=True)
    changed = set(subprocess.check_output(
        ["git", "diff", "--name-only", args.cache_base, "--", "*.lean"], text=True
    ).splitlines())


def lean(*cmd):
    start = time.monotonic()
    while True:
        uptime = subprocess.check_output(["uptime"], text=True).strip()
        mem = subprocess.check_output(["free", "-g"], text=True).strip()
        load = float(re.search(r"load averages?:\s*([0-9.]+)", uptime)[1])
        free_gb = int(next(s for s in mem.splitlines() if s.startswith("Mem:")).split()[-1])
        print(uptime, mem, sep="\n", flush=True)
        if load <= 150 and free_gb >= 20:
            break
        if time.monotonic() - start >= 3600:
            raise SystemExit("Lean blocked by host load or memory for an hour")
        print("Holding for host load or memory", flush=True)
        time.sleep(300)
    subprocess.run(["lake", "env", "lean", *map(str, cmd)], check=True, env=env)


def imports(src):
    return re.findall(
        r"^(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?([\w.]+)",
        src.read_text(), flags=re.M,
    )


def visit(module):
    if module in seen:
        return
    seen.add(module)
    stem = Path(*module.split("."))
    base = cache
    src = stem.with_suffix(".lean")
    root = Path(".")
    options = []
    if module.startswith("ZInQ.") or module == "ZInQ":
        if args.package_cache and (args.package_cache / stem.with_suffix(".olean")).exists():
            return
        root, base = Path("lean"), local
        src = root / src
    elif module == "Submission" or module.startswith(("Submission.", "ChallengeDeps")):
        root = Path("ThirdParty/GreenTao")
        src = root / src
        options = ["-DautoImplicit=false"]
    elif not (module == "ZInQKernel" or module.startswith("ZInQKernel.")):
        return  # pinned Mathlib/toolchain
    olean = base / stem.with_suffix(".olean")
    deps = imports(src)
    for dep in deps:
        visit(dep)
    if (not olean.exists() or str(src) in changed
            or src.stat().st_mtime_ns > olean.stat().st_mtime_ns and not args.cache_base
            or updated.intersection(deps)):
        updated.add(module)
        print(f"Compile {src}", flush=True)
        if not args.plan:
            olean.parent.mkdir(parents=True, exist_ok=True)
            lean(*options, "-R", root, "-o", olean, src)
            changed.discard(str(src))


for module in args.module:
    visit(module)
for check in args.check:
    for dep in imports(check):
        visit(dep)
    if not args.plan:
        lean(check)
print(f"{len(updated)} project modules compiled" if not args.plan else
      f"{len(updated)} project modules to compile")
