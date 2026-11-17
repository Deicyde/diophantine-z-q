#!/usr/bin/env python3
"""Build the complete kernel project and check its exact proof contracts."""
import argparse
from contextlib import nullcontext
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

from check_kernel_contract import ROOT, git, validate
from kernel_diagnostics import AuditDiagnostics


def run(command, output, name, cwd=ROOT, audit_metrics=False):
    start = time.monotonic()
    usage_path = output / (name + "-resource-usage.txt")
    if audit_metrics and sys.platform.startswith("linux") and Path("/usr/bin/time").is_file():
        # GNU time records the OS high-water RSS as well as CPU, faults and swaps.
        command = ["/usr/bin/time", "-v", "-o", str(usage_path), "--", *command]
    print(f"[kernel-ci] {name}: starting", flush=True)
    with (output / (name + ".log")).open("w", encoding="utf-8") as log:
        log.write(json.dumps(command) + "\n")
        log.flush()
        proc = subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, errors="replace")
        with proc.stdout, (AuditDiagnostics(proc.pid, output, name=name) if audit_metrics else nullcontext()):
            for line in proc.stdout:
                print(line, end="", flush=True)
                log.write(line)
                log.flush()
            code = proc.wait()
    print(f"[kernel-ci] {name}: exit {code}, elapsed {time.monotonic() - start:.1f}s", flush=True)
    if audit_metrics and usage_path.is_file():
        print(usage_path.read_text(encoding="utf-8", errors="replace"), flush=True)
    (output / (name + "-timing.json")).write_text(json.dumps({
        "seconds": round(time.monotonic() - start, 3), "exit_code": code,
        "lean_num_threads": os.environ.get("LEAN_NUM_THREADS"),
        "command": command}), encoding="utf-8")
    if code:
        raise RuntimeError(f"{name} failed ({code}); see {output / (name + '.log')}")


def check_dependencies():
    manifest = json.loads((ROOT / "lake-manifest.json").read_bytes())
    for package in manifest["packages"]:
        if package["type"] == "git":
            path = ROOT / manifest["packagesDir"] / package["name"]
            actual = git(path, "rev-parse", "HEAD").decode().strip()
            if actual != package["rev"]:
                raise RuntimeError("Dependency revision mismatch: " + package["name"])
            if git(path, "status", "--porcelain", "--untracked-files=no"):
                raise RuntimeError("Modified dependency source: " + package["name"])


def progress(report, output, base_report=None):
    previous = {}
    if base_report:
        base = json.loads(base_report.read_bytes())
        if base.get("contract_sha256") == report["contract_sha256"]:
            previous = {r["declaration"]: r for r in base["targets"]}
    rows = ["# Kernel proof status", "", "The headline remains conditional on:", "",
            "```lean", report["headline_type"], "```", "",
            "| Target | Base | Candidate |", "|---|---|---|"]
    for target in report["targets"]:
        old = previous.get(target["declaration"], {}).get("status", "not measured")
        rows.append(f"| `{target['declaration']}` | {old} | {target['status']} |")
    rows += ["", "A passed kernel audit is not independent Astra acceptance.",
             "These targets concern the original large polynomial, not the current quartic.",
             "A proved premise does not remove it from the headline until a discharge theorem is checked.", ""]
    text = "\n".join(rows)
    (output / "progress.md").write_text(text, encoding="utf-8")
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as summary:
            summary.write(text)


def build_identity(contract, version):
    return {"head_sha": git(ROOT, "rev-parse", "HEAD").decode().strip(),
            "contract_sha256": contract["manifest_sha256"],
            "compiler": version.strip(), "modules": sorted(contract["modules"])}


def build_modules(contract, version, output):
    # Never let a failed new build leave an earlier success marker/report usable.
    for name in ("build-complete.json", "audit.json", "progress.md"):
        (output / name).unlink(missing_ok=True)
    identity = build_identity(contract, version)
    phases = ["root-build"]
    run(["lake", "build", "ZInQKernel", "GreenTaoVendor"], output,
        "root-build", audit_metrics=True)
    # Explicit targets also build new Contrib files not imported by a root.
    names = sorted(contract["modules"])
    for i in range(0, len(names), 100):
        name = f"modules-{i//100}"
        run(["lake", "build", *["+" + n for n in names[i:i+100]]], output,
            name, audit_metrics=True)
        phases.append(name)
    run(["python", "-B", "scripts/check_target.py"], output, "frozen-target-build")
    if validate() != contract or build_identity(contract, version) != identity:
        raise RuntimeError("Source contract or revision changed during compilation")
    check_dependencies()
    marker = {"schema": "kernel-build-complete/v1", "status": "complete",
              "identity": identity, "phases": phases,
              "completed_at": datetime.now(timezone.utc).isoformat(),
              "acceptance": False}
    (output / "build-complete.json").write_text(json.dumps(marker, indent=2) + "\n", encoding="utf-8")


def audit_modules(contract, version, output, base_report=None, require_build=True):
    identity = build_identity(contract, version)
    for name in ("audit.json", "progress.md"):
        (output / name).unlink(missing_ok=True)
    if require_build:
        marker = json.loads((output / "build-complete.json").read_bytes())
        if (marker.get("schema") != "kernel-build-complete/v1"
                or marker.get("status") != "complete"
                or marker.get("identity") != identity):
            raise RuntimeError("Missing or stale completed-build identity")
    # Recheck after the artifact upload separating the two required CI steps.
    run(["python", "-B", "scripts/check_target.py"], output, "frozen-target")
    if validate() != contract:
        raise RuntimeError("Source contract changed before the audit")
    check_dependencies()
    spec = dict(contract)
    spec["modules"] = sorted(contract["modules"])
    spec_path = output / "spec.json"
    spec_path.write_text(json.dumps(spec, indent=2), encoding="utf-8")
    run(["lake", "env", "lean", "--run", "scripts/audit_kernel.lean", str(spec_path),
         str(output / "audit.json")], output, "kernel-audit", audit_metrics=True)
    report = json.loads((output / "audit.json").read_bytes())
    if validate() != contract or build_identity(contract, version) != identity:
        raise RuntimeError("Source contract changed during the audit")
    check_dependencies()
    report["head_sha"] = git(ROOT, "rev-parse", "HEAD").decode().strip()
    report["contract_sha256"] = contract["manifest_sha256"]
    report["compiler"] = version.strip()
    (output / "audit.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    progress(report, output, base_report)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, default=ROOT / "build/kernel-ci")
    p.add_argument("--base-report", type=Path)
    p.add_argument("--phase", choices=("all", "build", "audit"), default="all",
                   help="Required CI runs build, preserves its evidence, then runs audit")
    p.add_argument("--skip-build", action="store_true", help="Local audit only; not used by required CI")
    args = p.parse_args(argv)
    if args.skip_build and args.phase != "all":
        p.error("--skip-build cannot be combined with --phase")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    contract = validate()
    check_dependencies()
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True)
    if not re.search(r"\bversion 4\.35\.0\b", version):
        raise RuntimeError("Wrong Lean compiler: " + version)
    if args.phase in ("all", "build") and not args.skip_build:
        build_modules(contract, version, output)
    if args.phase in ("all", "audit"):
        audit_modules(contract, version, output, args.base_report, require_build=not args.skip_build)


if __name__ == "__main__":
    main()
