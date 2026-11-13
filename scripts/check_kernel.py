#!/usr/bin/env python3
"""Build the complete kernel project and check its exact proof contracts."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import time

from check_kernel_contract import ROOT, git, validate


def run(command, output, name, cwd=ROOT):
    start = time.monotonic()
    with (output / (name + ".log")).open("w", encoding="utf-8") as log:
        log.write(json.dumps(command) + "\n")
        log.flush()
        proc = subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, errors="replace")
        for line in proc.stdout:
            print(line, end="", flush=True)
            log.write(line)
        code = proc.wait()
    (output / (name + "-timing.json")).write_text(json.dumps({
        "seconds": round(time.monotonic() - start, 3), "exit_code": code}), encoding="utf-8")
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


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, default=ROOT / "build/kernel-ci")
    p.add_argument("--base-report", type=Path)
    p.add_argument("--skip-build", action="store_true", help="Local audit only; not used by required CI")
    args = p.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    contract = validate()
    check_dependencies()
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True)
    if not re.search(r"\bversion 4\.35\.0\b", version):
        raise RuntimeError("Wrong Lean compiler: " + version)
    if not args.skip_build:
        run(["lake", "build", "ZInQKernel", "GreenTaoVendor"], output, "root-build")
        # Explicit targets also build new Contrib files not imported by a root.
        names = sorted(contract["modules"])
        for i in range(0, len(names), 100):
            run(["lake", "build", *["+" + n for n in names[i:i+100]]], output, f"modules-{i//100}")
    run(["python", "-B", "scripts/check_target.py"], output, "frozen-target")
    if validate() != contract:
        raise RuntimeError("Source contract changed during compilation")
    check_dependencies()
    spec = dict(contract)
    spec["modules"] = sorted(contract["modules"])
    spec_path = output / "spec.json"
    spec_path.write_text(json.dumps(spec, indent=2), encoding="utf-8")
    run(["lake", "env", "lean", "--run", "scripts/audit_kernel.lean", str(spec_path),
         str(output / "audit.json")], output, "kernel-audit")
    report = json.loads((output / "audit.json").read_bytes())
    if validate() != contract:
        raise RuntimeError("Source contract changed during the audit")
    check_dependencies()
    report["head_sha"] = git(ROOT, "rev-parse", "HEAD").decode().strip()
    report["contract_sha256"] = contract["manifest_sha256"]
    report["compiler"] = version.strip()
    (output / "audit.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    progress(report, output, args.base_report)


if __name__ == "__main__":
    main()
