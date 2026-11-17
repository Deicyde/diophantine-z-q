#!/usr/bin/env python3
"""Check the separate research module with the pinned native Lean kernel.

Development scope only. Dependency caches are trusted; no --paranoid or external
checker execution is included. Refuse reuse of project compilation artifacts.
"""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "lean"
PREFIX = "Research.DerivativeSwitch."
THEOREMS = [PREFIX + name for name in [
    "finite_kernel_line", "singular_kernel_line", "boundary_images_meet_zero",
    "no_identity_strict_square", "Volume.area_action", "Volume.area_neg_one"]]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="A new evidence directory")
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        raise RuntimeError("Output must be new; old target artifacts are never reused")
    output.mkdir(parents=True)
    lib = output / "lib"
    (lib / "Research").mkdir(parents=True)
    commands = []

    def run(label, command, cwd=ROOT, env=None):
        result = subprocess.run(command, cwd=cwd, env=env, capture_output=True)
        (output / (label + ".log")).write_bytes(result.stdout + result.stderr)
        commands.append({"label": label, "command": command,
                         "cwd": str(cwd.relative_to(ROOT)), "exit_code": result.returncode})
        (output / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if result.returncode:
            raise RuntimeError(f"{label} failed; inspect {output / (label + '.log')}")
        return result.stdout.decode()

    # Frozen helpers remain a separate source-identity target, not coverage of this module.
    run("frozen-source-guard", [sys.executable, "-B", "scripts/check_lean.py"])
    run("audit-history", [sys.executable, "-B", "scripts/check_audit_history.py", "--self-test"])
    run("local-model", [sys.executable, "-B", "research/determinant-switch/check_local_model.py"])

    spec = importlib.util.spec_from_file_location("frozen_checker", ROOT / "scripts/check_lean.py")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    source = PROJECT / "Research/DerivativeSwitchBoundary.lean"
    code = checker.code_only(source.read_text())
    forbidden = r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b"
    if re.search(forbidden, code) or "skipKernelTC" in code:
        raise RuntimeError("Disallowed proof escape or admission in research source")

    lock = json.loads((PROJECT / "lake-manifest.json").read_text())
    dependencies, libraries = [], []
    for package in lock["packages"]:
        folder = PROJECT / ".lake/packages" / package["name"]
        revision = subprocess.check_output(["git", "-C", str(folder), "rev-parse", "HEAD"], text=True).strip()
        if revision != package["rev"]:
            raise RuntimeError(f"Dependency revision differs: {package['name']}")
        subprocess.run(["git", "-C", str(folder), "diff", "--quiet", "HEAD", "--"], check=True)
        dependencies.append({"name": package["name"], "revision": revision})
        library = folder / ".lake/build/lib/lean"
        if library.exists():
            libraries.append(library)
    version = run("lean-version", ["lean", "--version"], PROJECT).strip()
    if "version 4.35.0," not in version:
        raise RuntimeError("Use the pinned Lean 4.35.0 toolchain")
    run("lake-version", ["lake", "--version"], PROJECT)
    env = os.environ.copy()
    env.pop("LEAN_SRC_PATH", None)
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in [lib, *libraries])
    base = ["lean", "-j1", "-Ddebug.skipKernelTC=false"]
    run("target", base + ["-o", str(lib / "Research/DerivativeSwitchBoundary.olean"),
                          "Research/DerivativeSwitchBoundary.lean"], PROJECT, env)
    auditor = output / "Axioms.lean"
    auditor.write_text("\n".join([
        "import Research.DerivativeSwitchBoundary", "import Lean.Util.CollectAxioms",
        "set_option pp.universes true", "set_option pp.explicit true",
        "#print Research.DerivativeSwitch.AxesKernel",
        "#print Research.DerivativeSwitch.Volume.area",
        "#print Research.DerivativeSwitch.Volume.action",
        *["#print axioms " + name for name in THEOREMS],
        "open Lean Elab Command in", "run_cmd do",
        "  let names : Array Name := #[" + ", ".join("`" + n for n in THEOREMS) + "]",
        "  for name in names do",
        "    let declaration ← getConstInfo name",
        '    logInfo m!"STATEMENT {name}: {declaration.type}"',
        "    let axioms ← collectAxioms name",
        "    for ax in axioms do",
        "      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do",
        '        throwError "Unexpected axiom {ax} in {name}"',
        '    logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"',
        '  logInfo "AXIOM_AUDIT_PASS declarations=6"', ""]))
    audit = run("axioms-and-statements", base + [str(auditor)], PROJECT, env)
    if "AXIOM_AUDIT_PASS declarations=6" not in audit:
        raise RuntimeError("Incomplete axiom audit")
    actual = {}
    for name, values in re.findall(r"AXIOM_CHECK ([\w.]+): \[([^\]]*)\]", audit):
        actual[name] = sorted(x.strip() for x in values.split(",") if x.strip())
    if set(actual) != set(THEOREMS) or any(set(xs) - ALLOWED for xs in actual.values()):
        raise RuntimeError("Axiom output does not cover exactly the requested theorems")
    inputs = [source, PROJECT / "lean-toolchain", PROJECT / "lakefile.toml",
              PROJECT / "lake-manifest.json", PROJECT / "SOURCE_MANIFEST.json",
              Path(__file__), ROOT / "research/determinant-switch/CONTRACT.md",
              ROOT / "research/determinant-switch/check_local_model.py"]
    result = {"status": "PASS", "assurance_profile": "development",
              "lean": version, "dependencies": dependencies, "theorem_axioms": actual,
              "allowed_axioms": sorted(ALLOWED), "paranoid": False,
              "external_checkers": "NOT_RUN", "main_theorem_proved": False,
              "fresh_target_olean": True, "dependency_cache": "Trusted published prebuilt cache",
              "input_hashes": {str(p.relative_to(ROOT)): sha(p) for p in inputs},
              "artifact_sha256": sha(lib / "Research/DerivativeSwitchBoundary.olean"),
              "semantic_review": "See VERIFICATION.md; no independent acceptance claimed"}
    (output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "theorems": len(actual), "lean": version,
                      "paranoid": False, "output": str(output)}, indent=2))


if __name__ == "__main__":
    main()
