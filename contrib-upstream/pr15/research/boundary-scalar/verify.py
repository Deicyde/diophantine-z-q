#!/usr/bin/env python3
"""Fresh native checks of the combined research contribution; no paranoid run."""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "lean"
PACKET = ROOT / "research/boundary-scalar"
MODULES = ["DerivativeSwitchBoundary", "BoundaryScalar", "BoundaryCupAdapter"]
DEFINITIONS = ["Research.DerivativeSwitch.AxesKernel", "Research.DerivativeSwitch.Volume.area",
               "Research.DerivativeSwitch.Volume.action", "Research.BoundaryScalar.axis",
               "Research.BoundaryScalar.singularNormal", "Research.BoundaryScalar.exchange",
               "Research.BoundaryScalar.finiteNormal", "Research.BoundaryCupAdapter.transportedPairing"]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    output = parser.parse_args().output.resolve()
    if output.exists():
        raise SystemExit("Output must be new")
    output.mkdir(parents=True)
    lib = output / "lib"
    (lib / "Research").mkdir(parents=True)
    commands = []

    def run(label, command, cwd=ROOT, env=None, expected=0):
        r = subprocess.run(command, cwd=cwd, env=env, capture_output=True)
        (output / (label + ".log")).write_bytes(r.stdout + r.stderr)
        commands.append({"label": label, "command": command,
                         "cwd": str(cwd.relative_to(ROOT)), "exit_code": r.returncode,
                         "expected_exit_code": expected})
        (output / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if r.returncode != expected:
            raise RuntimeError(f"{label}: expected {expected}, got {r.returncode}; see output log")
        return r.stdout

    config_path = PACKET / "verification/comparator.json"
    config = json.loads(config_path.read_text())
    targets = config["theorem_names"]
    if len(targets) != len(set(targets)) or len(targets) != 21:
        raise RuntimeError("Expected exactly 21 distinct selected declarations")
    if config["definition_names"] != [] or set(config["permitted_axioms"]) != ALLOWED:
        raise RuntimeError("Changed comparison/axiom policy")

    archive = PACKET / "inputs/diophantine_zq_complete_math_review_bundle_2026-11-08.zip"
    if sha(archive) != "a90ece63029cdbca8bb7db1871cc5325a6cd19b505e6ed53810ab17fb2e62bae":
        raise RuntimeError("Received archive differs")
    with ZipFile(archive) as z:
        if z.testzip() is not None:
            raise RuntimeError("Received archive CRC failure")
        for item in json.loads(z.read("FILE_MANIFEST.json"))["files"]:
            data = z.read(item["path"])
            if len(data) != item["bytes"] or hashlib.sha256(data).hexdigest() != item["sha256"]:
                raise RuntimeError("Received archive input mismatch")

    run("frozen-source-guard", [sys.executable, "-B", "scripts/check_lean.py"])
    run("audit-history", [sys.executable, "-B", "scripts/check_audit_history.py", "--self-test"])
    run("original-model", [sys.executable, "-B", "research/determinant-switch/check_local_model.py"])
    normal = run("boundary-model", [sys.executable, "-B", "research/boundary-scalar/check_boundary_scalar.py"])
    optimized = run("boundary-model-optimized", [sys.executable, "-B", "-O", "research/boundary-scalar/check_boundary_scalar.py"])
    if normal != optimized:
        raise RuntimeError("Optimized finite checker differs")

    spec = importlib.util.spec_from_file_location("frozen_checker", ROOT / "scripts/check_lean.py")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    sources = [PROJECT / f"Research/{name}.lean" for name in MODULES]
    for source in sources:
        code = checker.code_only(source.read_text())
        if re.search(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b", code) or "skipKernelTC" in code:
            raise RuntimeError(f"Disallowed proof escape: {source}")

    lock = json.loads((PROJECT / "lake-manifest.json").read_text())
    dependencies, libraries = [], []
    for package in lock["packages"]:
        folder = PROJECT / ".lake/packages" / package["name"]
        rev = subprocess.check_output(["git", "-C", str(folder), "rev-parse", "HEAD"], text=True).strip()
        if rev != package["rev"]:
            raise RuntimeError(f"Wrong dependency revision: {package['name']}")
        subprocess.run(["git", "-C", str(folder), "diff", "--quiet", "HEAD", "--"], check=True)
        dependencies.append({"name": package["name"], "revision": rev})
        library = folder / ".lake/build/lib/lean"
        if library.exists():
            libraries.append(library)

    version = run("lean-version", ["lean", "--version"], PROJECT).decode().strip()
    if "version 4.35.0," not in version:
        raise RuntimeError("Use pinned Lean 4.35.0")
    run("lake-version", ["lake", "--version"], PROJECT)
    env = os.environ.copy()
    env.pop("LEAN_SRC_PATH", None)
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in [lib, *libraries])
    base = ["lean", "-j1", "-Ddebug.skipKernelTC=false"]
    for module in MODULES:
        run("target-" + module, base + ["-o", str(lib / f"Research/{module}.olean"),
                                        f"Research/{module}.lean"], PROJECT, env)
    solution = output / "Solution.lean"
    solution.write_bytes((PACKET / "verification/Solution.lean").read_bytes())
    run("solution", base + ["-o", str(lib / "Solution.olean"), "Solution.lean"], output, env)
    auditor = output / "Axioms.lean"
    auditor.write_text("\n".join([
        "import Solution", "import Lean.Util.CollectAxioms",
        "set_option pp.universes true", "set_option pp.explicit true",
        *["#print " + name for name in DEFINITIONS],
        "open Lean Elab Command in", "run_cmd do",
        "  let names : Array Name := #[" + ", ".join("`" + n for n in targets) + "]",
        "  for name in names do",
        "    let declaration ← getConstInfo name",
        '    logInfo m!"STATEMENT {name}: {declaration.type}"',
        "    let axioms ← collectAxioms name",
        "    for ax in axioms do",
        "      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do",
        '        throwError "Unexpected axiom {ax} in {name}"',
        '    logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"',
        '  logInfo "AXIOM_AUDIT_PASS declarations=21"', ""]))
    audit = run("axioms-and-statements", base + [str(auditor)], PROJECT, env).decode()
    actual = {name: sorted(x.strip() for x in vals.split(",") if x.strip())
              for name, vals in re.findall(r"AXIOM_CHECK ([\w.]+): \[([^\]]*)\]", audit)}
    if set(actual) != set(targets) or any(set(xs) - ALLOWED for xs in actual.values()):
        raise RuntimeError("Incomplete or disallowed axiom coverage")
    if "AXIOM_AUDIT_PASS declarations=21" not in audit:
        raise RuntimeError("Missing successful axiom audit marker")
    inputs = [*sources, Path(__file__), config_path, archive,
              PROJECT / "lean-toolchain", PROJECT / "lakefile.toml", PROJECT / "lake-manifest.json",
              PACKET / "CONTRACT.md", PACKET / "DERIVATION.md", PACKET / "check_boundary_scalar.py"]
    result = {"status": "PASS", "profile": "development", "lean": version,
              "modules_freshly_compiled": MODULES, "selected_declarations": len(targets),
              "theorem_axioms": actual, "allowed_axioms": sorted(ALLOWED), "dependencies": dependencies,
              "paranoid": False, "native_export_replay": "NOT_RUN", "protected_comparator": "NOT_RUN",
              "external_checkers": "NOT_RUN", "arithmetic_tensor_compatibility": "OPEN",
              "dependency_cache": "Trusted pinned Mathlib master cache",
              "input_hashes": {str(p.relative_to(ROOT)): sha(p) for p in inputs},
              "artifact_sha256": {str(p.relative_to(lib)): sha(p) for p in lib.rglob('*.olean')}}
    (output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "selected_declarations": len(targets),
                      "paranoid": False, "output": str(output)}, indent=2))


if __name__ == "__main__":
    main()
