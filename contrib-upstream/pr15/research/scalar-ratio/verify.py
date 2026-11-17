#!/usr/bin/env python3
"""Fresh native checks of the combined scalar-ratio contribution; no paranoid run."""

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
PACKET = ROOT / "research/scalar-ratio"
MODULES = ['DerivativeSwitchBoundary', 'BoundaryScalar', 'BoundaryCupAdapter', 'DerivativeSwitch.Coordinate', 'DerivativeSwitch.CommonStrict', 'DerivativeSwitch.UnitCriterion', 'DerivativeSwitch.BoundaryCup']
DEFINITIONS = ["Research.DerivativeSwitch.ScalarRatio." + name for name in
               ["tensor", "HasCoordinate", "normal", "Index", "Local", "join", "pairCols", "area",
                "cycle", "frame", "target", "matrixUnit", "CommonStrictData",
                "CommonStrictData.delta", "CommonStrictData.eta", "CommonStrictData.a",
                "CommonStrictData.b", "CommonStrictData.theta", "CommonStrictData.qF", "CommonStrictData.qS", "unitValue",
                "UnitRelated", "finiteFormula", "singularFormula", "beta", "BoundaryCupIdentity"]]
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
    if len(targets) != len(set(targets)) or len(targets) != 39:
        raise RuntimeError("Expected exactly 39 distinct selected declarations")
    if config["definition_names"] != [] or set(config["permitted_axioms"]) != ALLOWED:
        raise RuntimeError("Changed comparison/axiom policy")

    archive = PACKET / "inputs/diophantine_zq_scalar_ratio_milestone_2026-11-08.zip"
    if sha(archive) != "f68a88c8c69a7a971666d399f74427dea292ddbc1653c2d40debfda8f0a65e8b":
        raise RuntimeError("Received archive differs")
    with ZipFile(archive) as z:
        if z.testzip() is not None:
            raise RuntimeError("Received archive CRC failure")
        rows = z.read("scalar_ratio_milestone/MANIFEST.sha256").decode().splitlines()
        if len(rows) != 20:
            raise RuntimeError("Received manifest inventory differs")
        for row in rows:
            wanted, relative = row.split("  ", 1)
            if hashlib.sha256(z.read("scalar_ratio_milestone/" + relative)).hexdigest() != wanted:
                raise RuntimeError("Received archive input mismatch")
    for folder, expected in [("determinant-switch", "de9e04423f3ccafa9690e6ff53c1f0bb79f5f91406ee3e4e89246ce2cf97fa12"),
                             ("boundary-scalar", "8696323b0d1bb78e68ba4daea0437f38dde4ff3be8281e3856712a5f5369dba6")]:
        manifest = ROOT / "research" / folder / "MANIFEST.sha256"
        if sha(manifest) != expected:
            raise RuntimeError("Prior frozen manifest changed")
        for row in manifest.read_text().splitlines():
            expected_hash, relative = row.split("  ", 1)
            path = (ROOT / relative).resolve()
            if not path.is_relative_to(ROOT) or sha(path) != expected_hash:
                raise RuntimeError("Prior frozen source changed: " + relative)
    run("frozen-source-guard", [sys.executable, "-B", "scripts/check_lean.py"])
    run("audit-history", [sys.executable, "-B", "scripts/check_audit_history.py", "--self-test"])
    run("original-model", [sys.executable, "-B", "research/determinant-switch/check_local_model.py"])
    normal = run("boundary-model", [sys.executable, "-B", "research/scalar-ratio/tests/check_milestone.py"])
    optimized = run("boundary-model-optimized", [sys.executable, "-B", "-O", "research/scalar-ratio/tests/check_milestone.py"])
    if normal != optimized:
        raise RuntimeError("Optimized finite checker differs")

    spec = importlib.util.spec_from_file_location("frozen_checker", ROOT / "scripts/check_lean.py")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    sources = [PROJECT / ("Research/" + name.replace(".", "/") + ".lean") for name in MODULES]
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
    if "version 4.35.0," not in version or "eb6cafb" not in version:
        raise RuntimeError("Use pinned Lean 4.35.0")
    run("lake-version", ["lake", "--version"], PROJECT)
    env = os.environ.copy()
    env.pop("LEAN_SRC_PATH", None)
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in [lib, *libraries])
    base = ["lean", "-j1", "-Ddebug.skipKernelTC=false"]
    for module in MODULES:
        relative = Path("Research") / (module.replace(".", "/") + ".lean")
        artifact = lib / relative.with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        run("target-" + module, base + ["-o", str(artifact), str(relative)], PROJECT, env)
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
        '  logInfo "AXIOM_AUDIT_PASS declarations=39"', ""]))
    audit = run("axioms-and-statements", base + [str(auditor)], PROJECT, env).decode()
    actual = {name: sorted(x.strip() for x in vals.split(",") if x.strip())
              for name, vals in re.findall(r"AXIOM_CHECK ([\w.]+): \[([^\]]*)\]", audit)}
    if set(actual) != set(targets) or any(set(xs) - ALLOWED for xs in actual.values()):
        raise RuntimeError("Incomplete or disallowed axiom coverage")
    if "AXIOM_AUDIT_PASS declarations=39" not in audit:
        raise RuntimeError("Missing successful axiom audit marker")
    inputs = [*sources, Path(__file__), config_path, archive,
              PROJECT / "lean-toolchain", PROJECT / "lakefile.toml", PROJECT / "lake-manifest.json",
              PACKET / "CONTRACT.md", PACKET / "DERIVATION.md", PACKET / "tests/check_milestone.py", PACKET / "tests/exact_matrix.py"]
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
