#!/usr/bin/env python3
"""Fresh native Lean build, statement dump and transitive-axiom audit.

Adapted for this selection from the two research runners recorded in ORIGIN.json.
Run from the repository root; OUTPUT must be a new directory below lean/.checks/.
Cached pinned dependencies are trusted imports, not rebuilt or independently replayed.
"""
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "lean"
PACKET = Path(__file__).resolve().parent
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: python3 -B research/local-boundary-interfaces/verify_native.py lean/.checks/NEW_RUN")
    output = (ROOT / sys.argv[1]).resolve()
    if not output.is_relative_to(PROJECT / ".checks"):
        raise SystemExit("OUTPUT must be below lean/.checks/")
    output.mkdir(parents=True, exist_ok=False)
    relative_output = output.relative_to(PROJECT)
    lib = relative_output / "lib"
    (PROJECT / lib / "Research/DerivativeSwitch").mkdir(parents=True)
    origin = json.loads((PACKET / "ORIGIN.json").read_text())
    selection = json.loads((PACKET / "TARGETS.json").read_text())
    modules = selection["modules"]
    targets = selection["proof_roots"]
    if len(targets) != len(set(targets)) or set(selection["permitted_axioms"]) != ALLOWED:
        raise RuntimeError("Invalid target or axiom selection")
    if modules != [m["module"] for m in origin["modules"]]:
        raise RuntimeError("Module selection differs from origin")
    for entry in origin["modules"]:
        data = (ROOT / entry["path"]).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if sha(ROOT / entry["path"]) != entry["sha256"] or blob != entry["source_blob"]:
            raise RuntimeError("Source drift: " + entry["path"])
    for name, digest in origin["dependency_pin_files"].items():
        if sha(ROOT / name) != digest:
            raise RuntimeError("Dependency pin drift: " + name)
    input_paths = [ROOT / m["path"] for m in origin["modules"]]
    input_paths += [ROOT / name for name in origin["dependency_pin_files"]]
    input_paths += [PACKET / name for name in
                    ("ORIGIN.json", "TARGETS.json", "README.md", "APPLICATION.md", "verify_native.py")]
    snapshot = lambda: {str(p.relative_to(ROOT)): sha(p) for p in input_paths}
    before = snapshot()
    commands = []

    def run(label, args, env=None):
        result = subprocess.run(args, cwd=PROJECT, env=env, capture_output=True)
        (output / (label + ".stdout.txt")).write_bytes(result.stdout)
        (output / (label + ".stderr.txt")).write_bytes(result.stderr)
        commands.append({"label": label, "command": args, "cwd": "lean", "exit_code": result.returncode})
        (output / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if result.returncode:
            raise RuntimeError(f"{label} failed; see {output.relative_to(ROOT)}")
        return result.stdout.decode()

    libraries, dependencies = [], []
    lock = json.loads((PROJECT / "lake-manifest.json").read_text())
    for package in lock["packages"]:
        folder = PROJECT / ".lake/packages" / package["name"]
        rev = subprocess.check_output(["git", "-C", str(folder), "rev-parse", "HEAD"], text=True).strip()
        if rev != package["rev"]:
            raise RuntimeError("Dependency revision drift: " + package["name"])
        subprocess.run(["git", "-C", str(folder), "diff", "--quiet", "HEAD", "--"], check=True)
        cache = Path(".lake/packages") / package["name"] / ".lake/build/lib/lean"
        if (PROJECT / cache).is_dir():
            libraries.append(cache)
        dependencies.append({"name": package["name"], "revision": rev,
                             "tracked_source_clean": True, "cache_present": (PROJECT / cache).is_dir()})
    version = run("lean-version", ["lean", "--version"]).strip()
    if "version 4.35.0," not in version or "eb6cafb" not in version:
        raise RuntimeError("Wrong Lean version")
    run("lake-version", ["lake", "--version"])
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], cwd=PROJECT, text=True).strip())
    executable_hashes = {name: sha(prefix / "bin" / name) for name in ("lean", "lake")}
    env = os.environ.copy()
    env.pop("LEAN_SRC_PATH", None)
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in [lib, *libraries])
    base = ["lean", "-j1", "-Ddebug.skipKernelTC=false"]
    for module in modules:
        source = Path(*module.split(".")).with_suffix(".lean")
        run(module.rsplit(".", 1)[-1], base + ["-o", str(lib / source.with_suffix(".olean")), str(source)], env)
    audit = relative_output / "Audit.lean"
    (PROJECT / audit).write_text("\n".join([
        *["import " + name for name in modules], "import Lean.Util.CollectAxioms",
        "set_option pp.universes true", "set_option pp.explicit false",
        "set_option pp.deepTerms true", "set_option pp.maxSteps 1000000",
        *["#print " + name for name in selection["definitions_to_print"]],
        "open Lean Elab Command in", "run_cmd do",
        "  let names : Array Name := #[" + ", ".join("`" + name for name in targets) + "]",
        "  for name in names do",
        "    let declaration ← getConstInfo name",
        '    logInfo m!"STATEMENT {name}: {declaration.type}"',
        "    let axioms ← collectAxioms name",
        "    for ax in axioms do",
        "      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do",
        '        throwError "Unexpected axiom {ax} in {name}"',
        '    logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"',
        f'  logInfo "AXIOM_AUDIT_PASS declarations={len(targets)}"', ""]))
    printed = run("axioms-and-statements", base + [str(audit)], env)
    actual = {name: sorted(x.strip() for x in values.split(",") if x.strip())
              for name, values in re.findall(r"AXIOM_CHECK ([\w.]+): \[([^\]]*)\]", printed)}
    if set(actual) != set(targets) or any(set(a) - ALLOWED for a in actual.values()):
        raise RuntimeError("Incomplete or unexpected axiom audit")
    after = snapshot()
    if before != after:
        raise RuntimeError("Inputs changed during native verification")
    result = {
        "status": "PASS", "profile": "development", "lean": version,
        "platform": platform.platform(), "python": platform.python_version(),
        "executable_sha256": executable_hashes,
        "modules_freshly_compiled": modules, "proof_roots": targets, "theorem_axioms": actual,
        "permitted_axioms": sorted(ALLOWED), "dependencies": dependencies,
        "dependency_cache_trust": "Existing pinned dependency caches and Lean standard library imported; not source-rebuilt or independently replayed. Clean tracked package sources do not authenticate cached binaries.",
        "lean_path": env["LEAN_PATH"], "lean_src_path": "UNSET",
        "input_hashes_before": before, "input_hashes_after": after,
        "artifact_hashes": {str(p.relative_to(PROJECT / lib)): sha(p) for p in sorted((PROJECT / lib).rglob("*.olean"))},
        "protected_comparison": "NOT_RUN", "export_replay": "NOT_RUN",
        "external_checkers": "NOT_RUN", "paranoid": "NOT_RUN",
        "arithmetic_galois_selmer_instance": "NOT_FORMALIZED_BY_THIS_PACKET",
    }
    (output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "proof_roots": len(targets), "output": str(output.relative_to(ROOT))}))


if __name__ == "__main__":
    main()
