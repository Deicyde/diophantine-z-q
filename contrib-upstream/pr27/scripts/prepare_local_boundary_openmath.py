#!/usr/bin/env python3
"""Stage the frozen four-module packet for source-bound Open Math checking.

Offline preparation only: no dependency install, Lean run, or cloud dispatch.
Does not create a comparator challenge or change the reviewed mathematical files.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "research/local-boundary-interfaces"
CORE_MANIFEST = "ce59e6667e58c1858a0bb87830c35f4142dc1f69c805f2e4daaa169f130220e3"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="New directory; never overwritten")
    out = parser.parse_args().output.resolve()
    if out.exists():
        raise SystemExit("Output must be new")
    manifest = (PACKET / "MANIFEST.sha256").read_bytes()
    if sha(manifest) != CORE_MANIFEST:
        raise SystemExit("Frozen core manifest identity changed")
    for line in manifest.decode().splitlines():
        expected, name = line.split("  ", 1)
        source = (ROOT / name).resolve()
        if not source.is_relative_to(ROOT) or sha(source.read_bytes()) != expected:
            raise SystemExit("Frozen core input changed: " + name)
    origin = json.loads((PACKET / "ORIGIN.json").read_text())
    selection = json.loads((PACKET / "TARGETS.json").read_text())
    modules = [m["module"] for m in origin["modules"]]
    targets = selection["proof_roots"]
    if modules != selection["modules"] or len(modules) != 4 or len(targets) != 41 or len(set(targets)) != 41:
        raise SystemExit("Unexpected four-module / 41-root selection")
    files, sources = {}, {}
    for item in origin["modules"]:
        name = str(Path(item["path"]).relative_to("lean"))
        data = (ROOT / item["path"]).read_bytes()
        if sha(data) != item["sha256"]:
            raise SystemExit("Source identity mismatch: " + item["path"])
        files[name] = data
        sources[name] = {"source": item["path"], "sha256": sha(data), "transformation": "byte-identical"}
    for name in ("lean-toolchain", "lake-manifest.json"):
        data = (ROOT / "lean" / name).read_bytes()
        if sha(data) != origin["dependency_pin_files"]["lean/" + name]:
            raise SystemExit("Dependency pin drift: " + name)
        if name == "lake-manifest.json":
            lock = json.loads(data)
            lock["name"] = "local_boundary_verification"
            files[name] = (json.dumps(lock, indent=2) + "\n").encode()
            transform = "Only root package name changed; all nine dependency pins preserved"
        else:
            files[name] = data
            transform = "byte-identical"
        sources[name] = {"source": "lean/" + name, "sha256": sha(data), "transformation": transform}
    files["Packet.lean"] = ("\n".join("import " + m for m in modules) + "\n").encode()
    files["roots.txt"] = ("\n".join(targets) + "\n").encode()
    files["TARGETS.json"] = (PACKET / "TARGETS.json").read_bytes()
    files["lakefile.toml"] = ('''name = "local_boundary_verification"
version = "0.1.0"
defaultTargets = ["LocalBoundary"]
requiresModuleSystem = false
moreLeanArgs = ["-Ddebug.skipKernelTC=false"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.35.0"

[[lean_lib]]
name = "LocalBoundary"
roots = ''' + json.dumps(["Packet", *modules]) + "\n").encode()
    files["SOURCES.json"] = (json.dumps({"core_manifest_sha256": CORE_MANIFEST,
        "generator_sha256": sha(Path(__file__).read_bytes()), "sources": sources,
        "generated_support": ["Packet.lean", "roots.txt", "lakefile.toml"],
        "scope": "41 named roots and their transitive proof closure; no frozen-39 imports, challenge, or new theorem"}, indent=2) + "\n").encode()
    files["MANIFEST.sha256"] = "".join(sha(data) + "  " + name + "\n"
                                       for name, data in sorted(files.items())).encode()
    out.mkdir(parents=True)
    for name, data in files.items():
        dest = out / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
    print(json.dumps({"status": "PREPARED", "files": len(files), "proof_roots": len(targets),
                      "manifest_sha256": sha(files["MANIFEST.sha256"]),
                      "lean_executed": False, "paranoid": "NOT_RUN"}, indent=2))


if __name__ == "__main__":
    main()
