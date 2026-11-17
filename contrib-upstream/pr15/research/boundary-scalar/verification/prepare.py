#!/usr/bin/env python3
"""Generate a fresh combined Open Math project from committed source inputs."""

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PACKET = ROOT / "research/boundary-scalar"
TEMPLATES = PACKET / "verification"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    output = parser.parse_args().output.resolve()
    if output.exists():
        raise SystemExit("Output must be new")
    copies = {
        "Research/DerivativeSwitchBoundary.lean": ROOT / "lean/Research/DerivativeSwitchBoundary.lean",
        "Research/BoundaryScalar.lean": ROOT / "lean/Research/BoundaryScalar.lean",
        "Research/BoundaryCupAdapter.lean": ROOT / "lean/Research/BoundaryCupAdapter.lean",
        "lean-toolchain": ROOT / "lean/lean-toolchain",
        "Solution.lean": TEMPLATES / "Solution.lean",
        "Challenge.lean": TEMPLATES / "Challenge.lean",
        "Challenge/Original.lean": TEMPLATES / "Challenge/Original.lean",
        "Challenge/Matrix.lean": TEMPLATES / "Challenge/Matrix.lean",
        "Challenge/Cup.lean": TEMPLATES / "Challenge/Cup.lean",
        "lakefile.toml": TEMPLATES / "lakefile.toml",
        "comparator.json": TEMPLATES / "comparator.json",
        "README.md": TEMPLATES / "README.md",
        "CONTRACT.md": PACKET / "CONTRACT.md",
        "DERIVATION.md": PACKET / "DERIVATION.md",
    }
    files = {name: source.read_bytes() for name, source in copies.items()}
    sources = {name: {"source": str(source.relative_to(ROOT)), "sha256": sha(files[name]),
                      "transformation": "byte-identical copy"}
               for name, source in copies.items()}
    original = (ROOT / "lean/lake-manifest.json").read_bytes()
    lock = json.loads(original)
    lock["name"] = "boundary_scalar_verification"
    files["lake-manifest.json"] = (json.dumps(lock, indent=2) + "\n").encode()
    sources["lake-manifest.json"] = {
        "source": "lean/lake-manifest.json", "sha256": sha(original),
        "transformation": "change only root name; UTF-8 JSON indent=2 and final LF"}
    sources["generator"] = {"source": str(Path(__file__).relative_to(ROOT)),
                            "sha256": sha(Path(__file__).read_bytes())}
    files["SOURCES.json"] = (json.dumps(sources, indent=2, sort_keys=True) + "\n").encode()
    files["MANIFEST.sha256"] = "".join(
        f"{sha(data)}  {name}\n" for name, data in sorted(files.items())).encode()
    output.mkdir(parents=True)
    for name, data in files.items():
        target = output / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    print(json.dumps({"output": str(output), "files": len(files),
                      "manifest_sha256": sha(files["MANIFEST.sha256"]),
                      "executed_lean": False}, indent=2))


if __name__ == "__main__":
    main()
