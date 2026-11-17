#!/usr/bin/env python3
"""Make a new, deterministic handoff project; never execute Lean or use network."""

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
PACKET = ROOT / "research/determinant-switch"
TEMPLATES = PACKET / "verification"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        raise SystemExit("Output must be new; existing handoffs are never overwritten")

    # Explicit source/output list. Copied sources remain byte-identical.
    copies = {
        "Research/DerivativeSwitchBoundary.lean": ROOT / "lean/Research/DerivativeSwitchBoundary.lean",
        "lean-toolchain": ROOT / "lean/lean-toolchain",
        "Challenge.lean": TEMPLATES / "Challenge.lean",
        "lakefile.toml": TEMPLATES / "lakefile.toml",
        "comparator.json": TEMPLATES / "comparator.json",
        "README.md": TEMPLATES / "README.md",
        "CONTRACT.md": PACKET / "CONTRACT.md",
    }
    files = {dest: source.read_bytes() for dest, source in copies.items()}
    sources = {dest: {"source": str(source.relative_to(ROOT)), "sha256": sha(files[dest]),
                      "transformation": "byte-identical copy"}
               for dest, source in copies.items()}
    original_lock = (ROOT / "lean/lake-manifest.json").read_bytes()
    lock = json.loads(original_lock)
    lock["name"] = "derivative_switch_verification"
    files["lake-manifest.json"] = (json.dumps(lock, indent=2) + "\n").encode()
    sources["lake-manifest.json"] = {
        "source": "lean/lake-manifest.json", "sha256": sha(original_lock),
        "transformation": "change only root name; serialize as UTF-8, indent=2, final LF",
    }
    sources["generator"] = {"source": str(Path(__file__).relative_to(ROOT)),
                            "sha256": sha(Path(__file__).read_bytes())}
    files["SOURCES.json"] = (json.dumps(sources, indent=2, sort_keys=True) + "\n").encode()
    files["MANIFEST.sha256"] = "".join(
        f"{sha(data)}  {name}\n" for name, data in sorted(files.items())).encode()
    output.mkdir(parents=True)
    for name, data in files.items():
        destination = output / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
    print(json.dumps({"output": str(output), "files": len(files),
                      "manifest_sha256": sha(files["MANIFEST.sha256"]),
                      "executed_lean": False}, indent=2))


if __name__ == "__main__":
    main()
