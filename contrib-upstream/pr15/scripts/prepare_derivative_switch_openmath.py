#!/usr/bin/env python3
"""Prepare a frozen research project from a repository checkout, offline.

This does not install dependencies, invoke Lean, run --paranoid, or dispatch a
cloud job. Open Math performs those operations after pulling the repository.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
PACKETS = {
    "six-lemma": {
        "path": "research/determinant-switch",
        "source_commit": "2c15940380520d6b6de72c2a1b6700ed192a7a87",
        "manifest": "de9e04423f3ccafa9690e6ff53c1f0bb79f5f91406ee3e4e89246ce2cf97fa12",
        "project_manifest": "e37368316a682d30f9358d7cf1c1ebd01e622e7896c99ca020ae5f94288f6188",
        "output": "lean/.checks/openmath-derivative-switch",
        "targets": 6,
    },
    "boundary-scalar": {
        "path": "research/boundary-scalar",
        "source_commit": "7ca086adf4298e2b611b9fa0b954eab838873bf3",
        "manifest": "8696323b0d1bb78e68ba4daea0437f38dde4ff3be8281e3856712a5f5369dba6",
        "project_manifest": "fa7749aa918702ddb8f3694641839a1f751e2b377784c153e3332196076fc171",
        "output": "lean/.checks/openmath-boundary-scalar",
        "targets": 21,
    },
    "scalar-ratio": {
        "path": "research/scalar-ratio",
        "source_commit": "3d2243ff141f9681fbd6a659ca28ffddfae9b000",
        "manifest": "d313ec3ff5ad0e91d555d26b2beef6ad401d7e9c86cdfe77adbe119062498610",
        "project_manifest": "117f9ca2c28c42e45198f790dd8c3f324e1bed9d3af11ea9707575363304b811",
        "output": "lean/.checks/openmath-scalar-ratio",
        "targets": 39,
    },
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest(manifest, base, expected):
    if digest(manifest) != expected:
        raise SystemExit(f"Frozen manifest changed: {manifest}")
    count = 0
    for line in manifest.read_text().splitlines():
        wanted, relative = line.split("  ", 1)
        path = (base / relative).resolve()
        if not path.is_relative_to(base.resolve()) or not path.is_file():
            raise SystemExit(f"Missing or outside-root manifest input: {relative}")
        if digest(path) != wanted:
            raise SystemExit(f"Frozen input changed: {relative}")
        count += 1
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", choices=sorted(PACKETS), default="scalar-ratio",
                        help="The current scalar-ratio project or an explicitly selected earlier freeze")
    parser.add_argument("--output", type=Path,
                        help="New output directory, relative to repository root unless absolute")
    args = parser.parse_args()
    plan = PACKETS[args.packet]
    packet = ROOT / plan["path"]
    output = (ROOT / (args.output or plan["output"])).resolve()
    if output.exists():
        raise SystemExit("Output must be new; choose another --output directory")
    prerequisite_count = 0
    if args.packet in {"boundary-scalar", "scalar-ratio"}:
        old = PACKETS["six-lemma"]
        prerequisite_count = check_manifest(ROOT / old["path"] / "MANIFEST.sha256", ROOT,
                                            old["manifest"])
    if args.packet == "scalar-ratio":
        prior = PACKETS["boundary-scalar"]
        prerequisite_count += check_manifest(ROOT / prior["path"] / "MANIFEST.sha256", ROOT,
                                             prior["manifest"])
    count = check_manifest(packet / "MANIFEST.sha256", ROOT, plan["manifest"])
    checkout = subprocess.check_output(
        ["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()
    generator = packet / "verification/prepare.py"
    subprocess.run([sys.executable, "-B", str(generator), "--output", str(output)],
                   check=True, cwd=ROOT)
    generated_count = check_manifest(output / "MANIFEST.sha256", output,
                                     plan["project_manifest"])
    receipt = {
        "status": "PREPARED_FROM_REPOSITORY",
        "checkout_commit": checkout,
        "packet": args.packet,
        "selected_declarations": plan["targets"],
        "reviewed_source_commit": plan["source_commit"],
        "prerequisite_inputs_checked": prerequisite_count,
        "packet_manifest_sha256": plan["manifest"],
        "packet_inputs_checked": count,
        "generated_manifest_sha256": plan["project_manifest"],
        "generated_inputs_checked": generated_count,
        "preparation_script_sha256": digest(Path(__file__).resolve()),
        "lean_invoked": False,
        "network_used": False,
        "paranoid_run": "NOT_RUN; owned by Open Math in the cloud",
        "cloud_command": ["lake", "comparator", "--config", "comparator.json", "--paranoid"],
    }
    (output / "OPENMATH_PREPARATION.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
