#!/usr/bin/env python3
"""Validate the kernel baseline and classify a diff against a trusted base.

A candidate's internally consistent manifest is NOT approval to change the
baseline. The protected reviewer must compare with the base commit. This
program never publishes an acceptance check.

`--write` regenerates the "files" hashes for a maintainer's statement or
infrastructure change: it rehashes every pinned file, registers new baseline
sources and drops deleted ones, and leaves targets, headline and exports alone.
The rewritten manifest still needs the same review as any other lock change.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path, PurePosixPath
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = "KERNEL_CONTRACT.json"
CONTRIB = "ZInQKernel/Contrib/"


def git(root, *args):
    return subprocess.run(["git", "-c", "safe.directory=" + str(root.resolve()), "-C", str(root), *args], check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def tracked(root):
    return [p.decode("utf-8") for p in git(root, "ls-files", "-z").split(b"\0") if p]


def valid_path(path):
    p = PurePosixPath(path)
    return (bool(path) and str(p) == path and not p.is_absolute()
            and ":" not in path and ".." not in p.parts and "\\" not in path)


def protected_source(path):
    """A baseline Lean source that the manifest must pin (contributions excepted)."""
    return (((path.startswith(("ZInQKernel/", "ThirdParty/", "lean/")) and path.endswith(".lean"))
             or path == "ZInQKernel.lean") and not path.startswith(CONTRIB))


def lean_modules(paths):
    result = {}
    for path in paths:
        if path == "ZInQKernel.lean" or path.startswith("ZInQKernel/"):
            module = path[:-5].replace("/", ".") if path.endswith(".lean") else None
        elif path.startswith("ThirdParty/GreenTao/") and path.endswith(".lean"):
            module = path[len("ThirdParty/GreenTao/"):-5].replace("/", ".")
        elif path == "lean/ZInQ.lean" or path.startswith("lean/ZInQ/"):
            module = path[len("lean/"):-5].replace("/", ".") if path.endswith(".lean") else None
        else:
            module = None
        if module:
            if module in result:
                raise ValueError("Duplicate module: " + module)
            result[module] = path
    if "ZInQKernel" not in result or "Submission" not in result:
        raise ValueError("Missing required kernel/vendor root")
    return result


def validate(root=ROOT):
    manifest = json.loads((root / MANIFEST).read_bytes())
    if manifest.get("schema") != "kernel-contract/v1":
        raise ValueError("Unsupported kernel contract")
    paths = tracked(root)
    files = manifest["files"]
    for path, digest in files.items():
        if not valid_path(path) or not isinstance(digest, str) or not re.fullmatch(r"[a-f0-9]{64}", digest):
            raise ValueError("Invalid manifest entry: " + path)
        full = root / path
        if (full.is_symlink() or not full.is_file() or path not in paths
                or not full.resolve().is_relative_to(root.resolve())
                or any(p.is_symlink() for p in full.parents if p != root and p.is_relative_to(root))):
            raise ValueError("Missing/untracked/symlinked contract file: " + path)
        if sha(full.read_bytes()) != digest:
            raise ValueError("Changed contract file requires statement/infrastructure review: " + path)
    # Pin the entire existing mathematical baseline. New contribution modules
    # can be checked without silently extending the meaning of locked targets.
    for path in paths:
        if protected_source(path) and path not in files:
            raise ValueError("Unregistered baseline source: " + path)
        if path.startswith(CONTRIB):
            full = root / path
            if not path.endswith(".lean") or full.is_symlink():
                raise ValueError("Contribution source must be an ordinary .lean file: " + path)
        if path.endswith(".lean") or PurePosixPath(path).name in ("lakefile.toml", "lakefile.lean"):
            # Intentionally includes comments. This is a bypass-option denylist,
            # not a textual proof-hole detector.
            if "skipKernelTC" in (root / path).read_text(encoding="utf-8"):
                raise ValueError("Kernel-check bypass option in tracked source: " + path)
    targets = manifest["targets"]
    names = [t["declaration"] for t in targets]
    if not names or len(names) != len(set(names)):
        raise ValueError("Empty/duplicate target list")
    for target in targets:
        if target["source"] not in files:
            raise ValueError("Unpinned target source: " + target["source"])
    providers = [t["provider"] for t in targets]
    if len(providers) != len(set(providers)):
        raise ValueError("Duplicate proof provider")
    return {"schema": "kernel-contract-check/v1", "manifest_sha256": sha((root / MANIFEST).read_bytes()),
            "files": len(files), "modules": lean_modules(paths), "targets": targets,
            "headline": manifest["headline"], "exports": manifest["exports"],
            "status": "valid_candidate_contract",
            "acceptance": False}


def classify(root, base_ref):
    # The caller of a protected gate must execute its trusted checker, not a
    # checker chosen by the candidate. Resolve refs to immutable commits first.
    base = git(root, "rev-parse", "--verify", base_ref + "^{commit}").decode().strip()
    head = git(root, "rev-parse", "HEAD").decode().strip()
    try:
        baseline = json.loads(git(root, "show", base + ":" + MANIFEST))
    except subprocess.CalledProcessError:
        return {"route": "baseline_review", "base": base, "head": head,
                "reason": "Trusted base has no kernel contract", "acceptance": False}
    changed = [x.decode() for x in git(root, "diff", "--name-only", "-z", base, head).split(b"\0") if x]
    # Full baseline hashes, manifest, and checker inputs must be identical to
    # the trusted base even when a candidate updates hashes self-consistently.
    locked = {MANIFEST, *baseline["files"]}
    lock_changed = sorted(locked.intersection(changed))
    pure = bool(changed) and not lock_changed and all(p.startswith(CONTRIB) and p.endswith(".lean") for p in changed)
    return {"route": "proof_only_astra_review" if pure else "statement_or_infrastructure_review",
            "base": base, "head": head, "changed": changed, "lock_changed": lock_changed,
            "acceptance": False}


def regenerate(root=ROOT):
    """Rewrite the manifest's file hashes; return what changed."""
    path = root / MANIFEST
    manifest = json.loads(path.read_bytes())
    paths = set(tracked(root))
    old = manifest["files"]
    pinned = {p for p in old if p in paths} | {p for p in paths if protected_source(p)}
    files = {p: sha((root / p).read_bytes()) for p in sorted(pinned)}
    manifest["files"] = files
    path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n")
    return {"added": sorted(set(files) - set(old)), "removed": sorted(set(old) - set(files)),
            "changed": sorted(p for p in files if p in old and old[p] != files[p])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--base-ref")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--write", action="store_true",
                        help="regenerate the file hashes in the manifest (maintainers)")
    args = parser.parse_args()
    if args.write:
        changes = regenerate(args.root)
        for kind in ("added", "removed", "changed"):
            for p in changes[kind]:
                print(f"{kind}: {p}", file=sys.stderr)
    result = validate(args.root)
    if args.base_ref:
        result["review"] = classify(args.root, args.base_ref)
    raw = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(raw, encoding="utf-8")
    print(raw, end="")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, subprocess.CalledProcessError) as error:
        print("Kernel contract rejected: " + str(error), file=sys.stderr)
        sys.exit(1)
