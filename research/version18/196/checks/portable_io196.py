"""Portable data authentication and output handling; no mathematical tests."""
import argparse
import hashlib
import json
import sys
from pathlib import Path

def inputs():
    if not __debug__:
        raise SystemExit("Run without -O; assertions are required.")
    parser = argparse.ArgumentParser(description="Replay the independent 198 to 196 exact audit.")
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--parent-table", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root, parent, output = (p.resolve() for p in (args.source_root, args.parent_table, args.output))
    code_root = Path(__file__).resolve().parents[1]
    if output.is_relative_to(root) or output == parent or output.is_relative_to(code_root):
        raise SystemExit("Output must be outside the source and checker directories and differ from the parent table.")
    if output.exists():
        raise SystemExit("Refusing to overwrite output.")
    pins_path = code_root / "provenance/SOURCE-PINS.json"
    if hashlib.sha256(pins_path.read_bytes()).hexdigest() != "e29aa9a32a69e8d2a6c36795b8f8e71bbdc9262817054e989018165c093eb63f":
        raise SystemExit("Source-pins digest mismatch.")
    pins = json.loads(pins_path.read_text(encoding="utf-8"))
    if pins["commit"] != "5c35db3253a70b0875acec4b451cdaac4da3c8fd":
        raise SystemExit("Wrong source commit.")
    expected = {r["path"] for r in pins["files"]}
    actual = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()}
    if actual != expected:
        raise SystemExit("Source file inventory mismatch.")
    for row in pins["files"]:
        path = (root / row["path"]).resolve()
        if not path.is_relative_to(root):
            raise SystemExit("Source path escapes source root.")
        data = path.read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if len(data) != row["bytes"] or hashlib.sha256(data).hexdigest() != row["sha256"] or blob != row["git_blob"]:
            raise SystemExit("Source digest mismatch: " + row["path"])
    parent_digest = hashlib.sha256(parent.read_bytes()).hexdigest()
    if parent_digest != "c55d7eefe41f62fee88b467e3ea8f6be8ba1e66f6a94b30eb74b39f6f6e7efad":
        raise SystemExit("Frozen Conant198 parent digest mismatch.")
    output.parent.mkdir(parents=True, exist_ok=True)
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    return root, parent, output
