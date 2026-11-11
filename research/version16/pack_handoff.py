"""Build a cumulative Version 16 handoff without modifying prior archives."""
import argparse
import hashlib
import json
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE_SHA = "93766200f2a2893e82c9d6e1839956f2d9508a6eeb2ebe082251870e35f3900d"


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--previous", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    if args.output.exists():
        raise ValueError("Refusing to overwrite an existing archive")
    if sha(args.previous) != BASE_SHA:
        raise ValueError("Wrong Version 15 archive")
    manifest_path = ROOT / "research/version16/MANIFEST.json"
    manifest = json.loads(manifest_path.read_bytes())
    records = list(manifest["files"])
    records.append({"path": "research/version16/MANIFEST.json",
                    "sha256": sha(manifest_path),
                    "bytes": manifest_path.stat().st_size})
    base = json.loads((ROOT / "research/version16/HANDOFF-BASE.json").read_bytes())
    selected = {item["path"] for item in records}
    for name in base["postpublication_paths"] + [".gitattributes", "SHA256SUMS"]:
        if name not in selected:
            target = (ROOT / name).resolve()
            if not target.is_relative_to(ROOT):
                raise ValueError("Postpublication path outside repository")
            records.append({"path": name, "sha256": sha(target),
                            "bytes": target.stat().st_size})
            selected.add(name)
    for item in records:
        f = (ROOT / item["path"]).resolve()
        if not f.is_relative_to(ROOT) or sha(f) != item["sha256"]:
            raise ValueError("Invalid current file: " + item["path"])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(args.output, "w", allowZip64=True) as z:
        z.write(args.previous, "historical/z-in-q-version15-cumulative.zip",
                compress_type=zipfile.ZIP_STORED)
        for item in records:
            z.write(ROOT / item["path"], "overlay/" + item["path"],
                    compress_type=zipfile.ZIP_DEFLATED)
        z.writestr("OVERLAY-MANIFEST.json", json.dumps(records, indent=2) + "\n")
        z.writestr("README.txt", "Version 16 cumulative research handoff\n\n"
            "Preserve the historical Version 15 archive unchanged. Reconstruct its\n"
            "repository according to its own instructions, then apply overlay/\n"
            "without removing other files. This overlay includes the intervening\n"
            "postpublication documentation changes and the Version 16 correction.\n"
            "It contains no conversation transcript or Busy Beaver draft.\n"
            "Read research/version16/README.md and FINDINGS.json for review scope.\n")
    with zipfile.ZipFile(args.output) as z:
        for item in records:
            if hashlib.sha256(z.read("overlay/" + item["path"])).hexdigest() != item["sha256"]:
                raise ValueError("Archive readback failed")
    print(json.dumps({"archive": args.output.name, "sha256": sha(args.output),
                      "bytes": args.output.stat().st_size,
                      "overlay_files": len(records),
                      "previous_sha256": BASE_SHA}, indent=2))


if __name__ == "__main__":
    main()
