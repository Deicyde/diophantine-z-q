"""Remove cached artifacts for changed modules and all their importers before Lake builds."""

from pathlib import Path
import re
import subprocess

original = "0b1e1b711059bb15bbbac2ead386c3f49564a30b"
record = Path(__file__).with_name("trim-invalidate.txt")
paths = record.read_text().splitlines()
changed = set(subprocess.check_output(
    ["git", "diff", "--name-only", original, "HEAD", "--", "*.lean"], text=True
).splitlines())
assert len(changed) == 9 and len(paths) == len(set(paths)) == 171 and changed <= set(paths)
for path in paths:
    if not re.fullmatch(r"ZInQKernel/Contrib/(?:[A-Za-z0-9_]+/)*[A-Za-z0-9_]+\.lean", path):
        raise ValueError(f"unexpected module path: {path}")

removed = 0
for root in (Path(".lake/build/lib/lean"), Path(".lake/build/ir")):
    for path in paths:
        stem = root / path.removesuffix(".lean")
        for artifact in stem.parent.glob(stem.name + ".*"):
            if artifact.is_file() or artifact.is_symlink():
                artifact.unlink()
                removed += 1
print(f"Cleared {removed} compiled artifacts for {len(paths)} affected modules.")
