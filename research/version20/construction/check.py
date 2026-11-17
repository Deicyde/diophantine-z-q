"""Authenticate the selected inputs and run the Version 20 finite checks."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
manifest = json.loads((ROOT / 'INPUTS.json').read_bytes())
seen = set()
for item in manifest['files']:
    name = item['path']
    path = ROOT / name
    assert name not in seen and path.resolve().is_relative_to(ROOT.resolve())
    seen.add(name)
    raw = path.read_bytes()
    assert len(raw) == item['bytes'], name
    assert hashlib.sha256(raw).hexdigest() == item['sha256'], name

# The old inputs and checkers are immutable. The two strengthened checks live here.
commands = [
    REPO / 'research/version19/construction/check.py',
    ROOT / 'verify250_retained.py',
    ROOT / 'verify247.py',
    ROOT / 'check_printed.py',
]
for script in commands:
    subprocess.run([sys.executable, '-B', str(script)], cwd=REPO, check=True)

print('Version 20 finite checks passed. Arithmetic proofs and release acceptance require separate review.')
