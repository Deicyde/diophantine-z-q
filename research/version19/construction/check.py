"""Authenticate the selected inputs, then run the independent finite checks."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
manifest = json.loads((ROOT/'INPUTS.json').read_bytes())
seen = set()
for item in manifest['files']:
    name = item['path']
    path = ROOT/name
    assert name not in seen and path.resolve().is_relative_to(ROOT.resolve())
    seen.add(name)
    data = path.read_bytes()
    assert len(data) == item['bytes'], name
    assert hashlib.sha256(data).hexdigest() == item['sha256'], name
for script in ['verify195.py', 'verify250.py', 'check_interfaces.py',
               'check_printed.py', 'plain-text/verify.py']:
    subprocess.run([sys.executable, '-B', str(ROOT/script)], cwd=REPO, check=True)
print('Version 19 finite checks passed. Arithmetic and source-application proofs are reviewed separately.')
