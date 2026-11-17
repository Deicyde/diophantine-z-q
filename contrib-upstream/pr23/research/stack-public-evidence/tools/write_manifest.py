"""Write MANIFEST.json: path, bytes and SHA-256 of every file in the packet except itself.

    python3 -B tools/write_manifest.py PACKET_DIR
"""
import hashlib, json, sys
from pathlib import Path

root = Path(sys.argv[1])
files = []
for p in sorted(root.rglob('*')):
    rel = str(p.relative_to(root))
    if p.is_file() and rel != 'MANIFEST.json' and '__pycache__' not in rel:
        b = p.read_bytes()
        files.append({'path': rel, 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()})
man = {'format': 'stack-public-evidence-manifest-v1',
       'scope': 'Every file in research/stack-public-evidence except MANIFEST.json itself. Paths are relative to that directory.',
       'fileCount': len(files), 'totalBytes': sum(f['bytes'] for f in files), 'files': files}
(root / 'MANIFEST.json').write_text(json.dumps(man, indent=1) + '\n')
print(len(files), man['totalBytes'])
