#!/usr/bin/env python3
"""Prepare retained-export comparator inputs offline; never invokes Lean or cloud APIs."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REQUEST_PATH = ROOT / 'docs/openmath/scalar-ratio-retained-comparator-20261110/REQUEST.json'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify_manifest(path, base, expected=None):
    data = path.read_bytes()
    if expected and digest(data) != expected:
        raise SystemExit('Manifest identity changed: ' + str(path))
    for line in data.decode().splitlines():
        wanted, relative = line.split('  ', 1)
        target = (base / relative).resolve()
        if not target.is_relative_to(base.resolve()) or digest(target.read_bytes()) != wanted:
            raise SystemExit('Input missing, outside root, or changed: ' + relative)
    return digest(data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path, help='New directory; no overwrite')
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        raise SystemExit('Output must be new')
    request = json.loads(REQUEST_PATH.read_text())
    support = REQUEST_PATH.parent / 'SUPPORT.sha256'
    verify_manifest(support, ROOT)
    for relative, expected in request['trusted_input_sha256'].items():
        if digest((ROOT / relative).read_bytes()) != expected:
            raise SystemExit('Frozen input changed: ' + relative)
    for item in request['frozen_manifests']:
        verify_manifest(ROOT / item['path'], ROOT, item['sha256'])
    subprocess.run([sys.executable, '-B', str(ROOT / request['base_preparer']),
                    '--output', str(output)], check=True, cwd=ROOT)
    base_hash = verify_manifest(output / 'MANIFEST.sha256', output,
                                request['base_project_manifest_sha256'])
    if request['packet'] == 'local-boundary-interfaces':
        # Preserve the base-stage index. It is not the index of the overlay.
        (output / 'MANIFEST.sha256').rename(output / 'BASE_PROJECT_MANIFEST.sha256')
        for relative in request['challenge_files']:
            name = str(Path(relative).relative_to(request['challenge_directory']))
            target = output / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((ROOT / relative).read_bytes())
        lakefile = output / 'lakefile.toml'
        text = lakefile.read_text()
        old_roots = json.dumps(['Packet', *request['solution_modules']])
        new_roots = json.dumps(['Packet', *request['solution_modules'], 'Challenge',
                               *['Challenge.' + n.rsplit('.', 1)[1]
                                 for n in request['solution_modules']]])
        if text.count('roots = ' + old_roots) != 1:
            raise SystemExit('Unexpected base Lake library configuration')
        lakefile.write_text(text.replace('roots = ' + old_roots, 'roots = ' + new_roots))
    (output / 'export-roots.txt').write_bytes((REQUEST_PATH.parent / 'export-roots.txt').read_bytes())
    # This is the complete current input index; runtime receipts are separate.
    names = sorted(str(p.relative_to(output)) for p in output.rglob('*') if p.is_file())
    payload = ''.join(digest((output / n).read_bytes()) + '  ' + n + '\n' for n in names)
    (output / 'COMPARATOR_INPUTS.sha256').write_text(payload)
    cfg = json.loads((output / 'comparator.json').read_text())
    if len(cfg['theorem_names']) != 39 or len(cfg['definition_names']) != request['definition_targets']:
        raise SystemExit('Unexpected comparator target selection')
    if cfg['permitted_axioms'] != request['permitted_axioms']:
        raise SystemExit('Unexpected axiom policy')
    actual = subprocess.check_output(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], text=True).strip()
    receipt = {'status': 'PREPARED_ONLY', 'checkout_commit': actual,
               'packet': request['packet'], 'request_sha256': digest(REQUEST_PATH.read_bytes()),
               'support_manifest_sha256': digest(support.read_bytes()),
               'base_project_manifest_sha256': base_hash,
               'comparator_inputs_manifest_sha256': digest(payload.encode()),
               'theorem_targets': 39, 'definition_targets': request['definition_targets'],
               'lean_executed': False, 'comparator': 'NOT_RUN', 'paranoid': 'NOT_RUN',
               'execution_owner': 'Open Math OS',
               'base_sources_note': 'SOURCES.json and BASE_PROJECT_MANIFEST.sha256, if present, describe the original base stage; COMPARATOR_INPUTS.sha256 covers the complete comparison project.'}
    (output / 'RETENTION_PREPARATION.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
