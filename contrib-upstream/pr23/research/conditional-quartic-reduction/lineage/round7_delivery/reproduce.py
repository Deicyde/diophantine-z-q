"""Rebuild and audit the proposal in a fresh directory, leaving sources intact.

Requires Python 3.11+ and Node.js. No external Python packages or network are
needed. The checks do not establish the inherited global arithmetic theorem.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative_path(value):
    if not isinstance(value, str) or not value or '\\' in value:
        raise ValueError('Invalid manifest path')
    p = PurePosixPath(value)
    if p.is_absolute() or '..' in p.parts or not p.parts or str(p) != value:
        raise ValueError('Invalid manifest path: '+value)
    return Path(*p.parts)


def regular_file(root, relative):
    """Reject symbolic links in both a file and every ancestor below root."""
    actual = root
    for part in relative.parts:
        actual = actual/part
        if actual.is_symlink():
            raise ValueError('Symbolic link is not an input or output artifact: '+str(relative))
    if not actual.is_file() or root not in actual.resolve().parents:
        raise ValueError('Missing or escaping artifact: '+str(relative))
    return actual


def file_records(value, label):
    if not isinstance(value, list) or not value:
        raise ValueError(label+' must contain a nonempty file list')
    paths = set()
    for item in value:
        path = relative_path(item['path'])
        if path in paths:
            raise ValueError('Duplicate '+label+' path: '+str(path))
        paths.add(path)
        if type(item['bytes']) is not int or item['bytes'] < 0:
            raise ValueError('Invalid byte count: '+str(path))
        digest = item['sha256']
        if not isinstance(digest, str) or len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest):
            raise ValueError('Invalid SHA-256: '+str(path))
    return paths


def verify_snapshot():
    manifest_path = regular_file(HERE, Path('SOURCE_MANIFEST.json'))
    manifest = json.loads(manifest_path.read_text())
    if manifest['format'] != 'conditional-quartic-proposal-source-v1':
        raise ValueError('Unknown source manifest format')
    paths = file_records(manifest['files'], 'source')
    if not {Path('reproduce.py'), Path('EXPECTED_OUTPUTS.json')} <= paths:
        raise ValueError('The wrapper and expected outputs must be source-manifest-bound')
    for item in manifest['files']:
        path = relative_path(item['path'])
        actual = regular_file(HERE, path)
        if actual.stat().st_size != item['bytes'] or sha(actual) != item['sha256']:
            raise ValueError('Source snapshot changed: '+str(path))
        if 'buildInput' in item and type(item['buildInput']) is not bool:
            raise ValueError('buildInput must be a Boolean: '+str(path))
    return manifest, sha(manifest_path)


def validate_expected(manifest):
    expected = json.loads((HERE/'EXPECTED_OUTPUTS.json').read_text())
    if expected.get('format') != 'conditional-quartic-proposal-outputs-v1':
        raise ValueError('Unknown expected-output manifest format')
    generated = file_records(expected['files'], 'output')
    source = {relative_path(item['path']) for item in manifest['files']}
    seeds = {relative_path(item['path']) for item in manifest['files'] if item.get('buildInput')}
    if Path('construction/reproduce.py') not in seeds:
        raise ValueError('The construction entry point must be a build input')
    for path in seeds:
        code = path.parts[0] in {'construction', 'audit'} and path.suffix in {'.py', '.cjs'}
        proof = path.parts[0] == 'proofs' and path.suffix in {'.tex', '.txt'}
        if not (code or proof):
            raise ValueError('Only construction/checker source and proof text may seed a build: '+str(path))
    audit_names = expected['auditReports']
    if not isinstance(audit_names, list) or not audit_names:
        raise ValueError('Expected audit reports must be a nonempty list')
    audits = [relative_path(name) for name in audit_names]
    if len(set(audits)) != len(audits):
        raise ValueError('Duplicate audit report path')
    reserved = {Path('construction.log'), Path('reproduction-receipt.json')}
    if seeds & (generated | set(audits) | reserved):
        raise ValueError('A generated artifact or audit report cannot be a build input')
    if generated & reserved or set(audits) & reserved:
        raise ValueError('Reserved reproduction path used as an expected artifact')
    tables = expected['committedTables']
    if not isinstance(tables, list) or not tables:
        raise ValueError('Committed tables must be a nonempty list')
    committed = set()
    for record in tables:
        src, dst = relative_path(record['committed']), relative_path(record['generated'])
        if src in committed:
            raise ValueError('Duplicate committed table: '+str(src))
        committed.add(src)
        if src not in source or dst not in generated:
            raise ValueError('Each committed table and reconstruction must be manifest-bound')
    return expected


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path,
                    help='An absent or empty output directory; default is a fresh directory under build/.')
    ap.add_argument('--check-source', action='store_true',
                    help='Verify the supplied source snapshot without running the construction.')
    args = ap.parse_args()
    if sys.version_info < (3, 11):
        raise RuntimeError('Python 3.11 or newer is required')
    if not __debug__:
        raise RuntimeError('Run without -O or PYTHONOPTIMIZE; exact audits require Python assertions')
    manifest, manifest_hash = verify_snapshot()
    expected = validate_expected(manifest)
    if args.check_source:
        print(f'PASS: {len(manifest["files"])} source/evidence files match the supplied snapshot.')
        return
    node = shutil.which('node')
    if not node:
        raise RuntimeError('Node.js is required; no package installation is performed by this script')
    if args.output:
        output = args.output.resolve()
        if output == HERE or HERE in output.parents:
            raise ValueError('Output must be outside the tracked proposal source directory')
        if output.exists() and any(output.iterdir()):
            raise ValueError('Output directory is not empty; select a fresh --output path')
        output.mkdir(parents=True, exist_ok=True)
    else:
        build_parent = HERE.parents[1]/'build'
        build_parent.mkdir(parents=True, exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix='conditional-quartic-', dir=build_parent))
    seed = [item for item in manifest['files'] if item.get('buildInput')]
    for item in seed:
        relative = relative_path(item['path'])
        destination = output/relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(HERE/relative, destination)
    command = [sys.executable, '-B', str(output/'construction/reproduce.py')]
    log_path = output/'construction.log'
    print(f'Rebuilding from {len(seed)} source/proof files in {output}', flush=True)
    environment = os.environ.copy()
    environment.pop('PYTHONOPTIMIZE', None)
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    with log_path.open('w', encoding='utf-8') as log:
        result = subprocess.run(command, cwd=output, env=environment, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        print('\n'.join(log_path.read_text().splitlines()[-45:]), file=sys.stderr)
        raise SystemExit(f'Construction or audit failed; complete log: {log_path}')
    if 'PASS: fresh construction, every coefficient table, and every portable audit.' not in log_path.read_text():
        raise RuntimeError('The complete pipeline did not record its final success marker')
    matches = []
    for item in expected['files']:
        path = regular_file(output, relative_path(item['path']))
        if path.stat().st_size != item['bytes'] or sha(path) != item['sha256']:
            raise RuntimeError('Reconstructed artifact differs: '+item['path'])
        matches.append(item)
    for record in expected['committedTables']:
        if regular_file(HERE, relative_path(record['committed'])).read_bytes() != regular_file(output, relative_path(record['generated'])).read_bytes():
            raise RuntimeError('Committed coefficient table differs from its reconstruction')
    _, after_hash = verify_snapshot()
    if after_hash != manifest_hash:
        raise RuntimeError('Tracked source manifest changed during the build')
    reports = {}
    for name in expected['auditReports']:
        report_path = regular_file(output, relative_path(name))
        report = json.loads(report_path.read_text())
        if report.get('status') not in {'PASS', 'passed_exact_algebra_checks', 'passed_final_SOS_and_fixed_parameter_checks'}:
            raise RuntimeError('Missing successful audit status: '+name)
        reports[name] = sha(report_path)
    receipt = {
        'status': 'PASS', 'method': 'Fresh output directory received only source/proof seeds; all mathematical outputs were regenerated.',
        'sourceManifestSha256': manifest_hash,
        'sourceFilesVerified': len(manifest['files']), 'buildInputFiles': len(seed),
        'deterministicArtifactsCompared': len(matches), 'files': matches,
        'auditReports': reports, 'trackedProposalFilesUnchanged': True,
        'constructionLogSha256': sha(log_path), 'pythonVersion': sys.version,
        'nodeVersion': subprocess.check_output([node, '--version'], text=True).strip(),
        'scope': 'Exact finite source, gate, transformation, full polynomial and text-table checks; inherited global arithmetic remains conditional.',
    }
    (output/'reproduction-receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(f'PASS: {len(matches)} deterministic artifacts matched byte for byte; all exact audits passed.')
    print('Tracked proposal source files are unchanged.')
    print(f'Receipt: {output / "reproduction-receipt.json"}')


if __name__ == '__main__':
    main()
