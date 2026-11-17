#!/usr/bin/env python3
"""Collect artifacts from the completed build/export and six-checker replay.

This only writes new evidence under `openmath-os-evidence`; it never rebuilds,
exports, alters proofs, or reruns a checker. No mathematical acceptance or
software provenance beyond the recorded build/export/replay is implied.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess

CENTER = Path(__file__).resolve().parent
CHECKOUT = next(parent for parent in CENTER.parents
                if (parent / 'lean' / '.checks' / 'openmath-local-boundary').is_dir())
PROJECT = CHECKOUT / 'lean' / '.checks' / 'openmath-local-boundary'
NATIVE = CHECKOUT / 'lean' / '.checks' / 'pr2-native-independent'
NATIVE_LIB = NATIVE / 'lib'


def sha(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            hasher.update(block)
    return hasher.hexdigest()


def command_record(argv, output_name=None):
    args = list(argv)
    if output_name:
        stdout = CENTER / f'{output_name}.stdout.txt'
        stderr = CENTER / f'{output_name}.stderr.txt'
        with stdout.open('wb') as out, stderr.open('wb') as err:
            done = subprocess.run(args, cwd=PROJECT, stdout=out, stderr=err)
        return done.returncode
    return subprocess.check_output(args, cwd=PROJECT, text=True).strip()


def main():
    assert CHECKOUT.name == 'pr2-review'
    target_names = [f'Research.DerivativeSwitch.{name}' for name in [
        'ConjugateLocalTransport', 'ConjugateLocalH1', 'ActualBoundaryCup',
        'OrthogonalComparison',
    ]]
    artifacts = []
    for base in (PROJECT / '.lake/build/lib/lean', PROJECT / 'openmath-evidence'):
        if base.is_dir():
            for path in sorted(base.rglob('*')):
                if path.is_file() and path.suffix in {'.olean', '.trace', '.ilean'}:
                    artifacts.append({'path': str(path), 'sha256': sha(path), 'bytes': path.stat().st_size})
    for filename in ['ConjugateLocalTransport', 'ConjugateLocalH1', 'ActualBoundaryCup', 'OrthogonalComparison']:
        for base in (PROJECT / '.lake/build/lib/lean', NATIVE_LIB):
            source = base / 'Research' / 'DerivativeSwitch' / f'{filename}.olean'
            assert source.exists(), source
    artifacts.append({'path': str(CENTER / 'packet.ndjson'),
                      'sha256': sha(CENTER / 'packet.ndjson'),
                      'bytes': (CENTER / 'packet.ndjson').stat().st_size})

    # Metadata-only executables: all were used by the successful Lake replay.
    prefix = Path(command_record(['lean', '--print-prefix']))
    tools = {}
    for name in ('lean', 'lake', 'leanexport', 'leanchecker',
                 'leanchecker-paranoid', 'lean4lean', 'nanoda_bin', 'con-leche', 'con-ron'):
        candidate = prefix / 'bin' / name
        if not candidate.exists():
            alternative = shutil.which(name)
            candidate = Path(alternative) if alternative else candidate
        assert candidate.exists(), f'Missing bundled executable: {name}'
        tools[name] = {'path': str(candidate.resolve()), 'sha256': sha(candidate)}

    for name, filename in [('RESULT', 'RESULT.json'),
                           ('commands', 'commands.json'),
                           ('axioms-and-statements', 'axioms-and-statements.stdout.txt'),
                           ('axioms-and-statements.err', 'axioms-and-statements.stderr.txt'),
                           ('Audit', 'Audit.lean')]:
        source = NATIVE / filename
        assert source.exists(), source
        shutil.copy2(source, CENTER / f'native-{filename}')
    core_dir = CENTER / 'core-artifacts'
    core_dir.mkdir(exist_ok=True)
    for base in (PROJECT / '.lake/build/lib/lean', NATIVE_LIB):
        for name in ['ConjugateLocalTransport', 'ConjugateLocalH1',
                     'ActualBoundaryCup', 'OrthogonalComparison']:
            shutil.copy2(base / 'Research' / 'DerivativeSwitch' / f'{name}.olean',
                         core_dir / f'{name}.olean')
    report = {
        'checker_names': {'nanoda': 'Executable path is `nanoda_bin` in this installed toolchain.'},
        'compiled_artifact_hashes': artifacts,
        'tool_versions': tools,
        'paranoid_exit_code': int((CENTER / 'paranoid-exit-code.txt').read_text()),
    }
    (CENTER / 'ARTIFACTS_AND_TOOLS.json').write_text(json.dumps(report, indent=2) + '\n')
    (CENTER / 'artifact-audit-exit-code.txt').write_text('0\n')
    print(json.dumps({'artifact_records': len(artifacts), 'tools': tools,
                      'core_olean_copies': len(list(core_dir.glob('*.olean')))}))


if __name__ == '__main__':
    main()
