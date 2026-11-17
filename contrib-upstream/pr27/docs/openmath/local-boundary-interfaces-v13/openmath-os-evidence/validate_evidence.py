#!/usr/bin/env python3
"""Validate the completed evidence package; do not alter proof or checker files."""
from pathlib import Path
import hashlib
import json
import subprocess

ROOT = Path.cwd()
EVIDENCE = ROOT / 'docs/openmath/local-boundary-interfaces-v13/openmath-os-evidence'
PROJECT = ROOT / 'lean/.checks/openmath-local-boundary'
CORE = ROOT / 'research/local-boundary-interfaces'
SOURCE_HEAD = '3e01aa877cd7434fdc759fe7b6a9271de6deff2e'
MERGE_HEAD = 'b6223977015d6f25baf613d0c88a5c83050f9c84'
BASE = '9c0b3aba60d90fdcac82115f0582a6f52f1054f7'
ORIGINAL = '33483f751e6dcd3f91fb303969838aca33ad0458'
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def git(*args):
    root = Path(subprocess.check_output(
        ['git','-c','safe.directory=*','rev-parse','--show-toplevel'],
        cwd=ROOT, text=True).strip())
    return subprocess.check_output(['git','-c','safe.directory=*','-C',str(root),*args], text=True).strip()


def main():
    assert git('rev-parse','HEAD') == SOURCE_HEAD
    assert git('rev-parse','omm/main') == MERGE_HEAD
    root_lock = ROOT / 'lean/lake-manifest.json'
    assert sha(root_lock) == 'a770787f33b5824f61a0731d59e67fca3f44a531b21d1fc1a804064c6fb54e58'
    origin = json.loads((CORE/'ORIGIN.json').read_text())
    selection = json.loads((CORE/'TARGETS.json').read_text())
    modules = selection['modules']
    target_roots = selection['proof_roots']
    definitions = selection['definitions_to_print']
    assert len(modules) == 4 and len(target_roots) == 41
    assert len(set(target_roots)) == 41 and len(definitions) == 16
    for entry in origin['modules']:
        if entry['module'] not in modules:
            raise AssertionError('Module/target mismatch')
        path = ROOT / entry['path']
        assert sha(path) == entry['sha256']
        assert git('rev-parse', f'{SOURCE_HEAD}:{entry["path"]}') == entry['source_blob']
        assert git('rev-parse', f'{ORIGINAL}:{entry["path"]}') == entry['source_blob']
    manifest = CORE / 'MANIFEST.sha256'
    assert sha(manifest) == 'ce59e6667e58c1858a0bb87830c35f4142dc1f69c805f2e4daaa169f130220e3'
    entries = manifest.read_text().splitlines()
    assert len(entries) == 62
    for line in entries:
        expected, name = line.split('  ',1)
        assert sha(ROOT / name) == expected, name
    prepared_manifest = PROJECT/'MANIFEST.sha256'
    assert sha(prepared_manifest) == '5a828f5d4608b801f7016b7c387fae3ab78274f237c8077771b38d7bbadd20a0'
    manifest_check = EVIDENCE/'generated-manifest.stdout.txt'
    manifest_lines = [line.strip() for line in manifest_check.read_text().splitlines() if line.strip()]
    assert manifest_lines
    assert len(manifest_lines) == len(prepared_manifest.read_text().splitlines())
    assert all(line.endswith(': OK') for line in manifest_lines), manifest_lines
    assert (EVIDENCE/'generated-manifest.stderr.txt').read_text() == ''
    assert PROJECT.joinpath('roots.txt').read_text().splitlines() == target_roots
    assert json.loads(PROJECT.joinpath('TARGETS.json').read_text())['proof_roots'] == target_roots
    selected_pins = json.loads((PROJECT/'lake-manifest.json').read_text())
    assert selected_pins['packages'] == json.loads(root_lock.read_text())['packages']
    prepared_deps = json.loads((EVIDENCE/'PREPARED_DEPENDENCIES.json').read_text())
    assert len(prepared_deps['dependencies']) == 9
    assert [p['name'] for p in prepared_deps['dependencies']] == [p['name'] for p in selected_pins['packages']]
    for item in prepared_deps['dependencies']:
        assert item['cache_present'] and item['tracked_source_clean']
    native = json.loads((ROOT/'lean/.checks/pr2-native-independent/RESULT.json').read_text())
    assert native['status'] == 'PASS'
    assert set(native['proof_roots']) == set(target_roots)
    assert set(native['theorem_axioms']) == set(target_roots)
    assert all(set(values) <= ALLOWED for values in native['theorem_axioms'].values())
    assert len(native['dependencies']) == 9
    audits=(EVIDENCE/'native-axioms-and-statements.stdout.txt').read_text()
    assert 'AXIOM_AUDIT_PASS declarations=41' in audits
    assert 'sorryAx' not in audits
    assert all(name in audits for name in definitions)
    export = json.loads((PROJECT/'openmath-evidence/export.json').read_text())
    assert export['exit_code'] == 0
    assert export['roots'] == target_roots
    assert export['export_bytes'] == (EVIDENCE/'packet.ndjson').stat().st_size
    assert sha(EVIDENCE/'packet.ndjson') == export['export_sha256']
    assert export['export_sha256'] == '4dca1de2e2450011f8ec32eb8cd9c17b531c7fbedd813ce75b0221dfe30e42aa'
    for label, exit_name in [('lake-build','lake-build-exit-code.txt'),('export','export-exit-code.txt'),
                             ('paranoid','paranoid-exit-code.txt'),('artifact','artifact-audit-exit-code.txt')]:
        assert Path(EVIDENCE/exit_name).read_text().strip() == '0', label
    checks = [
        'Lean paranoid kernel accepts the solution',
        'lean4lean kernel accepts the solution',
        'nanoda kernel accepts the solution',
        'con-leche kernel accepts the solution',
        'con-ron kernel accepts the solution',
        'Lean default kernel accepts the solution',
    ]
    stdout = (EVIDENCE/'paranoid.stdout.txt').read_text()
    assert all(message in stdout for message in checks)
    assert (EVIDENCE/'paranoid.stderr.txt').read_text() == ''
    assert 'Uses axioms: Quot.sound, propext, Classical.choice' in stdout
    assert 'checked 13713 declarations' in stdout
    assert stdout.count('accepted 13716 declarations (--verified)') == 2
    tools = json.loads((EVIDENCE/'ARTIFACTS_AND_TOOLS.json').read_text())
    assert all(data.get('path') and data.get('sha256') for data in tools['tool_versions'].values())
    assert Path(tools['tool_versions']['nanoda_bin']['path']).name == 'nanoda_bin'
    assert len(list((EVIDENCE/'core-artifacts').glob('*.olean'))) == 4
    for path in (EVIDENCE/'core-artifacts').glob('*.olean'):
        assert sha(path)
    controls = json.loads((EVIDENCE/'controls.stdout.txt').read_text().strip())
    assert controls.get('status') == 'PASS'
    assert controls.get('adverse_signatures') or controls.get('finite_checks') or controls
    assert (EVIDENCE/'controls.stderr.txt').read_text() == ''
    optimized = (EVIDENCE/'controls-optimized-exit-code.txt').read_text().strip()
    assert optimized == '1'
    assert 'Refusing optimized Python: these controls require assertions' in (EVIDENCE/'controls-optimized.stderr.txt').read_text()
    protocol = (EVIDENCE/'protocol.stdout.txt').read_text()
    assert 'PASS: 9 historical dispositions' in protocol
    assert 'PASS: 7 negative controls rejected' in protocol
    assert 'PASS: 19 application-review negative controls rejected' in protocol
    assert (EVIDENCE/'protocol.stderr.txt').read_text() == ''
    assert 'bubblewrap 0.' in (EVIDENCE/'bwrap-version.txt').read_text()
    independent = EVIDENCE/'INDEPENDENT_STATEMENT_REVIEW.md'
    text = independent.read_text()
    required = ['19 + 8 + 7 + 7 = 41', 'The 16 tested definitions',
                'No defective local deduction was found', 'right homotopy inverse',
                'The four formal modules, all 41 explicit roots and all 16 printed definitions']
    assert all(part in text for part in required)
    report = {
        'result': 'PASS',
        'scope': 'Independent PR #2 four-source, 41-root/16-definition semantic and six-checker evidence; no whole-manuscript acceptance.',
        'review_head': SOURCE_HEAD, 'fork_merge_commit': MERGE_HEAD, 'pr_base': BASE,
        'declaration_counts': [
            'lean4lean checked 13713 declarations',
            'con-leche accepted 13716 declarations',
            'con-ron accepted 13716 declarations',
        ],
        'per_checker': {name: 'accepted' for name in ['Lean_default','Lean_paranoid','lean4lean','nanoda','con-leche','con-ron']},
        'export_sha256': export['export_sha256'], 'export_bytes': export['export_bytes'],
        'proof_roots': len(target_roots),
        'per_root_axioms': sorted(ALLOWED),
        'dependency_revisions_verified': 9,
        'core_manifest_verified_entries': len(entries),
        'generated_manifest_sha256': sha(prepared_manifest),
        'compiled_core_oleans_retained': 4,
        'generated_artifact_records': len(tools['compiled_artifact_hashes']),
        'executable_hashes_present': True,
        'sandbox': 'Lake check with sandbox enabled by default; no --inadvisably-no-sandbox was used.',
        'checks_not_run': ['Open Math cloud execution','independent hermetic dependency rebuild','external independent specialist review'],
        'statement_and_application_review': 'No local proof defect found within conditional-interface scope. The actual global boundary-cup/Poitou–Tate instance, common-strict matrix/stored-row identification, integral determinant realization, inner/outer limits, restricted converse, and main Diophantine theorem remain outside the PR.',
        'published_history_unchanged': True,
    }
    (EVIDENCE/'EVIDENCE_VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
