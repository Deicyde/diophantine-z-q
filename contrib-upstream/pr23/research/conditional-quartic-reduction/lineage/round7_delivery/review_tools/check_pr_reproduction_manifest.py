"""Independently inspect the actual PR build contract and reference outputs.

This checker does not import the wrapper, producer, compiler or audit modules.
It deliberately does not hash SOURCE_MANIFEST.json in its report, so the
review can be included as new non-build evidence without a self-reference.
"""
from pathlib import Path, PurePosixPath
from collections import Counter
import argparse
import hashlib
import json
import re


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(text):
    assert isinstance(text, str) and text and '\\' not in text
    path = PurePosixPath(text)
    assert not path.is_absolute() and '..' not in path.parts and str(path) == text
    return Path(*path.parts)


def file_at(root, text):
    part = relative(text)
    path = root
    for component in part.parts:
        path = path/component
        assert not path.is_symlink(), text
    assert path.is_file() and root in path.resolve().parents, text
    return path


def volatile_fields(value, trail=''):
    found = []
    if isinstance(value, dict):
        for key, item in value.items():
            current = trail+'/'+key
            if re.search(r'elapsed|duration|timestamp|createdAt|modifiedAt|wallTime', key, re.I):
                found.append(current)
            found += volatile_fields(item, current)
    elif isinstance(value, list):
        for i, item in enumerate(value):
            found += volatile_fields(item, trail+'/'+str(i))
    elif isinstance(value, str) and '/workspace/' in value:
        found.append(trail)
    return found


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('proposal', type=Path)
    parser.add_argument('--reference', required=True, type=Path)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    proposal, reference = args.proposal.resolve(), args.reference.resolve()
    manifest = json.loads(file_at(proposal, 'SOURCE_MANIFEST.json').read_text())
    expected_path = file_at(proposal, 'EXPECTED_OUTPUTS.json')
    expected = json.loads(expected_path.read_text())
    assert manifest['format'] == 'conditional-quartic-proposal-source-v1'
    assert expected['format'] == 'conditional-quartic-proposal-outputs-v1'
    records = manifest['files']
    assert records and len({x['path'] for x in records}) == len(records)
    for record in records:
        path = file_at(proposal, record['path'])
        assert path.stat().st_size == record['bytes'] and digest(path) == record['sha256']
    declared = {x['path'] for x in records}
    assert {'reproduce.py', 'EXPECTED_OUTPUTS.json'} <= declared
    actual = {p.relative_to(proposal).as_posix() for p in proposal.rglob('*') if p.is_file()}
    assert actual == declared | {'SOURCE_MANIFEST.json'}, sorted(actual-declared-{'SOURCE_MANIFEST.json'})
    assert not any(p.is_symlink() for p in proposal.rglob('*'))
    seeds = [x for x in records if x.get('buildInput')]
    seed_names = {x['path'] for x in seeds}
    assert 'construction/reproduce.py' in seed_names
    kinds = Counter()
    for item in seeds:
        path = relative(item['path'])
        assert item['buildInput'] is True
        if path.parts[0] in {'construction', 'audit'}:
            assert path.suffix in {'.py', '.cjs'}
            kinds[path.parts[0]+'Code'] += 1
        else:
            assert path.parts[0] == 'proofs' and path.suffix in {'.tex', '.txt'}
            kinds['proofText'] += 1
    files = expected['files']
    assert files and len({x['path'] for x in files}) == len(files)
    generated = {x['path'] for x in files}
    audit_names = expected['auditReports']
    assert audit_names and len(set(audit_names)) == len(audit_names)
    assert not seed_names & (generated | set(audit_names) |
                            {'construction.log', 'reproduction-receipt.json'})
    compared = []
    for item in files:
        path = file_at(reference, item['path'])
        assert path.stat().st_size == item['bytes'] and digest(path) == item['sha256'], item['path']
        if path.suffix == '.json':
            assert not volatile_fields(json.loads(path.read_text())), item['path']
        compared.append(item['path'])
    summary = json.loads(file_at(reference, 'construction/balanced/summary.json').read_text())
    assert summary == expected['selected']
    table_records = []
    assert expected['committedTables']
    for item in expected['committedTables']:
        assert item['committed'] in declared and item['generated'] in generated
        left = file_at(proposal, item['committed'])
        right = file_at(reference, item['generated'])
        assert left.read_bytes() == right.read_bytes()
        table_records.append({**item, 'bytes': left.stat().st_size, 'sha256': digest(left)})
    reports = []
    statuses = {'PASS', 'passed_exact_algebra_checks', 'passed_final_SOS_and_fixed_parameter_checks'}
    for name in audit_names:
        path = file_at(reference, name)
        data = json.loads(path.read_text())
        assert data.get('status') in statuses, name
        reports.append({'path': name, 'status': data['status']})
    report = {
        'status': 'PASS',
        'wrapperSha256': digest(proposal/'reproduce.py'),
        'expectedOutputsSha256': digest(expected_path),
        'pipelineSha256': digest(proposal/'construction/reproduce.py'),
        'checkerSha256': digest(Path(__file__)),
        'reviewedSourceEvidenceFiles': len(records),
        'allDeclaredFilesMatchAndInventoryCompleteAtReview': True,
        'buildInputFiles': len(seeds), 'buildInputKinds': dict(kinds),
        'buildInputs': seeds,
        'buildInputsDisjointFromGeneratedArtifactsAndAuditReports': True,
        'deterministicArtifactsComparedToCompletedReference': len(compared),
        'deterministicArtifactPaths': compared,
        'noTimingOrAbsoluteWorkspaceFieldsInDeterministicJson': True,
        'committedTables': table_records,
        'successfulAuditReports': reports,
        'sourceManifestSelfHashIntentionallyNotRecorded': True,
        'scope': 'Actual manifest and completed-reference coverage review. This does not by itself claim a new full pipeline run. Adding this non-build review to the source snapshot changes no frozen build-input or expected-output binding.'}
    text = json.dumps(report, indent=2)+'\n'
    if args.report:
        args.report.write_text(text)
    print(json.dumps({k: v for k, v in report.items()
                      if k not in {'buildInputs', 'deterministicArtifactPaths', 'successfulAuditReports'}}, indent=2))


if __name__ == '__main__':
    main()
