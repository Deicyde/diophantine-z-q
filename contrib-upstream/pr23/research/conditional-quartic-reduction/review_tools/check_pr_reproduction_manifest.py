"""Independently inspect the actual PR build contract and reference outputs.

This checker does not import the wrapper, producer, compiler or audit modules.
It deliberately does not hash SOURCE_MANIFEST.json in its report, so the
review can be included as new non-build evidence without a self-reference.
"""
from pathlib import Path, PurePosixPath
from collections import Counter
import argparse
import ast
import hashlib
import json
import re


STAGES = ['build_source', 'build_reference_source', 'compile_source',
          'verify_gates', 'reduce_rows', 'lift_constants', 'verify_detector',
          'independent_detector', 'verify_package', 'verify_symbolic',
          'specialize', 'write_tables', 'balance', 'verify_geometry',
          'independent_scalar', 'verify_arithmetic', 'independent_arithmetic',
          'verify_chains', 'second_scalar', 'verify_parameter_binding',
          'verify_stage_bridges', 'verify_diagonal', 'verify_delivered_tables']
REQUIRED_REPORTS = {
    'construction/independent-gate-check.json',
    'construction/detector-source-check.json',
    'construction/independent-final-symbolic-check.json',
    'construction/ordinary389/specialization-report.json',
    'audit/arithmetic-check.json', 'audit/arithmetic-independent-check.json',
    'audit/delivered-quartics-check.json', 'audit/detector-independent-check.json',
    'audit/diagonal-scaling-check.json', 'audit/geometry-check.json',
    'audit/integrated-bridge-check.json', 'audit/parameter-binding-check.json',
    'audit/scalar-independent-check.json', 'audit/scalar-second-review-check.json',
    'audit/scaled-chain-independent-check.json',
}
REQUIRED_SEEDS = {
    'construction/reproduce.py', 'construction/builder.cjs',
    'construction/reference_round7/builder.cjs',
    'construction/verify_package.py', 'construction/balance_coefficients.py',
    'audit/check_detector_source.py', 'audit/check_detector_promotion_independent.py',
    'audit/check_arithmetic_round8.py', 'audit/check_arithmetic_round8_independent.py',
    'audit/check_scaled_chains_independent.py', 'audit/check_diagonal_scaling.py',
    'audit/check_delivered_quartics_round8.py',
    'proofs/arithmetic_round8.tex', 'proofs/detector_round8.tex',
    'proofs/geometry_round7.tex',
}


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
    assert expected['format'] == 'conditional-quartic-proposal-outputs-v2'
    records = manifest['files']
    assert records and len({x['path'] for x in records}) == len(records)
    for record in records:
        path = file_at(proposal, record['path'])
        assert type(record['bytes']) is int and record['bytes'] >= 0
        assert re.fullmatch('[0-9a-f]{64}', record['sha256'])
        assert 'buildInput' not in record or type(record['buildInput']) is bool
        assert path.stat().st_size == record['bytes'] and digest(path) == record['sha256']
    declared = {x['path'] for x in records}
    assert {'reproduce.py', 'EXPECTED_OUTPUTS.json'} <= declared
    actual = {p.relative_to(proposal).as_posix() for p in proposal.rglob('*') if p.is_file()}
    assert actual == declared | {'SOURCE_MANIFEST.json'}, sorted(actual-declared-{'SOURCE_MANIFEST.json'})
    assert not any(p.is_symlink() for p in proposal.rglob('*'))
    seeds = [x for x in records if x.get('buildInput')]
    seed_names = {x['path'] for x in seeds}
    assert REQUIRED_SEEDS <= seed_names, sorted(REQUIRED_SEEDS-seed_names)
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
        fresh = file_at(reference, item['path'])
        assert fresh.stat().st_size == item['bytes'] and digest(fresh) == item['sha256'], item['path']
    files = expected['files']
    assert files and len({x['path'] for x in files}) == len(files)
    generated = {x['path'] for x in files}
    audit_names = expected['auditReports']
    assert audit_names and len(set(audit_names)) == len(audit_names)
    assert set(audit_names) == REQUIRED_REPORTS
    reserved = {'construction.log', 'reproduction-receipt.json',
                'pipeline-progress.json', 'pipeline-completion.json'}
    assert not seed_names & (generated | set(audit_names) |
                            reserved)
    assert not generated & reserved and not set(audit_names) & reserved
    completion_contract = expected['completionRecord']
    assert completion_contract == {
        'path':'pipeline-completion.json', 'pipeline':'construction/reproduce.py',
        'format':'conditional-quartic-pipeline-completion-v1', 'stages':STAGES}
    pipeline = file_at(proposal, 'construction/reproduce.py')
    syntax = ast.parse(pipeline.read_text())
    run_nodes = [(i,node) for i,node in enumerate(syntax.body)
                 if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
                 and isinstance(node.value.func, ast.Name) and node.value.func.id == 'run']
    assert [ast.literal_eval(node.value.args[0]) for _,node in run_nodes] == STAGES
    completion_nodes = [(i,node) for i,node in enumerate(syntax.body)
                        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
                        and isinstance(node.value.func, ast.Name) and node.value.func.id == 'atomic_json']
    assert len(completion_nodes) == 1 and completion_nodes[0][0] > run_nodes[-1][0]
    completion_path = file_at(reference, completion_contract['path'])
    completion = json.loads(completion_path.read_text())
    assert completion == {'format':completion_contract['format'], 'status':'PASS',
                          'pipelineSha256':digest(pipeline), 'completedStages':STAGES}
    compared = []
    for item in files:
        path = file_at(reference, item['path'])
        assert type(item['bytes']) is int and item['bytes'] >= 0
        assert re.fullmatch('[0-9a-f]{64}', item['sha256'])
        assert path.stat().st_size == item['bytes'] and digest(path) == item['sha256'], item['path']
        if path.suffix == '.json':
            assert not volatile_fields(json.loads(path.read_text())), item['path']
        compared.append(item['path'])
    summary = json.loads(file_at(reference, 'construction/balanced/summary.json').read_text())
    assert summary == expected['selected']
    selected = {'coordinates':389, 'residuals':357, 'degree':4, 'monomials':26295,
                'integerContent':1, 'inputFourthPowerCoefficient':'1',
                'maximumCoefficientDigits':757, 'maximumCoefficientBits':2513,
                'scaledCoordinates':13, 'ternaryScaledCoordinates':12,
                'dyadicScaledCoordinates':2, 'anchorExponent':2364, 'cExponent':394}
    assert {key:summary[key] for key in selected} == selected
    for count, exponents in [(391,[788,788]), (392,[338,338,336]),
                             (393,[158,158,158,152])]:
        lifted = json.loads(file_at(reference, f'construction/ordinary{count}/lifted-ir.json').read_text())
        assert len(lifted['coordinates']) == count and len(lifted['residuals']) == 357+len(exponents)
        assert lifted['fixedParameter'] == {'name':'S','value':'3^2364','coordinate':False}
        assert lifted['constantChain']['coefficientExponents'] == exponents
        assert lifted['constantChain']['targetExponent'] == 2364
    table_records = []
    assert expected['committedTables']
    assert len({item['committed'] for item in expected['committedTables']}) == len(expected['committedTables'])
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
        'freshBuildInputFilesUnchanged': True,
        'buildInputs': seeds,
        'buildInputsDisjointFromGeneratedArtifactsAndAuditReports': True,
        'deterministicArtifactsComparedToCompletedReference': len(compared),
        'deterministicArtifactPaths': compared,
        'noTimingOrAbsoluteWorkspaceFieldsInDeterministicJson': True,
        'committedTables': table_records,
        'successfulAuditReports': reports,
        'selectedCountsAndParameter':selected,
        'structuredCompletion':{'sha256':digest(completion_path),
            'pipelineSha256':digest(pipeline), 'orderedStages':STAGES,
            'stageCount':len(STAGES), 'agreesWithActualPipelineAndManifest':True},
        'sourceManifestSelfHashIntentionallyNotRecorded': True,
        'scope': 'Actual manifest and completed-reference coverage review. This does not by itself claim a new full pipeline run. Adding this non-build review to the source snapshot changes no frozen build-input or expected-output binding.'}
    text = json.dumps(report, indent=2)+'\n'
    if args.report:
        args.report.write_text(text)
    print(json.dumps({k: v for k, v in report.items()
                      if k not in {'buildInputs', 'deterministicArtifactPaths', 'successfulAuditReports'}}, indent=2))


if __name__ == '__main__':
    main()
