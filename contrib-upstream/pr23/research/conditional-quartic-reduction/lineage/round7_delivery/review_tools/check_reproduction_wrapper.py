"""Focused failure-path probes for the PR wrapper, using isolated mock builds.

These probes test orchestration and manifest validation, not mathematics.
The real full pipeline has its own fresh reproduction receipt.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

MARKER = 'PASS: fresh construction, every coefficient table, and every portable audit.'
PAYLOAD = b'fresh fixture polynomial\n'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('wrapper', type=Path)
    parser.add_argument('--workdir', type=Path,
                        default=Path(__file__).resolve().parent/'wrapper-probes-final')
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    wrapper = args.wrapper.resolve()
    args.workdir.mkdir(parents=True, exist_ok=True)
    session = Path(tempfile.mkdtemp(prefix='probe-', dir=args.workdir.resolve()))
    results = []

    def run_case(name, expected_success, mode='good', env_change=None):
        case = session/name
        source = case/'source'
        output = case/'output'
        for folder in ['construction', 'audit', 'proofs', 'tables']:
            (source/folder).mkdir(parents=True, exist_ok=True)
        shutil.copyfile(wrapper, source/'reproduce.py')
        (source/'proofs/input.tex').write_text('Fixture proof input.\n')
        (source/'construction/builder.cjs').write_text('// Fixture only.\n')
        (source/'tables/fixture-table.txt').write_bytes(PAYLOAD)
        lines = ['from pathlib import Path', 'import json',
                 'root=Path(__file__).resolve().parent.parent']
        if mode in ['assert_failure', 'ignore_env_assert_failure']:
            lines += ["assert False, 'mandatory fixture assertion must fail'"]
        if mode != 'seeded_output':
            value = b'wrong output\n' if mode == 'artifact_mismatch' else PAYLOAD
            lines += ["(root/'construction/artifact.txt').write_bytes("+repr(value)+')']
            if mode != 'missing_audit':
                status = 'FAIL' if mode == 'failed_audit' else 'PASS'
                lines += ["(root/'audit').mkdir(exist_ok=True)",
                          "(root/'audit/fixture-check.json').write_text(json.dumps({'status': "+repr(status)+"})+'\\n')"]
        if mode == 'changed_source':
            lines += ['Path('+repr(str(source/'proofs/input.tex'))+").write_text('changed\\n')"]
        if mode == 'changed_manifest':
            lines += ['target=Path('+repr(str(source/'SOURCE_MANIFEST.json'))+')',
                      'data=json.loads(target.read_text())', "data['changedDuringBuild']=True",
                      'target.write_text(json.dumps(data))']
        if mode == 'generated_symlink':
            lines += ["(root/'construction/artifact.txt').unlink()",
                      "(root/'construction/artifact.txt').symlink_to("+repr(str(source/'tables/fixture-table.txt'))+')']
        if mode != 'missing_marker':
            lines += ['print('+repr(MARKER)+')']
        if mode == 'subprocess_failure':
            lines += ['raise SystemExit(7)']
        (source/'construction/reproduce.py').write_text('\n'.join(lines)+'\n')
        expected = {
            'format': 'conditional-quartic-proposal-outputs-v1',
            'files': [{'path': 'construction/artifact.txt', 'bytes': len(PAYLOAD),
                       'sha256': hashlib.sha256(PAYLOAD).hexdigest()}],
            'committedTables': [{'committed': 'tables/fixture-table.txt',
                                 'generated': 'construction/artifact.txt'}],
            'auditReports': ['audit/fixture-check.json']}
        if mode == 'wrong_expected_format':
            expected['format'] = 'invalid'
        if mode == 'duplicate_expected_path':
            expected['files'].append(dict(expected['files'][0]))
        if mode == 'duplicate_audit_path':
            expected['auditReports'].append(expected['auditReports'][0])
        if mode == 'duplicate_table_path':
            expected['committedTables'].append(dict(expected['committedTables'][0]))
        for key in ['files', 'committedTables', 'auditReports']:
            if mode == 'empty_'+key:
                expected[key] = []
        if mode == 'table_mismatch':
            (source/'tables/fixture-table.txt').write_text('wrong committed table\n')
        (source/'EXPECTED_OUTPUTS.json').write_text(json.dumps(expected, indent=2)+'\n')
        seeds = {'construction/reproduce.py', 'construction/builder.cjs', 'proofs/input.tex'}
        if mode == 'seeded_output':
            (source/'construction/artifact.txt').write_bytes(PAYLOAD)
            (source/'audit/fixture-check.json').write_text('{"status":"PASS"}\n')
            seeds |= {'construction/artifact.txt', 'audit/fixture-check.json'}
        if mode == 'unlisted_generated_seed':
            (source/'construction/stale-ir.json').write_text('{"stale":true}\n')
            seeds.add('construction/stale-ir.json')
        if mode == 'reserved_receipt_seed':
            (source/'reproduction-receipt.json').write_text('{"status":"PASS"}\n')
            seeds.add('reproduction-receipt.json')
        if mode in ['source_symlink', 'source_symlink_ancestor']:
            outside = case/'external'
            outside.mkdir()
            (outside/'input.tex').write_bytes((source/'proofs/input.tex').read_bytes())
            (source/'proofs/input.tex').unlink()
            if mode == 'source_symlink':
                (source/'proofs/input.tex').symlink_to(outside/'input.tex')
            else:
                (source/'proofs').rmdir()
                (source/'proofs').symlink_to(outside, target_is_directory=True)
        names = ['reproduce.py', 'construction/reproduce.py', 'construction/builder.cjs',
                 'proofs/input.tex', 'tables/fixture-table.txt', 'EXPECTED_OUTPUTS.json']
        names += sorted(seeds-set(names))
        records = []
        for name_ in names:
            path = source/name_
            records.append({'path': name_, 'bytes': path.stat().st_size,
                            'sha256': sha(path), 'buildInput': name_ in seeds})
        if mode == 'duplicate_source_path':
            records.append(dict(records[0]))
        if mode == 'source_traversal':
            records[3]['path'] = '../external/input.tex'
        if mode == 'unbound_expected':
            records = [r for r in records if r['path'] != 'EXPECTED_OUTPUTS.json']
        if mode == 'unbound_wrapper':
            records = [r for r in records if r['path'] != 'reproduce.py']
        manifest = {'format': 'conditional-quartic-proposal-source-v1', 'files': records}
        (source/'SOURCE_MANIFEST.json').write_text(json.dumps(manifest, indent=2)+'\n')
        if mode == 'source_hash_mismatch':
            (source/'proofs/input.tex').write_text('changed before running\n')
        sentinel = None
        if mode in ['nonempty_output', 'existing_empty_output']:
            output.mkdir()
            if mode == 'nonempty_output':
                sentinel = output/'sentinel'
                sentinel.write_text('preserve this preexisting file\n')
                before_sentinel = sentinel.read_bytes()
        if mode == 'output_inside_source':
            output = source/'forbidden-output'
        command = [sys.executable, '-B', str(source/'reproduce.py'), '--output', str(output)]
        if mode == 'ignore_env_assert_failure':
            command.insert(1, '-E')
        if mode == 'check_source_only':
            command = [sys.executable, '-B', str(source/'reproduce.py'), '--check-source']
        env = os.environ.copy()
        env.pop('PYTHONOPTIMIZE', None)
        if env_change:
            env.update(env_change)
        result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, env=env)
        (case/'command.log').write_text(result.stdout)
        observed_success = result.returncode == 0
        receipt = output/'reproduction-receipt.json'
        if expected_success and mode != 'check_source_only':
            assert receipt.is_file(), (name, 'missing success receipt', result.stdout)
            assert json.loads(receipt.read_text())['status'] == 'PASS'
        if not expected_success:
            assert not receipt.exists(), (name, 'failure wrote a PASS receipt')
        if sentinel:
            assert sentinel.read_bytes() == before_sentinel, name+' changed existing output'
        if mode in ['output_inside_source', 'check_source_only']:
            assert not output.exists(), name+' unexpectedly created output'
        record = {'case': name, 'expectedSuccess': expected_success,
                  'observedSuccess': observed_success, 'returnCode': result.returncode,
                  'matchedExpectation': observed_success == expected_success,
                  'diagnosticTail': result.stdout.splitlines()[-5:],
                  'logSha256': sha(case/'command.log')}
        results.append(record)

    cases = [('valid_fresh_output', True, 'good'),
             ('valid_existing_empty_output', True, 'existing_empty_output'),
             ('valid_source_only_check', True, 'check_source_only'),
             ('subprocess_failure_despite_marker', False, 'subprocess_failure'),
             ('missing_success_marker', False, 'missing_marker'),
             ('artifact_mismatch', False, 'artifact_mismatch'),
             ('committed_table_mismatch', False, 'table_mismatch'),
             ('failed_audit_status', False, 'failed_audit'),
             ('missing_audit_report', False, 'missing_audit'),
             ('source_changed_during_build', False, 'changed_source'),
             ('manifest_changed_during_build', False, 'changed_manifest'),
             ('nonempty_output_is_preserved', False, 'nonempty_output'),
             ('output_inside_source', False, 'output_inside_source'),
             ('source_symlink_file', False, 'source_symlink'),
             ('source_symlink_ancestor', False, 'source_symlink_ancestor'),
             ('seeded_generated_output_and_audit', False, 'seeded_output'),
             ('unlisted_generated_intermediate_seed', False, 'unlisted_generated_seed'),
             ('reserved_receipt_seed', False, 'reserved_receipt_seed'),
             ('wrong_expected_format', False, 'wrong_expected_format'),
             ('duplicate_source_path', False, 'duplicate_source_path'),
             ('duplicate_expected_path', False, 'duplicate_expected_path'),
             ('duplicate_audit_path', False, 'duplicate_audit_path'),
             ('duplicate_committed_table', False, 'duplicate_table_path'),
             ('empty_expected_files', False, 'empty_files'),
             ('empty_committed_tables', False, 'empty_committedTables'),
             ('empty_audit_reports', False, 'empty_auditReports'),
             ('unbound_expected_manifest', False, 'unbound_expected'),
             ('unbound_wrapper', False, 'unbound_wrapper'),
             ('source_path_traversal', False, 'source_traversal'),
             ('source_hash_mismatch', False, 'source_hash_mismatch')]
    for name, wanted, mode in cases:
        run_case(name, wanted, mode)
    run_case('optimized_failing_assertion', False, 'assert_failure', {'PYTHONOPTIMIZE': '1'})
    run_case('child_assertions_enabled_when_wrapper_ignores_environment', False,
             'ignore_env_assert_failure', {'PYTHONOPTIMIZE': '1'})
    run_case('generated_artifact_symlink', False, 'generated_symlink')
    report = {'status': 'PASS' if all(r['matchedExpectation'] for r in results) else 'FAIL',
              'wrapperSha256': sha(wrapper), 'probeScriptSha256': sha(Path(__file__)),
              'cases': len(results), 'matched': sum(r['matchedExpectation'] for r in results),
              'results': results,
              'scope': 'Isolated mock builders test wrapper validation, fresh-output discipline and failure propagation. These probes do not execute or certify the mathematical construction; its real fresh reproduction is separate.'}
    text = json.dumps(report, indent=2)+'\n'
    if args.report:
        args.report.write_text(text)
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    if report['status'] != 'PASS':
        print(json.dumps([r for r in results if not r['matchedExpectation']], indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
