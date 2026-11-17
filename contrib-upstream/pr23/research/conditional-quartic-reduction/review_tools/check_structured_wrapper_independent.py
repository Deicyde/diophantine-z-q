"""Independent focused checks of the structured-completion wrapper.

Mock builders test the handoff contract, not the mathematical construction.
All fixtures are confined to the explicitly supplied work directory.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('wrapper', type=Path)
    parser.add_argument('--workdir', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    args.workdir.mkdir(parents=True, exist_ok=True)
    session = Path(tempfile.mkdtemp(prefix='independent-', dir=args.workdir.resolve()))
    results = []
    stages = ['produce', 'audit']
    data = b'exact fixture coefficient table\n'
    for mode in ['control_without_stdout', 'changed_fresh_builder', 'changed_fresh_proof',
                 'deleted_fresh_proof', 'symlinked_fresh_proof',
                 'changed_fresh_pipeline', 'completion_before_nonzero_exit']:
        case = session/mode
        source = case/'source'
        output = case/'output'
        for name in ['construction', 'audit', 'proofs', 'tables']:
            (source/name).mkdir(parents=True, exist_ok=True)
        shutil.copyfile(args.wrapper, source/'reproduce.py')
        (source/'construction/builder.cjs').write_text('// reviewed fixture builder\n')
        (source/'proofs/input.tex').write_text('Reviewed fixture proof.\n')
        (source/'tables/fixture.txt').write_bytes(data)
        program = [
            'from pathlib import Path', 'import hashlib,json',
            'here=Path(__file__).resolve().parent', 'root=here.parent',
            "(here/'table.txt').write_bytes("+repr(data)+')',
            "(root/'audit').mkdir(exist_ok=True)",
            "(root/'audit/check.json').write_text(json.dumps({'status':'PASS'})+'\\n')",
        ]
        changes = {'changed_fresh_builder': 'construction/builder.cjs',
                   'changed_fresh_proof': 'proofs/input.tex',
                   'changed_fresh_pipeline': 'construction/reproduce.py'}
        if mode in changes:
            program += ["(root/"+repr(changes[mode])+").write_text('changed during build\\n')"]
        if mode in ['deleted_fresh_proof', 'symlinked_fresh_proof']:
            program += ["(root/'proofs/input.tex').unlink()"]
        if mode == 'symlinked_fresh_proof':
            program += ["(root/'proofs/input.tex').symlink_to("+repr(str(source/'proofs/input.tex'))+")"]
        program += [
            "record={'format':'conditional-quartic-pipeline-completion-v1','status':'PASS',",
            "'pipelineSha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),",
            "'completedStages':"+repr(stages)+'}',
            "(root/'pipeline-completion.json').write_text(json.dumps(record)+'\\n')",
        ]
        if mode == 'completion_before_nonzero_exit':
            program += ['raise SystemExit(9)']
        (source/'construction/reproduce.py').write_text('\n'.join(program)+'\n')
        expected = {
            'format': 'conditional-quartic-proposal-outputs-v2',
            'files': [{'path':'construction/table.txt', 'bytes':len(data),
                       'sha256':hashlib.sha256(data).hexdigest()}],
            'committedTables': [{'committed':'tables/fixture.txt', 'generated':'construction/table.txt'}],
            'auditReports':['audit/check.json'],
            'completionRecord': {'path':'pipeline-completion.json',
                'pipeline':'construction/reproduce.py',
                'format':'conditional-quartic-pipeline-completion-v1', 'stages':stages},
        }
        (source/'EXPECTED_OUTPUTS.json').write_text(json.dumps(expected, indent=2)+'\n')
        seeds = {'construction/builder.cjs','construction/reproduce.py','proofs/input.tex'}
        manifest = {'format':'conditional-quartic-proposal-source-v1', 'files':[]}
        for file in sorted(source.rglob('*')):
            if file.is_file():
                name = file.relative_to(source).as_posix()
                manifest['files'].append({'path':name,'bytes':file.stat().st_size,
                    'sha256':digest(file),'buildInput':name in seeds})
        (source/'SOURCE_MANIFEST.json').write_text(json.dumps(manifest, indent=2)+'\n')
        result = subprocess.run([sys.executable,'-B',str(source/'reproduce.py'),'--output',str(output)],
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (case/'command.log').write_text(result.stdout)
        receipt = output/'reproduction-receipt.json'
        results.append({'case':mode,'returnCode':result.returncode,
                        'successReceiptPresent':receipt.is_file(),
                        'expectedSuccess':mode=='control_without_stdout',
                        'diagnosticTail':result.stdout.splitlines()[-5:],
                        'commandLogSha256':digest(case/'command.log')})
    report = {'wrapperSha256':digest(args.wrapper),'checkerSha256':digest(Path(__file__)),
              'cases':results,
              'allExpectationsMatched':all((r['returnCode']==0)==r['expectedSuccess'] and
                                           r['successReceiptPresent']==r['expectedSuccess'] for r in results),
              'scope':'Independent mock tests of structured completion, unchanged fresh seeds, and process-failure precedence. No mathematical construction is executed.'}
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    if not report['allExpectationsMatched']:
        raise SystemExit(1)


if __name__=='__main__':
    main()
