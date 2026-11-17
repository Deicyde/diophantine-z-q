"""Reproduce the four-conic transport of the frozen 389-variable proposal.

Only the Python standard library and the parent package's Node dependency
are needed. A successful run is a finite check, not independent acceptance.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
PARENT = HERE.parent/'conditional-quartic-reduction'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='An absent or empty output directory.')
    parser.add_argument('--baseline', type=Path,
                        help='Reuse a completed parent reproduction after checking its entire manifest.')
    args = parser.parse_args()
    contract = json.loads((HERE/'APPLICATION_CONTRACT.json').read_text())
    for source in contract['boundFiles']:
        path = REPO/source['path']
        if digest(path) != source['sha256']:
            raise ValueError('Changed bound source: '+source['path'])
    if args.output:
        output = args.output.resolve()
        if output == HERE or HERE in output.parents or output == PARENT or PARENT in output.parents:
            raise ValueError('Build outputs must be outside the source packages')
        if output.exists() and any(output.iterdir()):
            raise ValueError('Output directory is not empty')
        output.mkdir(parents=True, exist_ok=True)
    else:
        (REPO/'build').mkdir(exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix='factored-poles-', dir=REPO/'build'))
    log_path = output/'reproduce.log'
    stages = []

    def run(label, script, *arguments):
        print(label, flush=True)
        with log_path.open('a') as log:
            log.write('\n'+label+'\n')
            log.flush()
            subprocess.run([sys.executable, '-B', str(script), *map(str, arguments)],
                           cwd=REPO, stdout=log, stderr=subprocess.STDOUT, check=True)
        stages.append(label)

    baseline = args.baseline.resolve() if args.baseline else output/'baseline389'
    if args.baseline is None:
        run('Reproduce the frozen 389-variable parent', PARENT/'reproduce.py', '--output', baseline)
    run('Check the complete parent import and reproduction',
        PARENT/'review_tools/check_pr_reproduction_manifest.py', PARENT,
        '--reference', baseline, '--report', output/'parent-check.json')
    source = baseline/'construction/final/integer-candidate-ir.json'
    expected = json.loads((HERE/'EXPECTED.json').read_text())
    if digest(source) != expected['sourceIrSha256']:
        raise ValueError('Parent compiled IR differs from the reviewed source')
    candidate = output/'candidate385'
    candidate.mkdir()
    shutil.copyfile(source, candidate/'baseline389-ir.json')
    run('Transport the four conics', HERE/'build_transport.py', candidate)
    run('Check transport identities, consumers and exceptional branches',
        HERE/'check_transport.py', candidate)
    run('Apply the unchanged parent diagonal scaling',
        PARENT/'construction/balance_coefficients.py', candidate)
    run('Check all diagonal substitutions and every quartic coefficient',
        PARENT/'audit/check_diagonal_scaling.py', candidate,
        '--expected-exponent', 2364, '--expected-coordinates', 385,
        '--expected-residuals', 353, '--expected-monomials', 26235,
        '--expected-max-digits', 757, '--expected-max-bits', 2513,
        '--report', candidate/'diagonal-check.json')
    for record in expected['artifacts']:
        if digest(candidate/record['path']) != record['sha256']:
            raise ValueError('Unexpected deterministic artifact: '+record['path'])
    summary = json.loads((candidate/'balanced/summary.json').read_text())
    if summary != expected['summary']:
        raise ValueError('Measured summary differs from expected output')
    for relative in ['transport-check.json', 'diagonal-check.json']:
        if json.loads((candidate/relative).read_text())['status'] != 'PASS':
            raise ValueError('Failed finite report: '+relative)
    if digest(source) != expected['sourceIrSha256']:
        raise ValueError('Parent source changed during transport')
    for bound in contract['boundFiles']:
        if digest(REPO/bound['path']) != bound['sha256']:
            raise ValueError('Bound source changed during reproduction: '+bound['path'])
    receipt = {
        'status': 'PASS',
        'scope': 'Finite reproduction and source comparison; independent mathematical acceptance pending.',
        'independentAcceptance': False,
        'contractSha256': digest(HERE/'APPLICATION_CONTRACT.json'),
        'baselineWasRebuilt': args.baseline is None,
        'sourceIrSha256': digest(source),
        'completedStages': stages,
        'summary': summary,
        'reports': [{'path': str(p.relative_to(output)), 'sha256': digest(p)} for p in
                    [output/'parent-check.json', candidate/'transport-check.json',
                     candidate/'diagonal-check.json']],
    }
    (output/'reproduction-receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print('PASS: 385 variables, 353 residuals, 26,235 monomials; maximum 757 digits / 2,513 bits.')
    print('Receipt: '+str(output/'reproduction-receipt.json'))


if __name__ == '__main__':
    main()
