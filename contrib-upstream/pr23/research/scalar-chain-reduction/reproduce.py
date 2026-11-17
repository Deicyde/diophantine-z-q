"""Reproduce the order-31 scalar chain with general preparation.

Finite source, circuit and coefficient checks do not accept the arithmetic proof.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys

from chain_patch import transform

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
PARENT = HERE.parent / 'conditional-quartic-reduction'
CONSTRUCTION = PARENT / 'construction'
TRANSPORT = HERE.parent / 'factored-pole-reduction'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True,
                        help='An absent or empty directory outside the source packets.')
    args = parser.parse_args()
    bindings = json.loads((HERE / 'SOURCE_BINDINGS.json').read_text())

    def check_bindings():
        for bound in bindings['files']:
            if sha(REPO / bound['path']) != bound['sha256']:
                raise ValueError('Changed source: ' + bound['path'])

    check_bindings()
    expected = json.loads((HERE / 'EXPECTED.json').read_text())
    output = args.output.resolve()
    for source in [HERE, PARENT, TRANSPORT]:
        if output == source or source in output.parents:
            raise ValueError('Keep build outputs outside the source packets')
    if output.exists() and any(output.iterdir()):
        raise ValueError('Output directory must be absent or empty')
    output.mkdir(parents=True, exist_ok=True)
    stages = []

    def run(label, *command):
        print(label, flush=True)
        with (output / 'reproduction.log').open('a') as log:
            log.write('\n' + label + '\n')
            log.flush()
            subprocess.run(list(map(str, command)), cwd=REPO, stdout=log,
                           stderr=subprocess.STDOUT, check=True)
        stages.append(label)

    run('Verify the frozen parent source manifest', sys.executable, '-B',
        PARENT / 'reproduce.py', '--check-source')
    original = (CONSTRUCTION / 'builder.cjs').read_text()
    baseline = output / 'baseline'
    baseline.mkdir()
    (baseline / 'builder.cjs').write_text(original)
    run('Build the unchanged raw source for comparison', 'node', baseline / 'builder.cjs')
    candidate = output / 'candidate'
    candidate.mkdir()
    (candidate / 'builder.cjs').write_text(transform(original))
    run('Build the order-31 scalar chain', 'node', candidate / 'builder.cjs')
    run('Check scalar equations, outside rows, height margins and negative controls',
        sys.executable, '-B', HERE / 'check_chain.py', candidate / 'raw-translated-ir.json',
        '--baseline', baseline / 'raw-translated-ir.json',
        '--report', candidate / 'source-check.json')
    run('Compile the quadratic system', sys.executable, '-B',
        CONSTRUCTION / 'tools/compile_ir.py', candidate / 'raw-translated-ir.json',
        candidate / 'compiled')
    run('Replay every source gate and compiler operation', 'node',
        CONSTRUCTION / 'tools/checker.cjs', '--input', candidate / 'raw-translated-ir.json',
        '--compiled', candidate / 'compiled/compiled-ir.json',
        '--certificate', candidate / 'compiled/reduction-certificate.json',
        '--coordinate-map', candidate / 'compiled/coordinate-map.json',
        '--quartic', candidate / 'compiled/polynomial.json',
        '--report', candidate / 'gate-check.json')
    coordinate_map = json.loads((candidate / 'compiled/coordinate-map.json').read_text())
    if coordinate_map['omittedFreeCoordinates']:
        raise ValueError('General preparation must retain its free witnesses')
    run('Replay exact quadratic eliminations', sys.executable, '-B',
        CONSTRUCTION / 'tools/run_pipeline.py', candidate / 'compiled/compiled-ir.json',
        candidate / 'final', '--orders', 2)
    source_ir = candidate / 'final/integer-candidate-ir.json'
    data = json.loads(source_ir.read_text())
    if (len(data['coordinates']), len(data['residuals'])) != (389, 357):
        raise ValueError('Unexpected count before factoring')
    if sha(source_ir) != expected['compiledIrSha256']:
        raise ValueError('Unexpected compiled scalar-chain IR')
    factored = output / 'factored'
    factored.mkdir()
    shutil.copyfile(source_ir, factored / 'scalar-chain389-ir.json')
    for name in ['build_transport.py', 'check_transport.py']:
        # Adapt only the input filename and negative-control slot lookup. All
        # identity, incidence and zero-branch checks remain the parent's code.
        text = (TRANSPORT / name).read_text().replace('baseline389-ir.json', 'scalar-chain389-ir.json')
        text = text.replace("'monomial':[279]", "'monomial':[next(c['id'] for c in a['coordinates'] if c['name']=='detector0.Bh.quadratic')]")
        text = text.replace("c['id']==280", "c['name']=='detector0.s2.quadratic'")
        (factored / name).write_text(text)
        run('Apply ' + name + ' to the actual compiled conics',
            sys.executable, '-B', factored / name, factored)
    run('Produce the input-fixed diagonal scaling', sys.executable, '-B',
        CONSTRUCTION / 'balance_coefficients.py', factored)
    run('Reconstruct every scaled row and every quartic coefficient', sys.executable, '-B',
        PARENT / 'audit/check_diagonal_scaling.py', factored,
        '--expected-exponent', 2130, '--expected-coordinates', 385,
        '--expected-residuals', 353, '--expected-monomials', 26200,
        '--expected-max-digits', 682, '--expected-max-bits', 2266,
        '--report', factored / 'diagonal-check.json')
    summary = json.loads((factored / 'balanced/summary.json').read_text())
    if summary != expected['summary']:
        raise ValueError('Changed measured summary or deterministic table')
    polynomial = json.loads((factored / 'balanced/polynomial.json').read_text())
    if max(abs(int(t['coefficient'])) for t in polynomial['terms']) != 28902 * 3**1420:
        raise ValueError('Changed exact coefficient maximum')
    reports = ['candidate/source-check.json', 'candidate/gate-check.json',
               'factored/transport-check.json', 'factored/diagonal-check.json']
    for relative in reports:
        report = json.loads((output / relative).read_text())
        expected_status = 'passed_exact_algebra_checks' if relative == 'candidate/gate-check.json' else 'PASS'
        if report['status'] != expected_status:
            raise ValueError('Failed finite report: ' + relative)
        if relative == 'candidate/gate-check.json':
            if report['gateIdentities']['unverified'] or not report['quarticTableCompared']:
                raise ValueError('Incomplete gate or quartic replay')
    check_bindings()
    receipt = {'status': 'PASS', 'independentAcceptance': False,
               'scope': 'Finite source, circuit, conic and coefficient replay; arithmetic acceptance pending.',
               'sourceBindingsSha256': sha(HERE / 'SOURCE_BINDINGS.json'),
               'contractSha256': sha(HERE / 'APPLICATION_CONTRACT.json'),
               'compiledIrSha256': sha(source_ir), 'summary': summary,
               'completedStages': stages,
               'reports': [{'path': p, 'sha256': sha(output / p)} for p in reports]}
    (output / 'reproduction-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('PASS: 385 variables, 353 residuals, 26,200 monomials; maximum 682 digits / 2,266 bits.')
    print('Receipt: ' + str(output / 'reproduction-receipt.json'))


if __name__ == '__main__':
    main()
