"""Reproduce mixed detector normalization: 380 variables and 644 digits.

Research experiment: compiler replay is not arithmetic acceptance.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
CONSTRUCTION = HERE.parent / 'conditional-quartic-reduction/construction'
TRANSPORT = HERE.parent / 'factored-pole-reduction'
sys.path.insert(0, str(HERE.parent / 'scalar-chain-reduction'))
sys.path.insert(0, str(HERE.parent / 'scalar-preparation-zero'))
from chain_patch import transform as chain
from zero_patch import transform as zero
from check_zero import omit_unused
sys.path.insert(0, str(HERE.parent / 'detector-cube-reuse'))
from cube_patch import transform as cube
from normalize_patch import transform as mixed


def transform(source, order, exponent):
    source = zero(chain(source, exponent=exponent))
    if order == 45:
        return source
    old = "let q45=rquot('detector'+r+'.q45',sq(mixedHigh),q1cube,'positive_order_one_weight');"
    if order == 47:
        new = """let highLift=rm('detector'+r+'.highLift',mixedHigh,eDelta);
 let q45=rquot('detector'+r+'.q45',sq(highLift),q1,'positive_order_one_weight');"""
    else:
        raise ValueError('Unsupported weight circuit')
    assert source.count(old) == 1
    result = re.sub(r'\b45\b', str(order), source.replace(old, new))
    return result.replace('q45', 'q' + str(order)).replace('E45', 'E' + str(order))


def main():
    if not __debug__:
        raise RuntimeError('Run the verification without Python optimization')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--order', type=int, choices=[46], default=46)
    # The selected source binds one anchor to each order.
    args = ap.parse_args()
    manifest = HERE / 'SOURCE_BINDINGS.json'
    assert hashlib.sha256(manifest.read_bytes()).hexdigest() == (HERE / 'SOURCE_BINDINGS_SHA256.txt').read_text().strip()
    bindings = json.loads(manifest.read_text())
    def check_bindings():
        for bound in bindings['files']:
            assert hashlib.sha256((REPO / bound['path']).read_bytes()).hexdigest() == bound['sha256'], bound['path']
    check_bindings()
    out = args.output.resolve()
    args.exponent = 2010
    assert not out.exists() or not any(out.iterdir())
    assert REPO / 'research' not in out.parents
    out.mkdir(parents=True, exist_ok=True)

    def run(*command):
        print('Run', Path(str(command[1])).name if len(command) > 1 else command[0], flush=True)
        with (out / 'replay.log').open('a') as log:
            environment = os.environ.copy()
            environment.pop('PYTHONOPTIMIZE', None)
            subprocess.run(list(map(str, command)), cwd=REPO, stdout=log,
                           stderr=subprocess.STDOUT, check=True, env=environment)

    original = (CONSTRUCTION / 'builder.cjs').read_text()
    baseline_source = cube(transform(original, 45, 2118))
    source = mixed(cube(transform(original, 45, args.exponent)))
    baseline = out / 'baseline'
    baseline.mkdir()
    (baseline / 'builder.cjs').write_text(baseline_source)
    run('node', baseline / 'builder.cjs')
    (out / 'builder.cjs').write_text(source)
    run('node', out / 'builder.cjs')
    run(sys.executable, '-B', HERE / 'check_mixed.py', baseline / 'raw-translated-ir.json',
        out / 'raw-translated-ir.json', '--report', out / 'mixed-check.json')
    run(sys.executable, '-B', CONSTRUCTION / 'tools/compile_ir.py', out / 'raw-translated-ir.json', out / 'compiled')
    run('node', CONSTRUCTION / 'tools/checker.cjs', '--input', out / 'raw-translated-ir.json',
        '--compiled', out / 'compiled/compiled-ir.json', '--certificate', out / 'compiled/reduction-certificate.json',
        '--coordinate-map', out / 'compiled/coordinate-map.json', '--quartic', out / 'compiled/polynomial.json',
        '--report', out / 'gate-check.json')
    active, removed = omit_unused(json.loads((out / 'compiled/compiled-ir.json').read_text()),
                                 json.loads((out / 'compiled/coordinate-map.json').read_text()))
    (out / 'active-ir.json').write_text(json.dumps(active, indent=2) + '\n')
    run(sys.executable, '-B', CONSTRUCTION / 'tools/run_pipeline.py', out / 'active-ir.json', out / 'before-factor', '--orders', 2)
    original = out / 'before-factor/integer-candidate-ir.json'
    ir = json.loads(original.read_text())
    n, m = len(ir['coordinates']) - 4, len(ir['residuals']) - 4
    shutil.copyfile(original, out / 'candidate-ir.json')
    for name in ['build_transport.py', 'check_transport.py']:
        code = (TRANSPORT / name).read_text().replace('baseline389-ir.json', 'candidate-ir.json')
        code = code.replace('385', str(n)).replace('353', str(m))
        code = code.replace("'monomial':[279]", "'monomial':[next(c['id'] for c in a['coordinates'] if c['name']=='detector0.Bh.quadratic')]")
        code = code.replace("c['id']==280", "c['name']=='detector0.s2.quadratic'")
        (out / name).write_text(code)
        run(sys.executable, '-B', out / name, out)
    run(sys.executable, '-B', CONSTRUCTION / 'balance_coefficients.py', out)
    summary = json.loads((out / 'balanced/summary.json').read_text())
    expected = json.loads((HERE / 'EXPECTED.json').read_text())[str(args.order)]
    assert summary == expected['summary']
    run(sys.executable, '-B', HERE.parent / 'conditional-quartic-reduction/audit/check_diagonal_scaling.py',
        out, '--expected-exponent', args.exponent, '--expected-coordinates', 380,
        '--expected-residuals', 349,
        '--expected-monomials', 26025,
        '--expected-max-digits', 644, '--expected-max-bits', 2139, '--report', out / 'diagonal-check.json')
    report_statuses = {'mixed-check.json': 'PASS', 'gate-check.json': 'passed_exact_algebra_checks',
                       'transport-check.json': 'PASS', 'diagonal-check.json': 'PASS'}
    for name, status in report_statuses.items():
        assert json.loads((out / name).read_text())['status'] == status, name
    gates = json.loads((out / 'gate-check.json').read_text())
    assert not gates['gateIdentities']['unverified'] and gates['quarticTableCompared']
    polynomial = json.loads((out / 'balanced/polynomial.json').read_text())
    assert max(abs(int(t['coefficient'])) for t in polynomial['terms']) == 28902*3**(2*args.exponent//3)
    for name, digest in expected['files'].items():
        assert hashlib.sha256((out / name).read_bytes()).hexdigest() == digest, name
    check_bindings()
    print(json.dumps(summary), flush=True)
    receipt = {'order': args.order, 'anchorExponent': args.exponent, 'summary': summary,
               'omittedCoordinates': removed, 'arithmeticAcceptance': False,
               'files': {p: hashlib.sha256((out / p).read_bytes()).hexdigest() for p in
                         ['builder.cjs', 'raw-translated-ir.json', 'final/integer-candidate-ir.json', 'balanced/polynomial.json',
                          *report_statuses]}}
    (out / 'MEASURED.json').write_text(json.dumps(receipt, indent=2) + '\n')


if __name__ == '__main__':
    main()
