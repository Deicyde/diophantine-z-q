"""Compile the R-inverse detector weight circuit with the actual pipeline (research copy)."""
from pathlib import Path
import argparse, json, os, re, shutil, subprocess, sys
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
CONSTRUCTION = HERE.parent / 'conditional-quartic-reduction/construction'
TRANSPORT = HERE.parent / 'factored-pole-reduction'
sys.path.insert(0, str(HERE.parent / 'scalar-chain-reduction'))
sys.path.insert(0, str(HERE.parent / 'scalar-preparation-zero'))
sys.path.insert(0, str(HERE.parent / 'detector-cube-reuse'))
from chain_patch import transform as chain
from zero_patch import transform as zero
from check_zero import omit_unused
from cube_patch import transform as cube

OLD_WEIGHTS = """let mixA=rsq('detector'+r+'.mixA',eDelta),
 mixB=rm('detector'+r+'.mixB',mixA,eDelta),
 mixC=rm('detector'+r+'.mixC',mixB,q1cube),
 mixD=rsq('detector'+r+'.mixD',mixC),
 q12=rquot('detector'+r+'.q12',sq(mixD),eDelta,'positive_inverse_R');"""
OLD_LAST = "let q45=rquot('detector'+r+'.q45',sq(mixedHigh),q1cube,'positive_order_one_weight');"

def rinv(source):
    # Store R=1/E once; each later quotient by R multiplies by E inside one quadratic row.
    new = """const Rinv=rquot('detector'+r+'.Rinv',one,eDelta,'positive_inverse_R');
 let qFive=rquot('detector'+r+'.qFive',mul(q1cube,eDelta),Rinv,'positive_R'),
 qEleven=rquot('detector'+r+'.qEleven',sq(qFive),Rinv,'positive_R'),
 q12=rquot('detector'+r+'.q12',sq(qEleven),Rinv,'positive_R');"""
    assert source.count(OLD_WEIGHTS) == 1 and source.count(OLD_LAST) == 1
    source = source.replace(OLD_WEIGHTS, new)
    return source.replace(OLD_LAST, "let q45=rquot('detector'+r+'.q45',sq(mixedHigh),Rinv,'positive_R');")

def powF(source):
    # q12=q1^23, mixedHigh=q1^46 (pure q1 powers); last weight q*F = mixedHigh^2 = q1^92/F
    # = e^(2*47-1) delta^-97 A^-5 for order 47 (semantic test D * delta^-95 * C^-5, A=C^2).
    new = """let q1p6=rsq('detector'+r+'.q1Sixth',q1cube),
 q1p12=rsq('detector'+r+'.q1Twelfth',q1p6),
 q12=rquot('detector'+r+'.q12',sq(q1p12),q1,'positive_order_one_weight');"""
    assert source.count(OLD_WEIGHTS) == 1 and source.count(OLD_LAST) == 1
    source = source.replace(OLD_WEIGHTS, new)
    return source.replace(OLD_LAST, "let q45=rquot('detector'+r+'.q45',sq(mixedHigh),Fv,'positive_F');")

def powinv(source, order):
    # Pure q1 powers with one stored inverse power; uniform normalization q_m=q1^(2m-1).
    if order == 48:
        new = """let q1p4=rsq('detector'+r+'.q1FourthForWeights',q1square),
 qInv=rquot('detector'+r+'.q1InverseCube',one,q1cube,'positive_order_one_weight'),
 q1p10=rquot('detector'+r+'.q1Tenth',mul(q1p4,q1cube),qInv,'positive_order_one_weight'),
 q12=rquot('detector'+r+'.q12',sq(q1p10),qInv,'positive_order_one_weight');"""
    elif order == 50:
        new = """let q1p4=rsq('detector'+r+'.q1FourthForWeights',q1square),
 q1p8=rsq('detector'+r+'.q1Eighth',q1p4),
 qInv=rquot('detector'+r+'.q1InverseSeventh',q1,q1p8,'positive_order_one_weight'),
 q12=rquot('detector'+r+'.q12',sq(q1p8),qInv,'positive_order_one_weight');"""
    else:
        raise ValueError(order)
    assert source.count(OLD_WEIGHTS) == 1 and source.count(OLD_LAST) == 1
    source = source.replace(OLD_WEIGHTS, new)
    return source.replace(OLD_LAST, "let q45=rquot('detector'+r+'.q45',sq(mixedHigh),qInv,'positive_order_one_weight');")

def last_q1(source):
    # Cube-reuse chain unchanged; q46*q1 = mixedHigh^2 gives e^91/delta^3.
    assert source.count(OLD_LAST) == 1
    return source.replace(OLD_LAST, "let q45=rquot('detector'+r+'.q45',sq(mixedHigh),q1,'positive_order_one_weight');")

def renumber(source, order):
    result = re.sub(r'\b45\b', str(order), source)
    return result.replace('q45', 'q' + str(order)).replace('E45', 'E' + str(order))

def build(variant, order, exponent):
    source = zero(chain((CONSTRUCTION / 'builder.cjs').read_text(), exponent=exponent))
    if variant == 'rinv':
        source = rinv(source)
    elif variant == 'cube_q1':
        source = last_q1(cube(source))
    elif variant == 'powF':
        source = powF(source)
    elif variant == 'powinv':
        source = powinv(source, order)
    elif variant == 'cube':
        source = cube(source)
    return renumber(source, order) if order != 45 else source

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--variant', choices=['rinv', 'cube_q1', 'cube', 'powF', 'powinv'], required=True)
    ap.add_argument('--order', type=int, required=True)
    ap.add_argument('--exponent', type=int, required=True)
    args = ap.parse_args()
    out = args.output.resolve(); assert not out.exists() or not any(out.iterdir()); out.mkdir(parents=True, exist_ok=True)
    def run(*command):
        print('Run', *[Path(str(c)).name for c in command[:2]], flush=True)
        with (out / 'replay.log').open('a') as log:
            env = os.environ.copy(); env.pop('PYTHONOPTIMIZE', None)
            subprocess.run(list(map(str, command)), cwd=REPO, stdout=log, stderr=subprocess.STDOUT, check=True, env=env)
    (out / 'builder.cjs').write_text(build(args.variant, args.order, args.exponent))
    run('node', out / 'builder.cjs')
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
    run(sys.executable, '-B', HERE.parent / 'conditional-quartic-reduction/audit/check_diagonal_scaling.py',
        out, '--expected-exponent', args.exponent, '--expected-coordinates', summary['coordinates'],
        '--report', out / 'diagonal-check.json')
    for name, status in {'gate-check.json': 'passed_exact_algebra_checks', 'transport-check.json': 'PASS', 'diagonal-check.json': 'PASS'}.items():
        assert json.loads((out / name).read_text())['status'] == status, name
    gates = json.loads((out / 'gate-check.json').read_text())
    assert not gates['gateIdentities']['unverified'] and gates['quarticTableCompared']
    print(json.dumps(summary), flush=True)
    (out / 'MEASURED.json').write_text(json.dumps({'variant': args.variant, 'order': args.order, 'anchorExponent': args.exponent,
        'compiledBeforeFactor': [n, m], 'summary': summary, 'omittedCoordinates': removed, 'arithmeticAcceptance': False}, indent=2) + '\n')

if __name__ == '__main__':
    main()
