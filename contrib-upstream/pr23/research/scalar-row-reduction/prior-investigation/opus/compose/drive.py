"""Compose driver (copy-local, research only, no arithmetic acceptance).

Builds the #13 pipeline source with the frontier detector transform (pow46 / 45 / ...),
then applies scalarpoles patches (tri, tau, ri31, f0guard) and the coeffrows A row
operation, then runs: node builder -> compile_ir -> checker.cjs (gate identities)
-> omit unused -> run_pipeline --orders 2 -> four-conic transports (+check).
Balancing is a separate step (balance.py).

usage: python3 -B drive.py OUT --detector pow46 --exponent 2016 --patches tri,A
"""
from pathlib import Path
import argparse, json, os, shutil, subprocess, sys

HERE = Path(__file__).resolve().parent
WORK = HERE / 'work'
RESEARCH = WORK / 'research'
CONSTRUCTION = RESEARCH / 'conditional-quartic-reduction/construction'
TRANSPORT = RESEARCH / 'factored-pole-reduction'
sys.path[:0] = [str(RESEARCH / 'detector-cube-reuse'), str(HERE / 'tools')]
from run_variant import transform as detector_transform  # frontier driver (copied)
from check_zero import omit_unused
import patches as SP


def once(s, old, new):
    assert s.count(old) == 1, old
    return s.replace(old, new)


def patch_A(src):
    # coeffrows A: in the w numerator replace x_S by h_S^2 (row + const * x_S definition rows).
    return once(src, "rawFmul(Qp.x,Rp.j)),F,'totally_positive_xP_xU_plus_D');",
                "rawFmul(rawFmul(Qp.h,Qp.h),Rp.j)),F,'totally_positive_xP_xU_plus_D');")


PATCH = {'tri': SP.t_by_rinverse, 'tau': SP.tau_chart, 'ri31': SP.ri31_leaf,
         'f0guard': SP.f0_guard, 'A': patch_A}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('out', type=Path)
    ap.add_argument('--detector', default='pow46')
    ap.add_argument('--exponent', type=int, required=True)
    ap.add_argument('--patches', default='')
    a = ap.parse_args()
    out = a.out.resolve()
    if out.exists():
        shutil.rmtree(out)
    out.mkdir(parents=True)

    def run(*command):
        with (out / 'replay.log').open('a') as log:
            env = os.environ.copy(); env.pop('PYTHONOPTIMIZE', None)
            subprocess.run(list(map(str, command)), cwd=WORK, stdout=log, stderr=subprocess.STDOUT, check=True, env=env)

    base = (CONSTRUCTION / 'builder.cjs').read_text()
    if a.detector.startswith('powinv'):
        # weight47 sibling: delta-only 7-gate chains at order 48/50 (no cube patch).
        from chain_patch import transform as chain
        from zero_patch import transform as zero
        import w47run
        order = int(a.detector[6:])
        src = w47run.renumber(w47run.powinv(zero(chain(base, exponent=a.exponent)), order), order)
    else:
        src = detector_transform(base, a.detector, a.exponent)
    for p in [p for p in a.patches.split(',') if p]:
        src = PATCH[p](src)
    (out / 'builder.cjs').write_text(src)
    run('node', out / 'builder.cjs')
    raw = json.loads((out / 'raw-translated-ir.json').read_text())
    run(sys.executable, '-B', CONSTRUCTION / 'tools/compile_ir.py', out / 'raw-translated-ir.json', out / 'compiled')
    run('node', CONSTRUCTION / 'tools/checker.cjs', '--input', out / 'raw-translated-ir.json',
        '--compiled', out / 'compiled/compiled-ir.json', '--certificate', out / 'compiled/reduction-certificate.json',
        '--coordinate-map', out / 'compiled/coordinate-map.json', '--quartic', out / 'compiled/polynomial.json',
        '--report', out / 'gate-check.json')
    active, removed = omit_unused(json.loads((out / 'compiled/compiled-ir.json').read_text()),
                                  json.loads((out / 'compiled/coordinate-map.json').read_text()))
    (out / 'active-ir.json').write_text(json.dumps(active, indent=2) + '\n')
    run(sys.executable, '-B', CONSTRUCTION / 'tools/run_pipeline.py', out / 'active-ir.json', out / 'before-factor', '--orders', 2)
    ir = json.loads((out / 'before-factor/integer-candidate-ir.json').read_text())
    n, m = len(ir['coordinates']) - 4, len(ir['residuals']) - 4
    shutil.copyfile(out / 'before-factor/integer-candidate-ir.json', out / 'candidate-ir.json')
    for name in ['build_transport.py', 'check_transport.py']:
        code = (TRANSPORT / name).read_text().replace('baseline389-ir.json', 'candidate-ir.json')
        code = code.replace('385', str(n)).replace('353', str(m))
        code = code.replace("'monomial':[279]", "'monomial':[next(c['id'] for c in a['coordinates'] if c['name']=='detector0.Bh.quadratic')]")
        code = code.replace("c['id']==280", "c['name']=='detector0.s2.quadratic'")
        (out / name).write_text(code)
        run(sys.executable, '-B', out / name, out)
    fin = json.loads((out / 'final/integer-candidate-ir.json').read_text())
    gates = json.loads((out / 'gate-check.json').read_text())
    res = {'detector': a.detector, 'exponent': a.exponent, 'patches': a.patches,
           'raw': raw['counts'], 'omitted': [c['name'] for c in removed],
           'final': {'coordinates': len(fin['coordinates']), 'residuals': len(fin['residuals'])},
           'gateCheck': gates['status'], 'gateUnverified': len(gates['gateIdentities']['unverified']),
           'quarticTableCompared': gates.get('quarticTableCompared'),
           'transportCheck': json.loads((out / 'transport-check.json').read_text())['status']}
    (out / 'BUILD.json').write_text(json.dumps(res, indent=2) + '\n')
    print(json.dumps(res))


if __name__ == '__main__':
    main()
