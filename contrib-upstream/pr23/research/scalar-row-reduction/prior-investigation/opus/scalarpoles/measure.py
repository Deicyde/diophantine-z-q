"""Measure a builder variant with the stack's actual pipeline (copy).

usage: python3 -B measure.py VARIANT_BUILDER.cjs OUTDIR [--prefixes detector0,...] [--balance] [--exponent E]
Mirrors research/detector-cube-reuse/reproduce.py, but omits *any* unused
unprotected base coordinate and lets the conic transport run on a chosen
set of pole prefixes.
"""
from pathlib import Path
from copy import deepcopy
import argparse, json, os, shutil, subprocess, sys

HERE = Path(__file__).resolve().parent
REPO = HERE / 'repo'
CONSTRUCTION = REPO / 'research/conditional-quartic-reduction/construction'
TRANSPORT = REPO / 'research/factored-pole-reduction'


def run(out, *command):
    with (out / 'replay.log').open('a') as log:
        env = os.environ.copy(); env.pop('PYTHONOPTIMIZE', None)
        subprocess.run(list(map(str, command)), cwd=REPO, stdout=log, stderr=subprocess.STDOUT, check=True, env=env)


def omit_unused(data, cmap):
    free = set(cmap['omittedFreeCoordinates'])
    removed = [c for c in data['coordinates'] if c['id'] in free]
    assert all(not c.get('protected', False) for c in removed), removed
    assert not any(free & set(t['monomial']) for r in data['residuals'] for t in r['terms'])
    res = deepcopy(data)
    res['coordinates'] = [c for c in data['coordinates'] if c['id'] not in free]
    return res, removed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('builder', type=Path)
    ap.add_argument('out', type=Path)
    ap.add_argument('--prefixes', default='detector0,detector1,detector2,scalar')
    ap.add_argument('--balance', action='store_true')
    ap.add_argument('--checker', action='store_true')
    a = ap.parse_args()
    out = a.out.resolve()
    if out.exists(): shutil.rmtree(out)
    out.mkdir(parents=True)
    shutil.copyfile(a.builder, out / 'builder.cjs')
    run(out, 'node', out / 'builder.cjs')
    raw = json.loads((out / 'raw-translated-ir.json').read_text())
    run(out, sys.executable, '-B', CONSTRUCTION / 'tools/compile_ir.py', out / 'raw-translated-ir.json', out / 'compiled')
    if a.checker:
        run(out, 'node', CONSTRUCTION / 'tools/checker.cjs', '--input', out / 'raw-translated-ir.json',
            '--compiled', out / 'compiled/compiled-ir.json', '--certificate', out / 'compiled/reduction-certificate.json',
            '--coordinate-map', out / 'compiled/coordinate-map.json', '--quartic', out / 'compiled/polynomial.json',
            '--report', out / 'gate-check.json')
    comp = json.loads((out / 'compiled/compiled-ir.json').read_text())
    active, removed = omit_unused(comp, json.loads((out / 'compiled/coordinate-map.json').read_text()))
    (out / 'active-ir.json').write_text(json.dumps(active, indent=2) + '\n')
    run(out, sys.executable, '-B', CONSTRUCTION / 'tools/run_pipeline.py', out / 'active-ir.json', out / 'before-factor', '--orders', 2)
    ir = json.loads((out / 'before-factor/integer-candidate-ir.json').read_text())
    prefixes = [p for p in a.prefixes.split(',') if p]
    k = len(prefixes)
    n, m = len(ir['coordinates']) - k, len(ir['residuals']) - k
    shutil.copyfile(out / 'before-factor/integer-candidate-ir.json', out / 'candidate-ir.json')
    result = {'rawCoordinates': len(raw['coordinates']), 'rawResiduals': len(raw['residuals']),
              'omitted': [c['name'] for c in removed],
              'beforeFactor': {'coordinates': len(ir['coordinates']), 'residuals': len(ir['residuals'])}}
    if k:
        for name in ['build_transport.py', 'check_transport.py']:
            code = (TRANSPORT / name).read_text().replace('baseline389-ir.json', 'candidate-ir.json')
            code = code.replace('385', str(n)).replace('353', str(m))
            code = code.replace("['detector0','detector1','detector2','scalar']", repr(prefixes))
            code = code.replace("'monomial':[279]", "'monomial':[next(c['id'] for c in a['coordinates'] if c['name']=='detector0.Bh.quadratic')]")
            code = code.replace("c['id']==280", "c['name']=='detector0.s2.quadratic'")
            (out / name).write_text(code)
        run(out, sys.executable, '-B', out / 'build_transport.py', out)
        try:
            run(out, sys.executable, '-B', out / 'check_transport.py', out)
            result['transportCheck'] = json.loads((out / 'transport-check.json').read_text()).get('status')
        except subprocess.CalledProcessError:
            result['transportCheck'] = 'FAILED (see replay.log)'
        fin = json.loads((out / 'final/integer-candidate-ir.json').read_text())
    else:
        (out / 'final').mkdir(exist_ok=True)
        shutil.copyfile(out / 'candidate-ir.json', out / 'final/integer-candidate-ir.json')
        fin = ir
    result['final'] = {'coordinates': len(fin['coordinates']), 'residuals': len(fin['residuals'])}
    if a.balance:
        run(out, sys.executable, '-B', CONSTRUCTION / 'balance_coefficients.py', out)
        result['balanced'] = json.loads((out / 'balanced/summary.json').read_text())
    (out / 'MEASURED.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=1))


if __name__ == '__main__':
    main()
