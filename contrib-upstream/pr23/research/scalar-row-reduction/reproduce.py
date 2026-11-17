"""Reproduce the 379-variable, 425-digit conditional row-reduction candidate.

Only Python standard library and Node are needed. Exact weights are supplied;
no floating-point search runs. Finite replay is not arithmetic acceptance.
"""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
CONSTRUCTION=HERE.parent/'conditional-quartic-reduction/construction'
TRANSPORT=HERE.parent/'factored-pole-reduction'
for directory in ['scalar-chain-reduction','scalar-preparation-zero','detector-cube-reuse','mixed-detector-normalization']:
    sys.path.insert(0,str(HERE.parent/directory))
from chain_patch import transform as chain
from zero_patch import transform as zero
from cube_patch import transform as cube
from normalize_patch import transform as mixed
from check_zero import omit_unused
from row_patch import transform as rows


def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def check_bindings(packet):
    manifest=packet/'SOURCE_BINDINGS.json'
    assert digest(manifest)==(packet/'SOURCE_BINDINGS_SHA256.txt').read_text().strip()
    for entry in json.loads(manifest.read_text())['files']:
        assert digest(REPO/entry['path'])==entry['sha256'],entry['path']


def parent_builder(exponent=2010):
    return mixed(cube(zero(chain((CONSTRUCTION/'builder.cjs').read_text(),exponent=exponent))))


def run(out,*command):
    print('Run',Path(str(command[1])).name if len(command)>1 else command[0],flush=True)
    with (out/'replay.log').open('a') as log:
        env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None)
        subprocess.run(list(map(str,command)),cwd=REPO,stdout=log,stderr=subprocess.STDOUT,check=True,env=env)


def write_builder(out,source):
    out.mkdir(parents=True,exist_ok=True)
    (out/'builder.cjs').write_text(source)
    run(out,'node',out/'builder.cjs')


def finish(out,weights,expected):
    """Common exact compile/transport/diagonal replay, with explicit expectations."""
    run(out,sys.executable,'-B',CONSTRUCTION/'tools/compile_ir.py',out/'raw-translated-ir.json',out/'compiled')
    run(out,'node',CONSTRUCTION/'tools/checker.cjs','--input',out/'raw-translated-ir.json',
        '--compiled',out/'compiled/compiled-ir.json','--certificate',out/'compiled/reduction-certificate.json',
        '--coordinate-map',out/'compiled/coordinate-map.json','--quartic',out/'compiled/polynomial.json','--report',out/'gate-check.json')
    active,removed=omit_unused(json.loads((out/'compiled/compiled-ir.json').read_text()),json.loads((out/'compiled/coordinate-map.json').read_text()))
    assert [c['name'] for c in removed]==['scalar.preparationU','scalar.preparationV']
    (out/'active-ir.json').write_text(json.dumps(active,indent=2)+'\n')
    run(out,sys.executable,'-B',CONSTRUCTION/'tools/run_pipeline.py',out/'active-ir.json',out/'before-factor','--orders',2)
    candidate=out/'before-factor/integer-candidate-ir.json';ir=json.loads(candidate.read_text())
    n,m=len(ir['coordinates'])-4,len(ir['residuals'])-4
    assert (n,m)==(expected['summary']['coordinates'],expected['summary']['residuals'])
    shutil.copyfile(candidate,out/'candidate-ir.json')
    for name in ['build_transport.py','check_transport.py']:
        code=(TRANSPORT/name).read_text().replace('baseline389-ir.json','candidate-ir.json')
        code=code.replace('385',str(n)).replace('353',str(m))
        code=code.replace("'monomial':[279]","'monomial':[next(c['id'] for c in a['coordinates'] if c['name']=='detector0.Bh.quadratic')]")
        code=code.replace("c['id']==280","c['name']=='detector0.s2.quadratic'")
        (out/name).write_text(code);run(out,sys.executable,'-B',out/name,out)
    run(out,sys.executable,'-B',HERE/'balance.py',out,weights)
    summary=json.loads((out/'balanced/summary.json').read_text())
    assert summary==expected['summary'],summary
    run(out,sys.executable,'-B',HERE/'check_diagonal.py',out,'--weights',weights,
        '--expected-exponent',summary['anchorExponent'],'--expected-coordinates',n,'--expected-residuals',m,
        '--expected-monomials',summary['monomials'],'--expected-max-digits',summary['maximumCoefficientDigits'],
        '--expected-max-bits',summary['maximumCoefficientBits'],'--report',out/'diagonal-check.json')
    for name,status in [('gate-check.json','passed_exact_algebra_checks'),('transport-check.json','PASS'),('diagonal-check.json','PASS')]:
        assert json.loads((out/name).read_text())['status']==status
    gates=json.loads((out/'gate-check.json').read_text())
    assert not gates['gateIdentities']['unverified'] and gates['quarticTableCompared']
    for path,sha in expected['files'].items():assert digest(out/path)==sha,path
    return {'summary':summary,'omittedCoordinates':removed,'arithmeticAcceptance':False,
            'files':{p:digest(out/p) for p in ['builder.cjs','raw-translated-ir.json','final/integer-candidate-ir.json',
                      'balanced/polynomial.json','gate-check.json','transport-check.json','diagonal-check.json']}}


def main():
    if not __debug__:raise RuntimeError('Verification requires Python assertions')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    check_bindings(HERE);out=a.output.resolve()
    assert not out.exists() or not any(out.iterdir())
    assert REPO/'research' not in out.parents
    source=parent_builder();write_builder(out/'baseline',source);write_builder(out,rows(source))
    run(out,sys.executable,'-B',HERE/'check_rows.py',out/'baseline/raw-translated-ir.json',out/'raw-translated-ir.json','--report',out/'row-check.json')
    expected=json.loads((HERE/'EXPECTED.json').read_text())
    result=finish(out,HERE/'DIAGONAL_WEIGHTS.json',expected)
    assert json.loads((out/'row-check.json').read_text())['status']=='PASS'
    result['files']['row-check.json']=digest(out/'row-check.json')
    check_bindings(HERE);(out/'MEASURED.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result['summary'],indent=2),flush=True)


if __name__=='__main__':main()
