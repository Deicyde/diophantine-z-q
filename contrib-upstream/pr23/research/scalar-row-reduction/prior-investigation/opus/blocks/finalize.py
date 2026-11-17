"""Run the remaining #13 pipeline stages (omission, run_pipeline, four pole transports) on a measured run."""
import json,subprocess,sys,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'tools_copy'))
def omit_unused(data, cmap):
    free=set(cmap['omittedFreeCoordinates'])
    assert not any(free & set(t['monomial']) for r in data['residuals'] for t in r['terms'])
    r=dict(data); r['coordinates']=[c for c in data['coordinates'] if c['id'] not in free]; return r
def finalize(name):
    out=HERE/'runs'/name
    log=(out/'final.log').open('w')
    run=lambda *c: subprocess.run([str(x) for x in c],cwd=out,stdout=log,stderr=subprocess.STDOUT,check=True)
    active=omit_unused(json.loads((out/'compiled/compiled-ir.json').read_text()),json.loads((out/'compiled/coordinate-map.json').read_text()))
    (out/'active-ir.json').write_text(json.dumps(active,indent=2)+'\n')
    if (out/'before-factor').exists(): shutil.rmtree(out/'before-factor')
    run(sys.executable,'-B',HERE/'construction/tools/run_pipeline.py',out/'active-ir.json',out/'before-factor','--orders',2)
    ir=json.loads((out/'before-factor/integer-candidate-ir.json').read_text())
    n,m=len(ir['coordinates'])-4,len(ir['residuals'])-4
    shutil.copyfile(out/'before-factor/integer-candidate-ir.json',out/'candidate-ir.json')
    for nm in ['build_transport.py','check_transport.py']:
        code=(HERE/'tools_copy'/nm).read_text().replace('baseline389-ir.json','candidate-ir.json')
        code=code.replace('385',str(n)).replace('353',str(m))
        code=code.replace("'monomial':[279]","'monomial':[next(c['id'] for c in a['coordinates'] if c['name']=='detector0.Bh.quadratic')]")
        code=code.replace("c['id']==280","c['name']=='detector0.s2.quadratic'")
        (out/nm).write_text(code)
        run(sys.executable,'-B',out/nm,out)
    fin=json.loads((out/'final/integer-candidate-ir.json').read_text())
    return len(ir['coordinates']),len(fin['coordinates']),len(fin['residuals']),json.loads((out/'transport-check.json').read_text())['status']
if __name__=='__main__':
    for n in sys.argv[1:]: print(n,finalize(n),flush=True)
