import json,subprocess,sys,itertools,shutil
from pathlib import Path
D=Path(__file__).parent; build=Path(sys.argv[1])
base={'S.chart.h0':1,'S.chart.h1':1,'S.chart.x.0.quadratic':1,'S.chart.x.1.quadratic':1,
 'anchor.U':4,'anchor.V':4,'anchor.W':4,'anchor.physicalA.quadratic':4}
two={'S.chart.x.0.quadratic':1,'heightProduct.scale0.quadratic':-21}
best=None
for wt in [0,1,2,3]:
  for wy in [0,1]:
    w=dict(base); w['scalar.shiftedS.tau.0']=wt; w['scalar.shiftedS.tau.1']=wt
    if wy: w['scalar.ratioProxyReal.quadratic']=wy
    (D/'w.json').write_text(json.dumps({'three':w,'two':two}))
    r=subprocess.run([sys.executable,'-B',str(D/'balance_var.py'),str(build),'--weights',str(D/'w.json')],capture_output=True,text=True)
    if r.returncode: print(wt,wy,'ERR',r.stderr.strip().splitlines()[-1]); continue
    s=json.loads((build/'balanced/summary.json').read_text())
    print(wt,wy,s['maximumCoefficientDigits'],s['monomials'],flush=True)
