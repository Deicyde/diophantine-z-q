"""Balance a build with LP weights (Fractions of E). usage: lpbalance.py BUILD LPW.json E DEN [--two]"""
import json,sys,subprocess,os,shutil,re
from fractions import Fraction as F
from pathlib import Path
build=Path(sys.argv[1]); lpw=json.load(open(sys.argv[2])); E=int(sys.argv[3]); den=int(sys.argv[4])
two={'S.chart.x.0.quadratic':1,'heightProduct.scale0.quadratic':-21} if '--two' in sys.argv else {}
three={k:int(F(v)*den) for k,v in lpw.items()}
assert all(F(v)*den==int(F(v)*den) for v in lpw.values())
# copy build with changed fixed parameter
tmp=build.parent/(build.name+f'_E{E}_d{den}'+('_two' if two else ''))
if tmp.exists(): shutil.rmtree(tmp)
(tmp/'final').mkdir(parents=True)
d=json.loads((build/'final/integer-candidate-ir.json').read_text()); d['fixedParameter']['value']=f'3^{E}'
(tmp/'final/integer-candidate-ir.json').write_text(json.dumps(d))
(tmp/'w.json').write_text(json.dumps({'three':three,'two':two}))
env=dict(os.environ,UNIT_DEN=str(den))
r=subprocess.run([sys.executable,'-B',str(Path(__file__).parent/'balance_frac.py'),str(tmp),'--weights',str(tmp/'w.json')],env=env,capture_output=True,text=True)
if r.returncode: print(r.stderr[-2000:]); sys.exit(1)
s=json.loads((tmp/'balanced/summary.json').read_text()); print(json.dumps({k:s[k] for k in ['coordinates','residuals','monomials','maximumCoefficientDigits','integerContent','inputFourthPowerCoefficient','anchorExponent']}))
