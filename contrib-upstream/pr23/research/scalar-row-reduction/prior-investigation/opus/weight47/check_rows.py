"""Compare raw IR rows of the R-inverse order-47 source with the #13 order-47 (383) raw IR,
and verify every changed/added weight row by exact rational-function evaluation."""
import json, sys, random
from fractions import Fraction as Fr
base=json.load(open(sys.argv[1])); new=json.load(open(sys.argv[2]))
def named(d):
    names={c['id']:c['name'] for c in d['coordinates']}
    return {r['name']:{(t['sPower'],tuple(sorted(names[i] for i in t['monomial']))):Fr(t['coefficient']) for t in r['terms']} for r in d['residuals']}
a,b=named(base),named(new)
print('deleted rows:',sorted(a.keys()-b.keys()))
print('added rows:',sorted(b.keys()-a.keys()))
print('changed rows:',sorted(n for n in a.keys()&b.keys() if a[n]!=b[n]))
print('guards equal:', [ {k:v for k,v in g.items() if k!='sourceLines'} for g in base['guards']]==[{k:v for k,v in g.items() if k!='sourceLines'} for g in new['guards']] if len(base['guards'])==len(new['guards']) else 'len differs')
ca={c['name'] for c in base['coordinates']}; cb={c['name'] for c in new['coordinates']}
print('coords removed:',sorted(ca-cb)); print('coords added:',sorted(cb-ca))
# exact check: evaluate each detector's weight rows at random rational t (and A) using semantic formulas
cs=[Fr(1)]
for root in [Fr(0),Fr(1,49),Fr(1,50),Fr(1,2450),Fr(32,1225)]:
    o=[Fr(0)]*(len(cs)+1)
    for j,c in enumerate(cs): o[j]-=root*c; o[j+1]+=c
    cs=o
def Fp(t): return sum(c*t**j for j,c in enumerate(cs))
for trial in range(5):
  t=Fr(random.randint(2,900),random.randint(1,97))+Fr(1,3); A=Fr(random.randint(1,50),random.randint(1,7))**2
  delta=98*t-1; e=(A*delta)**5/Fp(t); q1=e/delta; E=e*delta
  val={'q1':q1,'eDelta.quadratic':E,'q1CubedForWeights.quadratic':q1**3,'Rinv':1/E,'qFive':e**5/delta,'qEleven':e**11/delta,
       'q12':e**23/delta,'mixedHigh.quadratic':e**46/delta**2,'q47':e**93/delta**3}
  for r in range(3):
    p=f'detector{r}.'
    for row in ['Rinv','qFive','qEleven','q12','mixedHigh','q47']:
        terms=b[p+row+'.definition']; s=Fr(0)
        for (sp_,mon),c in terms.items():
            assert sp_==0; v=c
            for nm in mon: v*=val[nm[len(p):]]
            s+=v
        assert s==0,(p+row,trial)
print('all 18 weight rows vanish exactly at 5 random rational (t,A) points')
