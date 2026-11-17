import json, copy, sys
sys.path.insert(0, __file__.rsplit('/',1)[0])
from lp import solve
BASE='/tmp/codex-glazer389-review-3j08z564/cube/build/final380/final/integer-candidate-ir.json'
d0=json.load(open(BASE))
def cid(d,name): return next(c['id'] for c in d['coordinates'] if c['name']==name)
def row(d,name): return next(r for r in d['residuals'] if r['name']==name)
def T(c,mono,s=0): return {'sPower':s,'monomial':sorted(mono),'coefficient':str(c)}

def fanchor(k=2, a=None, b=None):
    """anchor uses N(f) with S^k on input part (f has double depth -> k=2)."""
    d=copy.deepcopy(d0)
    f0,f1=cid(d,'scalar.shiftedS.f.0'),cid(d,'scalar.shiftedS.f.1')
    A=cid(d,'anchor.physicalA.quadratic')
    r=row(d,'anchor.physicalA.definition')
    rest=[t for t in r['terms'] if t['sPower']==1]
    for t in rest: t['sPower']=k
    r['terms']=[T(1,[f0,f0]),T(-2,[f1,f1]),T(-1,[A])]+rest
    e=row(d,'anchor.translatedEquation')
    for t in e['terms']:
        if t['sPower']==1: t['sPower']=k
    return d
if __name__=='__main__':
    print('== f anchor, S^2'); solve(fanchor(2))

from fractions import Fraction as Fr
def gate_expr(d, name):
    """expression (list of terms) defining coordinate `name` by its definition row: row = expr - coord."""
    c=cid(d,name)
    for r in d['residuals']:
        ts=[t for t in r['terms'] if t['monomial']==[c]]
        if r['kind']=='gate' and len(ts)==1 and all(c not in t['monomial'] for t in r['terms'] if t is not ts[0]):
            k=Fr(ts[0]['coefficient'])
            return [ {'sPower':t['sPower'],'monomial':t['monomial'],'coefficient':Fr(t['coefficient'])/(-k)} for t in r['terms'] if t is not ts[0]], r['name']
    raise KeyError(name)
def inline(d, rowname, coordname, only_linear=True):
    """replace degree-1 occurrences of coord in row by its gate expression (keeps degree <=2)."""
    r=row(d,rowname); c=cid(d,coordname); expr,_=gate_expr(d,coordname)
    acc={}
    def addt(s,mono,coef):
        key=(s,tuple(sorted(mono))); acc[key]=acc.get(key,Fr(0))+coef
    for t in r['terms']:
        if t['monomial']==[c]:
            for e in expr: addt(t['sPower']+e['sPower'], e['monomial'], Fr(t['coefficient'])*e['coefficient'])
        else: addt(t['sPower'],t['monomial'],Fr(t['coefficient']))
    r['terms']=[{'sPower':s,'monomial':list(m),'coefficient':str(v)} for (s,m),v in acc.items() if v]
    assert all(len(t['monomial'])<=2 for t in r['terms'])
    return d
def hsub():
    d=copy.deepcopy(d0)
    for rn in ['scalar.shiftedS.rootTimesInverseRoot.definition.0','scalar.shiftedS.rootTimesInverseRoot.definition.1']:
        for cn in ['S.chart.x.0.quadratic','S.chart.x.1.quadratic']:
            inline(d,rn,cn)
    return d
if __name__=='__main__':
    print('== inline x=h^2 in w rows'); solve(hsub())
