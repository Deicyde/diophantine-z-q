"""Build variant IR (optionally with 3-power chain offsets and f-anchor), precise-LP, round, bake offsets, measure."""
import json, sys, copy, math
from fractions import Fraction as Fr
sys.path.insert(0,'lp'); sys.path.insert(0,'measure')
import variants as V
from offsets import add_offsets
from precise_lp import solve as psolve
from balance_any import balance
def bake(d, pw):
    """remove OFFSET fake coords: multiply their term coefficient by 3^a (2^b must be 0)."""
    d=copy.deepcopy(d); fakes={c['id']:c['name'] for c in d['coordinates'] if c['name'].startswith('OFFSET')}
    for r in d['residuals']:
        for t in r['terms']:
            for f in [i for i in t['monomial'] if i in fakes]:
                a,b=pw.get(fakes[f],[0,0]); assert b==0
                t['coefficient']=str(Fr(t['coefficient'])*Fr(3)**a); t['monomial']=[i for i in t['monomial'] if i!=f]
    d['coordinates']=[c for c in d['coordinates'] if c['id'] not in fakes]
    return d
def run(name, d, fixb=()):
    Z,a,b=psolve(d, fix=('input',)+tuple(fixb))
    pw={k:[round(a[k]),round(b[k])] for k in a}
    offs={k:v for k,v in pw.items() if k.startswith('OFFSET')}
    dd=bake(d,pw)
    pw={k:v for k,v in pw.items() if not k.startswith('OFFSET') and (v[0] or v[1])}
    r=balance(dd,pw); r.pop('_poly')
    json.dump(dd,open(f'measure/{name}_ir.json','w')); json.dump(pw,open(f'measure/{name}_powers.json','w'),indent=1)
    print(name,'LPdigits~%.1f'%(2*Z/math.log(10)),'MEASURED',r['maximumCoefficientDigits'],'digits',r['maxCoefficientFactor'][-40:] if len(r['maxCoefficientFactor'])<60 else '', 'coords',r['activeCoordinates'],'rows',r['residuals'],'monos',r['monomials'],'x0^4',r['inputFourthPowerCoefficient'][:20],'offsets',offs, flush=True)
    return r
if __name__=='__main__':
    H=json.load(open('greedy2_ir.json'))
    CH=[('scalar.chain3.definition','scalar.shiftedS.f.1'),('scalar.chain2.definition','scalar.shiftedS.f.0')]
    which=sys.argv[1:]
    if 'B' in which:
        d=add_offsets(H,CH); fk=[c['name'] for c in d['coordinates'] if c['name'].startswith('OFFSET')]
        run('B_hsub_chainoff', d, fixb=())
    if 'C' in which:
        V.d0=H; d=add_offsets(V.fanchor(2),CH)
        run('C_hsub_chainoff_fanchor', d)
