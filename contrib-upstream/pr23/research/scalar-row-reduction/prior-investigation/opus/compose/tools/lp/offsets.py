import json, sys, copy
sys.path.insert(0, __file__.rsplit('/',1)[0])
from lp import solve
def add_offsets(d, spec):
    """spec: list of (rowname, coordname-in-term) -> multiply that term by a free fake coordinate."""
    d=copy.deepcopy(d)
    for rn,cn in spec:
        cid=next(c['id'] for c in d['coordinates'] if c['name']==cn)
        r=next(r for r in d['residuals'] if r['name']==rn)
        nid=max(c['id'] for c in d['coordinates'])+1
        d['coordinates'].append({'id':nid,'name':'OFFSET:'+rn,'kind':'fake'})
        for t in r['terms']:
            if cid in t['monomial']: t['monomial']=t['monomial']+[nid]
    return d
CHAIN=[('scalar.chain3.definition','scalar.shiftedS.f.1'),('scalar.chain2.definition','scalar.shiftedS.f.0'),
       ('scalar.chain1.definition','H.chart.x.1.quadratic'),('scalar.N.definition','H.chart.x.0.quadratic')]
if __name__=='__main__':
    d=json.load(open(sys.argv[1]))
    v,w,_=solve(add_offsets(d,CHAIN))
    print({k:str(x) for k,x in w.items() if k.startswith('OFFSET')})
