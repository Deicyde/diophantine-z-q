"""Research experiment: transport Version 13's four conic factorizations.

This preserves the inherited arithmetic dependencies. It does not confer
independent mathematical acceptance on the changed construction.
"""
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
from math import gcd, lcm
import argparse
import hashlib
import json

def readpoly(ts):
    return {tuple([-1]*t['sPower']+t['monomial']): F(t['coefficient']) for t in ts}

def clean(p):
    return {m:c for m,c in p.items() if c}

def add(*ps):
    out = defaultdict(F)
    for p in ps:
        for m,c in p.items(): out[m] += c
    return clean(out)

def scale(p,c): return clean({m:a*c for m,a in p.items()})
def var(i): return {(i,): F(1)}

def mul(a,b):
    out = defaultdict(F)
    for m,c in a.items():
        for n,d in b.items(): out[tuple(sorted(m+n))] += c*d
    return clean(out)

def sub(p, mapping):
    out = {}
    for m,c in p.items():
        term = {(): c}
        for i in m: term = mul(term, mapping.get(i,var(i)))
        out = add(out,term)
    return out

def norm(p):
    den = lcm(*(c.denominator for c in p.values()))
    g = gcd(*(int(c*den) for c in p.values()))
    if p[min(p)] < 0: g = -g
    return scale(p,F(den,g)), F(g,den)

def encode(p):
    return [{'sPower':m.count(-1),'monomial':[i for i in m if i != -1],
             'coefficient':str(c)} for m,c in sorted(p.items())]

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(root,name,obj):
    p=root/name; p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(obj,indent=2)+'\n')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('construction', type=Path)
    args = parser.parse_args()
    root = args.construction.resolve()
    source = root/'baseline389-ir.json'
    d=json.loads(source.read_text()); names={c['name']:c['id'] for c in d['coordinates']}
    rows={r['name']:r for r in d['residuals']}; updated={}; removed=set(); certificates=[]
    for prefix in ['detector0','detector1','detector2','scalar']:
        s,q,h,s2,q2=[names[prefix+x] for x in ['.s','.q','.Bh.quadratic','.s2.quadratic','.q2.quadratic']]
        H=readpoly(d['values'][prefix+'.Bh']['terms'])
        alpha=H[(h,)]; rest=add(H,scale(var(h),-alpha))
        b=readpoly(d['values'][prefix+'.B' if prefix!='scalar' else 'scalar.correctedR']['terms'])
        assert len(H)==2 and alpha != 0
        allowed={prefix+x for x in ['.Bh.definition','.s2.definition','.q2.definition','.secondConic']}
        actual={r['name'] for r in d['residuals'] if any(set(t['monomial'])&{h,q,s2,q2} for t in r['terms'])}
        assert actual==allowed, (prefix, actual)
        old_expected=add(scale(mul(b,var(q2)),17),scale(mul(H,H),3),
                         scale(mul(var(s2),H),-2),scale(mul(var(s2),var(s2)),-1))
        assert norm(readpoly(rows[prefix+'.secondConic']['terms']))[0]==norm(old_expected)[0]
        # Repurpose h as v with H=s*v, q as Q, q2 as Q^2; delete s2.
        lift={h:scale(add(mul(var(s),var(h)),scale(rest,-1)),1/alpha),
              q:mul(var(s),var(q)),q2:mul(mul(var(s),var(s)),var(q2)),
              s2:mul(var(s),var(s))}
        assert sub(H,lift)==mul(var(s),var(h))
        new_expected=add(scale(mul(b,var(q2)),17),scale(mul(var(h),var(h)),3),
                         scale(mul(var(s),var(h)),-2),scale(mul(var(s),var(s)),-1))
        assert sub(old_expected,lift)==mul(mul(var(s),var(s)),new_expected)
        assert sub(readpoly(rows[prefix+'.s2.definition']['terms']),lift)=={}
        newraw={prefix+'.Bh.definition':sub(readpoly(rows[prefix+'.Bh.definition']['terms']),lift),
                prefix+'.q2.definition':add(mul(var(q),var(q)),scale(var(q2),-1)),
                prefix+'.secondConic':new_expected}
        for name,p in newraw.items():
            assert max(sum(i!=-1 for i in m) for m in p)<=2
            updated[name]=dict(rows[name],terms=encode(norm(p)[0]))
        removed.add(s2)
        certificates.append({'prefix':prefix,'s':s,'newV':h,'newQ':q,'newQSquare':q2,'removedSquare':s2,
            'semanticOldH':encode(H),'positiveConicInput':encode(b),
            'reverseLift':{str(i):encode(p) for i,p in lift.items()},
            'privateConsumerRows':sorted(actual),
            'normalizedNewRows':{name:updated[name]['terms'] for name in newraw},
            'zeroBranch':'Old s=0 implies 17*b*q^2+3*H^2=0. Since b>0, q=H=0. Set new v=Q=Q2=0.',
            'nonzeroBranch':'For old s!=0, v=H/s, Q=q/s, Q2=Q^2. Reverse uses H=s*v, old q=s*Q, old q2=s^2*Q2, old s2=s^2.'})
    result={'format':'hybrid385-research-quadratic-ir-v1','fixedParameter':d['fixedParameter'],
        'status':'Experimental author result; exact finite transport checked, independent acceptance pending.',
        'coordinates':[dict(c,name=c['name'].replace('.Bh.quadratic','.factored_v') if c['id'] in {r['newV'] for r in certificates} else c['name']) for c in d['coordinates'] if c['id'] not in removed],
        'residuals':[updated.get(r['name'],r) for r in d['residuals'] if r['name'] not in {c['prefix']+'.s2.definition' for c in certificates}]}
    assert len(result['coordinates'])==385 and len(result['residuals'])==353
    assert not any(set(t['monomial'])&removed for r in result['residuals'] for t in r['terms'])
    write(root,'final/integer-candidate-ir.json',result)
    write(root,'transport-certificate.json',{'source':source.name,'sourceSha256':sha(source),
        'candidateSha256':sha(root/'final/integer-candidate-ir.json'),'blocks':certificates,
        'scope':'Four pointwise rational projection equivalences, using positivity already supplied by the proposal. No new global theorem or independent acceptance.'})
    print(json.dumps({'coordinates':385,'residuals':353,'changedRows':len(updated),'deletedRows':4,'outsideRowsUnchanged':len(d['residuals'])-16,'sourceSha256':sha(source),'candidateSha256':sha(root/'final/integer-candidate-ir.json')},indent=2))

if __name__=='__main__': main()
