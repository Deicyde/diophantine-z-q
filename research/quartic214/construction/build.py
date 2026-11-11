#!/usr/bin/env python3
"""Portable 214 builder from the exact public raw224 stage.
Selected exponents (5,2,4; special 3), weights q,s1,s2,s4.
Standard library only; no defining value of N is selected."""
import json, sys, math, hashlib
from fractions import Fraction as Q
from collections import defaultdict
from pathlib import Path
HERE=Path(__file__).resolve().parent
PARENT=HERE.parents[2] / "research/version15/quartics/quartic-222/provenance/shared-T-redundancy224-006/candidate224-ir.json"
mode="brox"
def rd(r): return {(t['parameterPower'],tuple(sorted(t['monomial']))):Q(t['coefficient']) for t in r['terms']}
def clean(p): return {k:v for k,v in p.items() if v}
def add(*ps):
    o=defaultdict(Q)
    for p in ps:
        for k,v in p.items(): o[k]+=v
    return clean(o)
def scale(p,c): return clean({k:v*c for k,v in p.items()})
def mul(p,q):
    o=defaultdict(Q)
    for (a,m),c in p.items():
        for (b,n),d in q.items(): o[a+b,tuple(sorted(m+n))]+=c*d
    return clean(o)
def V(i): return {(0,(i,)):Q(1)}
ONE={(0,()):Q(1)}
def prim(p):
    den=math.lcm(*(v.denominator for v in p.values())); g=math.gcd(*(int(v*den) for v in p.values()))
    if p[min(p)]<0: g=-g
    return scale(p,Q(den,g))
def ser(p): return [dict(parameterPower=a,monomial=list(m),coefficient=str(v)) for (a,m),v in sorted(p.items())]
src=json.loads(PARENT.read_bytes())
coords={c['id']:dict(c) for c in src['coordinates']}; name={i:c['name'] for i,c in coords.items()}
byname={c['name']:i for i,c in coords.items()}
rows=[(dict((k,v) for k,v in r.items() if k!='terms'),rd(r)) for r in src['residuals']]
assert len(coords)==224 and len(rows)==198
removed={i for i,n in name.items() if '.wPower2.' in n or n.startswith('residue.V1.power4')}
assert len(removed)==10
# definitions of removed coordinates (each linear in exactly one removed coordinate)
defs={}; defrows=set()
for k,(meta,p) in enumerate(rows):
    lin=[x for x in removed if (0,(x,)) in p]
    if len(lin)==1 and meta['name'].endswith('.definition') and ('wPower2' in meta['name'] or 'V1.power4' in meta['name']):
        x=lin[0]; c=p[0,(x,)]
        defs[x]=scale(add(p,scale(V(x),-c)),-1/c); defrows.add(k)
        assert all(len(m)==2 and not set(m)&removed for (_,m) in defs[x])
assert set(defs)==removed and len(defrows)==10
newcoords=[]; changes={}; extra_rows=[]; nextid=max(coords)+1
weightsets=[]
for j in (0,1):
    q=byname[f'detector{j}.q1']; h=byname[f'reflected.detector{j}.weightPower7']
    e2=byname[f'detector{j}.E1.power2.quadratic']; e4=byname[f'detector{j}.E1.power4.quadratic']
    s1,s2,s4=h,e2,e4
    coords[s1]['name']=f'detector{j}.inverseWeight'; coords[s2]['name']=f'detector{j}.inverseWeightSquared'; coords[s4]['name']=f'detector{j}.inverseWeightFourthPower'
    changes[f'detector{j}.E1.power2.definition']=(f'detector{j}.inverseWeight.definition',add(mul(V(q),V(s1)),scale(ONE,-1)))
    changes[f'detector{j}.E1.power4.definition']=(f'detector{j}.inverseWeightSquared.definition',add(mul(V(s1),V(s1)),scale(V(s2),-1)))
    changes[f'reflected.detector{j}.weightPower7.definition']=(f'detector{j}.inverseWeightFourthPower.definition',add(mul(V(s2),V(s2)),scale(V(s4),-1)))
    repl={e2:V(s2), e4:None, h:V(q), q:V(s1)}  # selected exponents (5,2,4; special 3)
    factor_ids={i for i,n in name.items() if n.startswith(f'amplified.det{j}.factor')}; assert len(factor_ids)==10
    weightsets.append((q,h,e2,e4,repl,factor_ids,s4))
    # no other consumers of the three reused slots
    for meta,p in rows:
        if meta['name'].startswith(f'residue.det{j}.factor') or meta['name'] in changes: continue
        assert not any({h,e2,e4}&set(m) for _,m in p), meta['name']
for k,(meta,p) in enumerate(rows):
    for j,(q,h,e2,e4,repl,factor_ids,s4) in enumerate(weightsets):
        if meta['name'].startswith(f'residue.det{j}.factor'):
            out={}
            for (a,m),c in p.items():
                assert a==0
                if not m: term=V(s4)
                elif len(m)==1 and m[0] in factor_ids: term=mul(V(s4),V(m[0]))
                else:
                    hits=[x for x in m if x in repl]; assert len(hits)==1 and len(m)<=2,(meta['name'],m)
                    rest=[x for x in m]; rest.remove(hits[0]); r=repl[hits[0]]
                    if rest:
                        x=rest[0]; term=defs.get(x,V(x))
                        assert (r is None)==(x in removed),(meta['name'],m)
                    else:
                        term=ONE; assert r is not None
                    if r is not None: term=mul(r,term)
                out=add(out,scale(term,c))
            changes[meta['name']]=(meta['name'].replace('.definition','.reciprocal.definition'),out)
final=[]
for k,(meta,p) in enumerate(rows):
    if k in defrows: continue
    if meta['name'] in changes:
        nm,p=changes.pop(meta['name']); meta=dict(meta,name=nm,changed=True)
    assert not any(removed&set(m) for _,m in p), meta['name']
    final.append((meta,p))
assert not changes
final+=[(dict(m,changed=True),p) for m,p in extra_rows]
keep=sorted(i for i in coords if i not in removed); remap={i:k+1 for k,i in enumerate(keep)}
outcoords=[dict(coords[i],id=remap[i],parent224Id=(i if i<=224 else None)) for i in keep]
outrows=[]; poly=defaultdict(int)
for meta,p in final:
    p=prim(p); p={(a,tuple(sorted(remap[x] for x in m))):c for (a,m),c in p.items()}
    assert max(len(m) for _,m in p)<=2 and all(c.denominator==1 for c in p.values())
    outrows.append(dict(meta,id=len(outrows)+1,parent224RowId=meta.get('id'),terms=ser(p)))
    items=list(p.items())
    for (a,m),c in items:
        for (b,n),d in items: poly[a+b,tuple(sorted(m+n))]+=int(c)*int(d)
poly={k:v for k,v in poly.items() if v}
n=len(outcoords)
assert {x for _,m in poly for x in m}==set(range(1,n+1)) and max(len(m) for _,m in poly)==4
prof=defaultdict(dict)
for (a,m),c in poly.items(): prof[m][a]=c
multi=[(m,p) for m,p in prof.items() if len(p)>1]
C0=max(abs(p[0]) for p in prof.values() if set(p)=={0}); L=max((abs(p[1]) for p in prof.values() if 1 in p),default=0)
thr=next(N for N in range(1,300) if 149**(4*N+2)+1>C0 and all(abs(p.get(0,0))+abs(p.get(1,0))*149**(2*N+1)<149**(4*N+2)+1 for p in prof.values() if 2 not in p))
stats=dict(mode=mode,variables=n,quadraticRows=len(outrows),degree=4,content=math.gcd(*poly.values()),coordinateMonomials=len(prof),parameterTerms=len(poly),
 multiParameterProfiles=[{str(a):str(v) for a,v in p.items()} for m,p in multi],constantCoefficientMaximumBits=C0.bit_length(),linearParameterMaximum=str(L),
 coefficientHeightForNAtLeast=thr,coefficientHeight='149^(4N+2)+1',removedParent224Coordinates=sorted(removed),
 removedParent224Rows=sorted(rows[k][0]['id'] for k in defrows),changedRows=[r['name'] for r in outrows if r.get('changed')],
 unchangedRows=sum(1 for r in outrows if not r.get('changed')),parentSha256=hashlib.sha256(PARENT.read_bytes()).hexdigest(),
 thresholdStatus='Existence assertion has a fixed ineffective N0; N>=53 is coefficient-only; public review pending.')
out=HERE/"artifacts"/f'candidate{n}-{mode}'; out.mkdir(parents=True,exist_ok=True)
ir=dict(format='exploratory-quadratic-family',variables=n,inputCoordinate=1,fixedParameter=src['fixedParameter'],coordinates=outcoords,residuals=outrows)
(out/f'candidate{n}-ir.json').write_text(json.dumps(ir,indent=1)+'\n')
(out/f'candidate{n}-polynomial.json').write_text(json.dumps(dict(variables=n,degree=4,inputCoordinate=1,fixedParameter=src['fixedParameter'],terms=ser(poly)))+'\n')
(out/'STATISTICS.json').write_text(json.dumps(stats,indent=1)+'\n')
print(json.dumps({k:v for k,v in stats.items() if k not in('changedRows',)},indent=1))
