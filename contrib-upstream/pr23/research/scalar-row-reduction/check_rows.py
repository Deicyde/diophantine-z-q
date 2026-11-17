"""Exact source-row transport, outside-source comparison and mutation controls.

No builder, producer or symbolic algebra package is imported. Work in the
polynomial ring over Q on the actual named raw coordinates and formal S.
"""
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
import argparse, copy, hashlib, json


def add(*polys):
    out=defaultdict(F)
    for p in polys:
        for m,a in p.items(): out[m]+=a
    return {m:a for m,a in out.items() if a}


def scale(p,a): return {m:v*F(a) for m,v in p.items() if v*a}
def const(a): return {():F(a)} if a else {}
def var(s): return {(s,):F(1)}
def mul(p,q):
    out=defaultdict(F)
    for m,a in p.items():
        for n,b in q.items():out[tuple(sorted(m+n))]+=a*b
    return {m:a for m,a in out.items() if a}


def substitute(p, substitutions):
    result={}
    for m,a in p.items():
        term=const(a)
        for v in m:term=mul(term,substitutions.get(v,var(v)))
        result=add(result,term)
    return result


def decode(data):
    names={c['id']:c['name'] for c in data['coordinates']}
    assert len(names)==len(set(names.values()))==len(data['coordinates'])
    def poly(terms):
        out=defaultdict(F)
        for t in terms:
            assert isinstance(t['sPower'],int) and t['sPower']>=0
            out[tuple(sorted([names[i] for i in t['monomial']]+['$S']*t['sPower']))]+=F(t['coefficient'])
        return {m:a for m,a in out.items() if a}
    rows={r['name']:poly(r['terms']) for r in data['residuals']}
    assert len(rows)==len(data['residuals'])
    return rows,names,poly


def check(old,new):
    O,on,op=decode(old);N,nn,np=decode(new)
    assert old['fixedParameter']==new['fixedParameter']=={'name':'S','value':'3^2010','coordinate':False}
    W='scalar.W2.quadratic';To='scalar.preparationT.quadratic';Tn='scalar.preparationT'
    bh='scalar.Bh.quadratic';en='scalar.normalized_e';rin='scalar.rInverse';norm='scalar.N'
    assert set(on.values())-set(nn.values())=={W,To}
    assert set(nn.values())-set(on.values())=={Tn}
    assert set(O)-set(N)=={'scalar.W2.definition'} and not set(N)-set(O)
    changed={name for name in O.keys()&N.keys() if O[name]!=N[name]}
    arows={f'scalar.shiftedS.rootTimesInverseRoot.definition.{i}' for i in (0,1)}
    trirows={'scalar.preparationT.definition','scalar.Bh.definition','scalar.secondConic'}
    assert changed==arows|trirows,changed
    rowops=[]
    for i,(a,b) in enumerate([(F(-39,8),F(18)),(F(9,2),F(-39,4))]):
        name=f'scalar.shiftedS.rootTimesInverseRoot.definition.{i}'
        assert N[name]==add(O[name],scale(O['S.chart.x.0.definition'],a),scale(O['S.chart.x.1.definition'],b))
        rowops.append({'row':name,'multipliers':[str(a),str(b)]})
    # Decode r from r*ri-1, so the comparison covers the exact input polynomial.
    ri=var(rin);w=var(W);to=var(To);tn=var(Tn);e=var(en);b=var(bh);n2=mul(var(norm),var(norm))
    rr=add(O['scalar.rInverse.definition'],const(1));r={}
    for m,a in rr.items():
        assert m.count(rin)==1
        r[tuple(v for v in m if v!=rin)]=a
    assert mul(r,ri)==rr and N['scalar.rInverse.definition']==O['scalar.rInverse.definition']
    assert O['scalar.W2.definition']==add(w,scale(n2,-1))
    rhs=add(to,scale(O['scalar.preparationT.definition'],-1));L={}
    for m,a in rhs.items():
        assert m.count(W)==1
        L[tuple(v for v in m if v!=W)]=a
    k=F(521079743268,81331739215);mu=F(184460384539620)
    assert O['scalar.Bh.definition']==add(b,scale(mul(e,w),-1),scale(mul(e,to),-k))
    assert scale(add(const(1),scale(L,k)),mu)==scale(r,42)
    assert N['scalar.preparationT.definition']==add(mul(ri,tn),scale(n2,-42))
    assert N['scalar.Bh.definition']==add(b,scale(mul(e,tn),-1))
    assert substitute(N['scalar.secondConic'],{bh:scale(b,mu)})==O['scalar.secondConic']
    # Unique witness equations: T=42*r*N^2 follows without dividing by a variable
    # using r*(ri*T-42*N^2)-T*(r*ri-1)=T-42*r*N^2.
    assert add(mul(r,N['scalar.preparationT.definition']),scale(mul(tn,O['scalar.rInverse.definition']),-1))==add(tn,scale(mul(r,n2),-42))
    private={W,To,Tn,bh}
    for name,p in O.items():
        if name not in trirows|{'scalar.W2.definition'}:assert not any(private&set(m) for m in p),name
    for name,p in N.items():
        if name not in trirows:assert not any(private&set(m) for m in p),name
    # Actual inverse guards, not human-readable denominator annotations.
    def guards(d,p):return {g['name']:(p(g['expression']),p(g['inverse'])) for g in d['guards']}
    assert guards(old,op)==guards(new,np)
    # Gate expressions outside the changed definitions agree after identifying names.
    def gates(d,names,poly):
        residual_names={r['id']:r['name'] for r in d['residuals']};out={}
        def expression(value):
            if value and isinstance(value[0],list):return [poly(x) for x in value]
            return poly(value)
        for g in d['gates']:
            if residual_names[g['definitionResidualId']] in changed|{'scalar.W2.definition'}:continue
            x={k:v for k,v in g.items() if k not in {'coordinateId','definitionResidualId','sourceLines','expression','numerator','denominator'}}
            for k in ('expression','numerator','denominator'):
                if k in g:x[k]=expression(g[k])
            out[names[g['coordinateId']]]=x
        return out
    assert gates(old,on,op)==gates(new,nn,np)
    return {'status':'PASS','changedRows':sorted(changed),'deletedRow':'scalar.W2.definition',
            'rowOperations':rowops,'BhForwardScale':str(mu),'unchangedCommonRows':len(O.keys()&N.keys())-len(changed),
            'outsideGatesAndGuardsIdentical':True,'uniqueBidirectionalScalarTransport':True,
            'scope':'Exact source equations over Q with r*ri=1; inherited arithmetic and compiler/diagonal checks separate.'}


def controls(old,new):
    targets=['scalar.preparationT.definition','scalar.Bh.definition','scalar.secondConic',
             'scalar.shiftedS.rootTimesInverseRoot.definition.0','scalar.rInverse.definition']
    for name in targets:
        bad=copy.deepcopy(new)
        row=next(r for r in bad['residuals'] if r['name']==name)
        row['terms'][0]['coefficient']=str(F(row['terms'][0]['coefficient'])+1)
        try:check(old,bad)
        except AssertionError:continue
        raise AssertionError('Accepted corrupted row '+name)
    return targets


def main():
    if not __debug__:raise RuntimeError('Verification requires Python assertions')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('old',type=Path);ap.add_argument('new',type=Path);ap.add_argument('--report',type=Path,required=True);a=ap.parse_args()
    old=json.loads(a.old.read_text());new=json.loads(a.new.read_text());result=check(old,new)
    result['rejectedCorruptions']=controls(old,new)
    result['sources']={label:hashlib.sha256(p.read_bytes()).hexdigest() for label,p in [('old',a.old),('new',a.new)]}
    a.report.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))


if __name__=='__main__':main()
