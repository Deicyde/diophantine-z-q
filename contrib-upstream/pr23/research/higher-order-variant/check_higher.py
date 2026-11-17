"""Check actual changed source, inverse powers and finite arithmetic margins."""
from pathlib import Path
from fractions import Fraction as F
import argparse, copy, hashlib, json, sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'scalar-row-reduction'))
from check_rows import decode, add, mul, scale, var


def canonical(s):
    for a,b in [('q50','q46'),('E50','E46'),('.50.','.46.'),('q1FourthForWeights','E1.power4')]:s=s.replace(a,b)
    return s


def source_check(old,new):
    assert old['fixedParameter']=={'name':'S','value':'3^2010','coordinate':False}
    assert new['fixedParameter']=={'name':'S','value':'3^1512','coordinate':False}
    # Align the high-order names and the fourth-power slot shared by the builder.
    new=copy.deepcopy(new)
    for key in ['coordinates','residuals']:
        for x in new[key]:x['name']=canonical(x['name'])
    O,on,op=decode(old);N,nn,np=decode(new)
    removed={f'detector{i}.{s}.definition' for i in range(3) for s in ['q1Sixth','q1Twelfth']}
    added={f'detector{i}.{s}.definition' for i in range(3) for s in ['q1Eighth','q1InverseSeventh']}|{'scalar.rInverse31.definition'}
    changed={f'detector{i}.{s}.definition' for i in range(3) for s in ['q12','q46']}|{'scalar.ratioProxyLeaf.definition'}
    assert O.keys()-N.keys()==removed and N.keys()-O.keys()==added
    assert {k for k in O.keys()&N.keys() if O[k]!=N[k]}==changed
    assert set(on.values())-set(nn.values())=={x.replace('.definition','.quadratic') for x in removed}
    added_c={f'detector{i}.{s}' for i in range(3) for s in ['q1Eighth.quadratic','q1InverseSeventh']}|{'scalar.rInverse31'}
    assert set(nn.values())-set(on.values())==added_c
    def guards(d,p):return {g['name']:(p(g['expression']),p(g['inverse'])) for g in d['guards']}
    assert guards(old,op)==guards(new,np)
    av={k:op(v['terms']) for k,v in old['values'].items()}
    bv={canonical(k):np(v['terms']) for k,v in new['values'].items()}
    # The renamed fourth-power alias and its old name must identify the same slot.
    for k,v in new['values'].items():assert bv[canonical(k)]==np(v['terms'])
    assert av.keys()-bv.keys()=={x.removesuffix('.definition') for x in removed}
    assert bv.keys()-av.keys()=={x.removesuffix('.definition') for x in added}
    for k in av.keys()&bv.keys():assert av[k]==bv[k],k
    def gates(d,names,poly):
        rows={r['id']:r['name'] for r in d['residuals']};out={}
        def expression(v):return [poly(x) for x in v] if v and isinstance(v[0],list) else poly(v)
        for g in d['gates']:
            if rows[g['definitionResidualId']] in removed|added|changed:continue
            x={k:canonical(v) if isinstance(v,str) else v for k,v in g.items() if k not in {'coordinateId','definitionResidualId','sourceLines','dependencies','expression','numerator','denominator','output'}}
            x['dependencies']=sorted(names[i] for i in g['dependencies'])
            for k in ['expression','numerator','denominator','output']:
                if k in g:x[k]=expression(g[k])
            out[names[g['coordinateId']]]=x
        return out
    assert gates(old,on,op)==gates(new,nn,np)
    rows={r['id']:r['name'] for r in new['residuals']}
    for g in new['gates']:
        name=rows[g['definitionResidualId']]
        if name not in added|changed:continue
        output=var(nn[g['coordinateId']])
        if g['operation']=='quadratic_assignment':wanted=add(output,scale(np(g['expression']),-1))
        else:
            assert g['operation']=='rational_quotient'
            wanted=add(mul(output,np(g['denominator'])),scale(np(g['numerator']),-1))
        assert N[name]==wanted,name
    names={c['name']:c['id'] for c in new['coordinates']};gg={g['coordinateId']:g for g in new['gates']}
    decoded=[]
    for r in range(3):
        prefix=f'detector{r}.';powers={names[prefix+'q1']:1}
        def expression(ts):
            assert len(ts)==1;t=ts[0];assert F(t['coefficient'])==1 and t['sPower']==0
            return sum(power(i) for i in t['monomial'])
        def power(i):
            if i not in powers:
                g=gg[i]
                if g['operation']=='quadratic_assignment':v=expression(g['expression'])
                else:
                    assert g['operation']=='rational_quotient'
                    v=expression(g['numerator'])-expression(g['denominator'])
                powers[i]=v
            return powers[i]
        expected={'q1SquaredForWeights.quadratic':2,'q1CubedForWeights.quadratic':3,
                  'E1.power4.quadratic':4,'q1Eighth.quadratic':8,'q1InverseSeventh':-7,
                  'q12':23,'mixedHigh.quadratic':46,'q46':99,
                  'E46.power2.quadratic':198,'E46.power3.quadratic':297}
        for name,e in expected.items():assert power(names[prefix+name])==e
        decoded.append(expected)
    # Check scalar quotients against the actual r and proxy expressions, not labels.
    rr=bv['scalar.r'];proxy=bv['scalar.ratioProxyReal'];previous=var('scalar.rInverse15')
    assert N['scalar.rInverse31.definition']==add(mul(rr,var('scalar.rInverse31')),scale(mul(previous,previous),-1))
    assert N['scalar.ratioProxyLeaf.definition']==add(mul(rr,var('scalar.ratioProxyLeaf')),scale(mul(proxy,var('scalar.rInverse31')),-1))
    return {'removedRows':sorted(removed),'addedRows':sorted(added),'changedRows':sorted(changed),
            'unchangedCommonRows':len(O.keys()&N.keys())-len(changed),'actualMonomialPowers':decoded,
            'scalarLeaf':'Tproxy/r^32; inner coefficient remains r^-15',
            'note':'Canonical high names and shared fourth-power slot; formal expressions agree outside listed changes. Evaluated N,W,trace,B change.'}


def finite_checks():
    bounds=[F(1,4),F(31,4),F(31,8),F(91,8),F(91,16),F(211,16),F(211,32),F(451,32)]
    assert (F(-1,2)+1)/2==bounds[0] and (F(-1,2)+16)/2==bounds[1]
    for a,b,c in [(1,2,3),(3,4,5),(5,6,7)]:
        assert bounds[a]/2==bounds[b] and (bounds[a]+15)/2==bounds[c]
    assert bounds[-1]+32==F(1475,32)>46
    for R in range(1,32):
        L=16*R+1
        assert min(2*L,2*L-15*R)-R>=16*R+2
        assert 48*R+1-32*R==L
    orders=[1,12,50]
    for m in orders:assert 2*m-1-2*(2*m-1)==-(2*m-1)
    delta=[98*x-1 for x in [F(0),F(1,49),F(1,50),F(1,2450),F(32,1225)]]
    assert delta==[F(-1),F(1),F(24,25),F(-24,25),F(39,25)]
    for d in delta:
        for z in [abs(d.numerator),d.denominator]:
            for p in [2,3,5,7,13,17]:
                while z%p==0:z//=p
            assert z==1
    H=3*2**106*(2**32*3**9)**6*46410**18+128;c=2*3**755;b=c-1
    assert 8**1504*c**927>(25*H)**1504
    assert (2*(b*b-6))**1600>(3*H+14)**1600*(2*b**4+6*b**3+5*b*b+1)**577
    assert 64*50-2308==892 and 40*H<2**670 and b>67000
    assert F(4712,4775)*301+F(4616,4775)<298
    return {'scalarStrictBounds':list(map(str,bounds)),'proxyBound':'1475/32','radicalOrder':47,
            'orders':orders,'deltaValues':list(map(str,delta)),
            'localNuAndS':[[2*m-1,4*(2*m-1)] for m in orders],
            'realDecayPowers':[-(2*m-1) for m in orders],'precisionAvailable':51,
            'anchorExponent':1512,'allThreeHeightConsumers':True,'LucasEndpointExponent':892}


def main():
    if not __debug__:raise RuntimeError('Run without Python optimization')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('old',type=Path);ap.add_argument('new',type=Path);ap.add_argument('--report',type=Path,required=True);a=ap.parse_args()
    old=json.loads(a.old.read_text());new=json.loads(a.new.read_text());result=source_check(old,new)
    mutations=[]
    for name in ['detector0.q12.definition','detector1.q50.definition','scalar.rInverse31.definition','scalar.ratioProxyLeaf.definition','scalar.chain3.definition']:
        bad=copy.deepcopy(new);r=next(x for x in bad['residuals'] if x['name']==name);r['terms'][0]['coefficient']=str(F(r['terms'][0]['coefficient'])+1);mutations.append((name,bad))
    bad=copy.deepcopy(new);bad['guards']=[];mutations.append(('missing guards',bad))
    bad=copy.deepcopy(new);bad['fixedParameter']['value']='3^1506';mutations.append(('wrong anchor',bad))
    for name,bad in mutations:
        try:source_check(old,bad)
        except (AssertionError,KeyError):continue
        raise AssertionError('Accepted corrupted source '+name)
    report={'status':'PASS','sourceComparison':result,'finite':finite_checks(),'negativeControlsRejected':[n for n,_ in mutations],
            'files':{n:hashlib.sha256(p.read_bytes()).hexdigest() for n,p in [('before',a.old),('after',a.new)]},
            'scope':'Exact source/gate and finite margin checks; uniform arithmetic proof needs separate review.'}
    a.report.write_text(json.dumps(report,indent=2)+'\n');print('PASS: actual higher-order source, margins and seven negative controls')


if __name__=='__main__':main()
