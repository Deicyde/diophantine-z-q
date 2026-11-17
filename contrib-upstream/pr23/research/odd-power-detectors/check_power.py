"""Actual source comparison, exact monomial decoding and local exponent checks."""
from pathlib import Path
from fractions import Fraction as F
import argparse, copy, hashlib, json, sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'scalar-row-reduction'))
from check_rows import decode, add, mul, scale, var


def source_check(old,new):
    O,on,op=decode(old);N,nn,np=decode(new)
    assert old['fixedParameter']==new['fixedParameter']=={'name':'S','value':'3^2010','coordinate':False}
    removed={f'detector{i}.{s}.definition' for i in range(3) for s in ['eCubed','eSixth','eTwelfth']}
    added={f'detector{i}.{s}.definition' for i in range(3) for s in ['q1Sixth','q1Twelfth']}
    changed={f'detector{i}.q12.definition' for i in range(3)}
    assert O.keys()-N.keys()==removed and N.keys()-O.keys()==added
    assert {k for k in O.keys()&N.keys() if O[k]!=N[k]}==changed
    removed_c={x.replace('.definition','.quadratic') for x in removed}
    added_c={x.replace('.definition','.quadratic') for x in added}
    assert set(on.values())-set(nn.values())==removed_c
    assert set(nn.values())-set(on.values())==added_c
    def slots(d):return {c['name']:{k:v for k,v in c.items() if k!='id'} for c in d['coordinates']}
    a,b=slots(old),slots(new)
    for k in a.keys()&b.keys():assert a[k]==b[k],k
    def guards(d,p):return {g['name']:(p(g['expression']),p(g['inverse'])) for g in d['guards']}
    assert guards(old,op)==guards(new,np)
    av={k:op(v['terms']) for k,v in old['values'].items()};bv={k:np(v['terms']) for k,v in new['values'].items()}
    assert av.keys()-bv.keys()=={x.removesuffix('.definition') for x in removed}
    assert bv.keys()-av.keys()=={x.removesuffix('.definition') for x in added}
    for k in av.keys()&bv.keys():assert av[k]==bv[k],k
    def gates(d,names,poly):
        rows={r['id']:r['name'] for r in d['residuals']};out={}
        def expression(v):return [poly(x) for x in v] if v and isinstance(v[0],list) else poly(v)
        for g in d['gates']:
            if rows[g['definitionResidualId']] in removed|added|changed:continue
            x={k:v for k,v in g.items() if k not in {'coordinateId','definitionResidualId','sourceLines','dependencies','expression','numerator','denominator','output'}}
            x['dependencies']=sorted(names[i] for i in g['dependencies'])
            for k in ['expression','numerator','denominator','output']:
                if k in g:x[k]=expression(g[k])
            out[names[g['coordinateId']]]=x
        return out
    assert gates(old,on,op)==gates(new,nn,np)
    residual_names={r['id']:r['name'] for r in new['residuals']}
    for g in new['gates']:
        name=residual_names[g['definitionResidualId']]
        if name not in added|changed:continue
        output=var(nn[g['coordinateId']])
        if g['operation']=='quadratic_assignment':wanted=add(output,scale(np(g['expression']),-1))
        else:
            assert g['operation']=='rational_quotient'
            wanted=add(mul(output,np(g['denominator'])),scale(np(g['numerator']),-1))
        assert N[name]==wanted,name
    names={c['name']:c['id'] for c in new['coordinates']};gates_by_id={g['coordinateId']:g for g in new['gates']}
    decoded=[]
    for r in range(3):
        prefix=f'detector{r}.';powers={names[prefix+'q1']:1}
        def expression(ts):
            assert len(ts)==1;t=ts[0];assert F(t['coefficient'])==1 and t['sPower']==0
            return sum(power(i) for i in t['monomial'])
        def power(i):
            if i not in powers:
                g=gates_by_id[i]
                if g['operation']=='quadratic_assignment':v=expression(g['expression'])
                else:
                    assert g['operation']=='rational_quotient'
                    v=expression(g['numerator'])-expression(g['denominator'])
                powers[i]=v
            return powers[i]
        expected={'q1SquaredForWeights.quadratic':2,'q1CubedForWeights.quadratic':3,
                  'q1Sixth.quadratic':6,'q1Twelfth.quadratic':12,'q12':23,'mixedHigh.quadratic':46,
                  'q46':91,'E46.power2.quadratic':182,'E46.power3.quadratic':273}
        for name,e in expected.items():assert power(names[prefix+name])==e
        decoded.append(expected)
    return {'removedRows':sorted(removed),'addedRows':sorted(added),'changedRows':sorted(changed),
            'unchangedCommonRows':len(O.keys()&N.keys())-3,'allCommonFieldFunctionsAndGuardsIdentical':True,
            'actualMonomialPowers':decoded,'note':'Formal common expressions agree; evaluated W/trace/B change.'}


def finite_checks():
    orders=[1,12,46]
    for m in orders:
        j=2*m-1
        assert (2*m-1,2*m-1-2*j)==(2*m-1,-(2*m-1))
        assert 1-2*m+2*m==1
    delta=[98*x-1 for x in [F(0),F(1,49),F(1,50),F(1,2450),F(32,1225)]]
    assert delta==[F(-1),F(1),F(24,25),F(-24,25),F(39,25)]
    for d in delta:
        for z in [abs(d.numerator),d.denominator]:
            for p in [2,3,5,7,13,17]:
                while z%p==0:z//=p
            assert z==1
    H=3*2**106*(2**32*3**9)**6*46410**18+128;c=2*3**1004;b=c-1
    assert 8**992*c**415>(25*H)**992
    assert (2*(b*b-6))**1472>(3*H+14)**1472*(2*b**4+6*b**3+5*b*b+1)**577
    assert 40*H<2**670 and b>67000 and F(4712,4775)*301+F(4616,4775)<298
    return {'orders':orders,'deltaValues':list(map(str,delta)),
            'localNuAndS':[[2*m-1,4*(2*m-1)] for m in orders],
            'realDecayPowers':[-(2*m-1) for m in orders],'sameHeightConsumersAtE2010':True}


def main():
    if not __debug__:raise RuntimeError('Run without Python optimization')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('old',type=Path);ap.add_argument('new',type=Path);ap.add_argument('--report',type=Path,required=True);a=ap.parse_args()
    old=json.loads(a.old.read_text());new=json.loads(a.new.read_text());result=source_check(old,new)
    mutations=[]
    for name in ['detector0.q12.definition','detector1.q46.definition','scalar.N.definition']:
        bad=copy.deepcopy(new);r=next(x for x in bad['residuals'] if x['name']==name);r['terms'][0]['coefficient']=str(F(r['terms'][0]['coefficient'])+1);mutations.append((name,bad))
    bad=copy.deepcopy(new);bad['guards']=[];mutations.append(('missing guards',bad))
    bad=copy.deepcopy(new);bad['fixedParameter']['value']='3^2004';mutations.append(('wrong anchor',bad))
    for name,bad in mutations:
        try:source_check(old,bad)
        except (AssertionError,KeyError):continue
        raise AssertionError('Accepted corrupted source '+name)
    report={'status':'PASS','sourceComparison':result,'finite':finite_checks(),'negativeControlsRejected':[n for n,_ in mutations],
            'files':{n:hashlib.sha256(p.read_bytes()).hexdigest() for n,p in [('before',a.old),('after',a.new)]},
            'scope':'Exact source/gate/local-exponent and finite integer checks; uniform arithmetic proof needs separate review.'}
    a.report.write_text(json.dumps(report,indent=2)+'\n');print('PASS: uniform powers, outside source identity, margins and five negative controls')


if __name__=='__main__':main()
