"""Separate finite replay implementation, authored in the same review session.

Not an independent reviewer acceptance. Derives the semantic conic from its
actual residual, instead of trusting the producer's value metadata.
"""
from pathlib import Path
from fractions import Fraction
from itertools import product
import argparse
import hashlib
import json

def decode(ts):
    out={}
    for t in ts:
        k=tuple(sorted(t['monomial']+[-1]*t['sPower']))
        assert k not in out
        out[k]=Fraction(t['coefficient'])
    return out

def plus(a,b):
    return {k:a.get(k,0)+b.get(k,0) for k in a.keys()|b.keys() if a.get(k,0)+b.get(k,0)}

def times(a,b):
    result={}
    for (x,c),(y,d) in product(a.items(),b.items()):
        k=tuple(sorted(x+y));result[k]=result.get(k,0)+c*d
    return {k:c for k,c in result.items() if c}

def constant(x): return {():Fraction(x)}
def V(i): return {(i,):Fraction(1)}
def scaled(a,k): return times(a,constant(k))

def replace(p,mapping):
    result={}
    for m,c in p.items():
        term=constant(c)
        for i in m: term=times(term,mapping.get(i,V(i)))
        result=plus(result,term)
    return result

def proportional(a,b):
    assert a and b and set(a)==set(b)
    first=next(iter(a)); ratio=a[first]/b[first]
    assert ratio and all(a[m]==ratio*b[m] for m in a)
    return str(ratio)

def verify(source,candidate):
    old={r['name']:r for r in source['residuals']}; new={r['name']:r for r in candidate['residuals']}
    assert len(old)==len(source['residuals']) and len(new)==len(candidate['residuals'])
    mapping_names={c['name']:c['id'] for c in source['coordinates']}
    touched=set(); removed=set(); checks=[]
    for prefix in ['detector0','detector1','detector2','scalar']:
        s,q,h,s2,q2=[mapping_names[prefix+x] for x in ['.s','.q','.Bh.quadratic','.s2.quadratic','.q2.quadratic']]
        second=decode(old[prefix+'.secondConic']['terms'])
        # Decode H and 17*b directly from coefficients of the old conic.
        H={}; b={}
        for monomial,coefficient in second.items():
            m=list(monomial)
            if s2 in m and m.count(s2)==1:
                m.remove(s2); H[tuple(m)]=-coefficient/2
            if q2 in m:
                assert m.count(q2)==1
                m.remove(q2); b[tuple(m)]=coefficient/17
        assert second.get((s2,s2))==-1
        expected=plus(plus(scaled(times(b,V(q2)),17),scaled(times(H,H),3)),
                      plus(scaled(times(V(s2),H),-2),scaled(times(V(s2),V(s2)),-1)))
        assert expected==second
        alpha=H[(h,)];rest=plus(H,scaled(V(h),-alpha))
        mapping={h:scaled(plus(times(V(s),V(h)),scaled(rest,-1)),1/alpha),
                 q:times(V(s),V(q)),q2:times(times(V(s),V(s)),V(q2)),s2:times(V(s),V(s))}
        prefixes={prefix+x for x in ['.Bh.definition','.q2.definition','.s2.definition','.secondConic']}
        consumers={r['name'] for r in source['residuals'] if any(set(t['monomial'])&{h,q,q2,s2} for t in r['terms'])}
        assert consumers==prefixes
        assert prefix+'.s2.definition' not in new
        assert replace(decode(old[prefix+'.s2.definition']['terms']),mapping)=={}
        ratios={}
        for ending in ['.Bh.definition','.q2.definition','.secondConic']:
            name=prefix+ending
            target=decode(new[name]['terms'])
            lifted=replace(decode(old[name]['terms']),mapping)
            if ending!='.Bh.definition':target=times(times(V(s),V(s)),target)
            ratios[name]=proportional(lifted,target)
        # Forward nonzero-s map: substitute v=H/s, Q=q/s, Q2=q2/s^2
        # is inverse to mapping for s!=0. The s=0 case is justified by
        # 17*b*q^2+3*H^2=0 and b>0, not by cancellation of s^2.
        expected_zero=plus(scaled(times(b,times(V(q),V(q))),17),scaled(times(H,H),3))
        old_zero=replace(second,{s2:{},q2:times(V(q),V(q))})
        assert old_zero==expected_zero
        touched |= prefixes;removed.add(s2)
        checks.append({'prefix':prefix,'exactLiftRowFactors':ratios,'incidenceChecked':True,
                       'zeroBranchReducedToPositiveSum':True})
    assert set(old)-set(new)=={p+'.s2.definition' for p in ['detector0','detector1','detector2','scalar']}
    assert all(new[name]==row for name,row in old.items() if name not in touched)
    oldcoords={c['id']:c for c in source['coordinates']};newcoords={c['id']:c for c in candidate['coordinates']}
    assert len(oldcoords)==len(source['coordinates']) and len(newcoords)==len(candidate['coordinates'])
    assert set(newcoords)==set(oldcoords)-removed
    repurposed={mapping_names[p+'.Bh.quadratic'] for p in ['detector0','detector1','detector2','scalar']}
    for i,c in newcoords.items():
        expected=dict(oldcoords[i])
        if i in repurposed: expected['name']=expected['name'].replace('.Bh.quadratic','.factored_v')
        assert c==expected
    assert newcoords[0]==oldcoords[0] and oldcoords[0]['name']=='input'
    assert candidate['fixedParameter']==source['fixedParameter']
    assert len(newcoords)==385 and len(new)==353
    for row in new.values():
        for t in row['terms']:
            assert len(t['monomial'])<=2 and set(t['monomial'])<=set(newcoords)
    return checks

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('construction', type=Path)
    args = parser.parse_args()
    root = args.construction.resolve()
    cert=json.loads((root/'transport-certificate.json').read_text())
    sourcepath=root/cert['source'];candidatepath=root/'final/integer-candidate-ir.json'
    assert hashlib.sha256(sourcepath.read_bytes()).hexdigest()==cert['sourceSha256']
    assert hashlib.sha256(candidatepath.read_bytes()).hexdigest()==cert['candidateSha256']
    source=json.loads(sourcepath.read_text());candidate=json.loads(candidatepath.read_text())
    checks=verify(source,candidate)
    probes=[]
    for mutation in ['change_conic_coefficient','add_outside_consumer','restore_deleted_square']:
        a=json.loads(json.dumps(source));b=json.loads(json.dumps(candidate))
        if mutation=='change_conic_coefficient':
            r=next(r for r in b['residuals'] if r['name']=='scalar.secondConic');r['terms'][0]['coefficient']=str(Fraction(r['terms'][0]['coefficient'])+1)
        elif mutation=='add_outside_consumer':
            a['residuals'][0]['terms'].append({'sPower':0,'monomial':[279],'coefficient':'1'})
        else:
            b['coordinates'].append(next(c for c in a['coordinates'] if c['id']==280))
        try: verify(a,b)
        except AssertionError: probes.append(mutation)
        else: raise AssertionError('negative control accepted: '+mutation)
    report={'status':'PASS','scope':'Exact conic reconstruction, source-to-candidate lift identities, full consumer incidence, unchanged exterior rows. Arithmetic hypotheses and independent acceptance remain separate.',
            'coordinates':385,'residuals':353,'sourceSha256':cert['sourceSha256'],'candidateSha256':cert['candidateSha256'],'blocks':checks,'rejectedNegativeControls':probes,
            'independentAcceptance':False}
    (root/'transport-check.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__': main()
