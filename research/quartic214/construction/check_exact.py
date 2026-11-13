#!/usr/bin/env python3
"""Exact Laurent identities and full SOS replay; no arithmetic acceptance."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter,defaultdict
from math import gcd
from functools import reduce
import json
P=Path(__file__).resolve().parent
def add(*ps):
    out=defaultdict(F)
    for p in ps:
        for m,c in p.items():out[m]+=c
    return {m:c for m,c in out.items() if c}
def mul(a,b):
    out=defaultdict(F)
    for m,c in a.items():
        for n,d in b.items():
            powers=defaultdict(int,m)
            for v,e in n:powers[v]+=e
            out[tuple(sorted((v,e) for v,e in powers.items() if e))]+=c*d
    return {m:c for m,c in out.items() if c}
def scale(p,c):return {m:v*c for m,v in p.items() if v*c}
ONE={():F(1)}
def V(i,e=1):return {((i,e),):F(1)} if e else ONE
def raw(terms,remap=None):
    out={}
    for term in terms:
        count=Counter(remap[i] if remap else i for i in term['monomial'])
        if term['parameterPower']:count[0]=term['parameterPower']
        out[tuple(sorted(count.items()))]=F(term['coefficient'])
    return out
def substitute(poly,maps):
    total={}
    for mon,c in poly.items():
        term=scale(ONE,c)
        for v,e in mon:
            assert e>=0
            for _ in range(e):term=mul(term,maps.get(v,V(v)))
        total=add(total,term)
    return total
def proportional(a,b):
    assert a and set(a)==set(b)
    m=next(iter(a));c=a[m]/b[m]
    assert c and a==scale(b,c)
    return c
parent=json.loads((P.parents[2]/'research/version15/quartics/quartic-222/provenance/shared-T-redundancy224-006/candidate224-ir.json').read_text())
pr={r['id']:r for r in parent['residuals']}
names={c['name']:c['id'] for c in parent['coordinates']}
removed={c['id'] for c in parent['coordinates'] if '.wPower2.' in c['name'] or c['name'].startswith('residue.V1.power4')}
defs={};defrows=set()
for r in parent['residuals']:
    p=raw(r['terms'])
    hits=[v for v in removed if ((v,1),) in p]
    if len(hits)==1 and r['name'].endswith('.definition') and ('wPower2' in r['name'] or 'V1.power4' in r['name']):
        v=hits[0];c=p[((v,1),)]
        defs[v]=scale(add(p,scale(V(v),-c)),-1/c);defrows.add(r['id'])
assert len(defs)==len(defrows)==10

reports=[]
for mode,n in [('brox',214)]:
    folder=P/'artifacts'/f'candidate{n}-{mode}'
    ir=json.loads((folder/f'candidate{n}-ir.json').read_text())
    # Expanded IDs map to unique original IDs; additional slots stay distinct.
    mapping={c['id']:(c['parent224Id'] if c['parent224Id'] is not None else 1000+c['id']) for c in ir['coordinates']}
    candidate_names={c['name']:mapping[c['id']] for c in ir['coordinates']}
    old_maps=dict(defs);new_maps={};weight_rows=set();qids=[]
    for j in (0,1):
        q=names[f'detector{j}.q1'];qids.append(q)
        h=names[f'reflected.detector{j}.weightPower7']
        a=names[f'detector{j}.E1.power2.quadratic'];b=names[f'detector{j}.E1.power4.quadratic']
        old_maps.update({h:V(q,5 if mode=='brox' else 7),a:V(q,2),b:V(q,4)})
        new_maps.update({h:V(q,-1),a:V(q,-2),b:V(q,-4)})
        if mode=='equiv':
            new_maps[candidate_names[f'detector{j}.weightCubed']]=V(q,3)
            new_maps[candidate_names[f'detector{j}.inverseWeightCubed']]=V(q,-3)
        for r in parent['residuals']:
            if r['name'] in (f'detector{j}.E1.power2.definition',f'detector{j}.E1.power4.definition',f'reflected.detector{j}.weightPower7.definition'):
                weight_rows.add(r['id'])
    assert len(weight_rows)==6
    identities=[];unchanged=0
    for r in ir['residuals']:
        actual=raw(r['terms'],mapping);rid=r.get('parent224RowId')
        if rid in weight_rows or rid is None:
            assert not substitute(actual,new_maps),r['name']
            continue
        original=raw(pr[rid]['terms'])
        if r['name'].startswith('residue.det'):
            j=int(r['name'].split('residue.det')[1][0]);q=qids[j]
            # q itself is changed only in factor2's special coefficient.
            if mode=='brox':
                special={}
                for mon,c in original.items():
                    if any(v==q for v,e in mon):
                        assert dict(mon)[q]==1
                        mon=tuple(sorted((v,3 if v==q else e) for v,e in mon))
                    special[mon]=c
                original=special
            before=substitute(original,old_maps)
            after=mul(V(q,4),substitute(actual,new_maps))
            c=proportional(before,after)
            identities.append({'parentRow':rid,'newRow':r['id'],'multiplier':str(c),'weight':q,'power':4})
        else:
            proportional(original,actual);unchanged+=1
    assert len(identities)==20 and unchanged==162
    polynomial={}
    for r in ir['residuals']:
        rr=raw(r['terms']);polynomial=add(polynomial,mul(rr,rr))
    expected=raw(json.loads((folder/f'candidate{n}-polynomial.json').read_text())['terms'])
    assert polynomial==expected
    assert reduce(gcd,(abs(int(c)) for c in polynomial.values()))==1
    assert max(sum(e for v,e in m if v) for m in polynomial)==4
    assert {v for mon in polynomial for v,e in mon if v}==set(range(1,215))
    # Exact coefficient-height proof for every A>=149^107 (N>=53).
    profiles=defaultdict(dict)
    for mon,c in polynomial.items():
        a=dict(mon).get(0,0)
        coordinate_mon=tuple((v,e) for v,e in mon if v)
        profiles[coordinate_mon][a]=c
    assert all(set(profile)<={0,1,2} for profile in profiles.values())
    dominant=[profile for profile in profiles.values() if 2 in profile]
    assert dominant==[{0:F(1),2:F(1)}]
    A53=149**107
    for profile in profiles.values():
        if 2 not in profile:
            # After division by A^2 the left side decreases, and RHS>=1.
            assert abs(profile.get(0,0))+abs(profile.get(1,0))*A53<A53*A53
    assert any(abs(profile.get(0,0))>=149**210+1 for profile in profiles.values() if set(profile)=={0})
    # Corruption controls: each altered factor identity and a changed table term fails.
    failures=0
    for identity in identities:
        r=ir['residuals'][identity['newRow']-1]
        altered=add(raw(r['terms'],mapping),ONE)
        correct=raw(r['terms'],mapping)
        before=scale(mul(V(identity['weight'],4),substitute(correct,new_maps)),F(identity['multiplier']))
        try:
            proportional(before,mul(V(identity['weight'],4),substitute(altered,new_maps)))
        except AssertionError:
            failures+=1
        else:
            raise AssertionError('Corrupted factor transport accepted')
    try:
        assert add(expected,ONE)==polynomial
    except AssertionError:
        failures+=1
    else:
        raise AssertionError('Corrupted quartic table accepted')
    reports.append({'mode':mode,'variables':n,'rows':len(ir['residuals']),
                    'unchanged_rows':unchanged,'factor_identities':identities,
                    'full_sos':True,'all_variables_occur':True,'coefficient_height_N_at_least':53,'coefficient_height':'149^(4N+2)+1','deliberate_corruptions_rejected':failures,
                    'scope':'exact algebra only;214 changes factor exponents and requires arithmetic proof'})
(P/'EXACT-CHECKS.json').write_text(json.dumps(reports,indent=2)+'\n')
print(json.dumps([{k:v for k,v in r.items() if k!='factor_identities'} for r in reports]))
