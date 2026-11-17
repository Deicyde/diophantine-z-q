"""Independent exact verification of inert 214 -> 212 -> 247 -> 244 -> 250 data."""
from pathlib import Path
from collections import defaultdict
from fractions import Fraction as F
from functools import reduce
from math import gcd
import json, hashlib
R=Path(__file__).resolve().parent
OUT=R.parents[2]/'build/version19'
OUT.mkdir(parents=True, exist_ok=True)
def read(p): return json.loads((R/p).read_bytes())
def poly(row, mapping=None):
    out=defaultdict(F)
    for t in row['terms']:
        key=(t['parameterPower'],tuple(sorted(mapping.get(i,i) if mapping else i for i in t['monomial'])))
        out[key]+=F(t['coefficient'])
    return {k:v for k,v in out.items() if v}
q214=read('inputs/jose/computation/quartic/balanced214_v24/source/quadratic214.json')
q212=read('inputs/jose/computation/quartic/additive212_v25/unbalanced-quadratic.json')
q247=read('inputs/carbon/family244/family247-intermediate-quadratic.json')
q244=read('inputs/carbon/family244/unbalanced244-quadratic.json')
q250=read('inputs/carbon/explicit250/explicit250-quadratic.json')
cert=read('inputs/carbon/family244/laurent244-certificate.json')
mapping={x['parent214Id']:x['id'] for x in q212['coordinates']}
changed=[]
for row in q212['residuals']:
    old=q214['residuals'][row['parent214RowId']-1]
    if poly(old,mapping)!=poly(row):changed.append(old['id'])
assert changed==[22,24,25,35,36,37,38,182],changed
assert set(range(1,189))-{r['parent214RowId'] for r in q212['residuals']}=={64,65}
repurposed={4,76,77,78,90,91,92,93}
assert all(row['id'] in set(changed)|{23,64,65} or
           not (repurposed & {i for t in row['terms'] for i in t['monomial']})
           for row in q214['residuals'])
for a,b in zip(q212['residuals'],q247['residuals']): assert poly(a)==poly(b)
clone={x['clonedFrom212Id']:x['id'] for x in q247['coordinates'][212:]}
rows_by_name={x['name']:x for x in q212['residuals']}
for row in q247['residuals'][186:218]:
    name=row['name'].replace('detector2','detector1').replace('det2','det1')
    assert poly(rows_by_name[name],clone)==poly(row),row['name']

# Reconstruct the contact coefficients, rather than trusting their description.
theta=[F(0),F(-1,2),F(-1),F(1,2399),F(-32,407)]
es=[F(1)]+[F(0)]*5
for a in [(1-t)**2 for t in theta]:
    for k in range(5,0,-1):es[k]+=a*es[k-1]
scale=3813373161796
for offset,(t,r,s,v,w) in [(21,(4,76,77,78,80)),(34,(90,91,92,93,95)),(190,(217,218,219,220,222))]:
    # Locate by coordinate rather than assuming a cloned-row ordering.
    expected=[{(t,t):F(1),(t,):F(-2),():F(1),(r,):F(-1)},
              {(r,r):F(1),(s,):F(-1)},
              {(r,s):F(scale),(s,):-scale*es[1],tuple(sorted((s,w))):-scale*es[1],
               (r,):scale*es[2],tuple(sorted((r,w))):scale*es[2],(v,):F(-scale)},
              {(s,v):F(-scale),(s,):scale*es[3],tuple(sorted((s,w))):scale*es[3],
               (r,):-scale*es[4],tuple(sorted((r,w))):-scale*es[4],():scale*es[5],(w,):scale*es[5]}]
    for p in expected:
        want={(0,tuple(sorted(k))):value for k,value in p.items() if value}
        assert any(poly(row)==want for row in q247['residuals']),('contact',t,p)

# Every diagonal identity is checked in a Laurent ring on the literal guard chart.
deleted=set(cert['deleted_coordinates'])
renumber={old:i+1 for i,old in enumerate(i for i in range(1,248) if i not in deleted)}
powers={int(k):tuple(v) for k,v in cert['powers'].items()}
weights={int(k):tuple(v) for k,v in cert['weights'].items()}
constants={int(k):F(v) for k,v in cert['constants'].items()}
H=31581660**14; K=82479248*H
assert int(cert['constant_scale_H'])==H and int(cert['constant_scale_K'])==K
assert constants=={109:F(1,H),110:F(-1,K),13:F(-K),14:F(K),15:F(K),16:F(K),
                  111:F(K*K),113:F(K*K),112:F(-1)}
target_powers={renumber[k]:v for k,v in powers.items() if k not in deleted}
def laurent(row,source):
    out=defaultdict(F)
    for t in row['terms']:
        c=F(t['coefficient']); unit=[0,0,0]; mon=[]
        for i in t['monomial']:
            if source:
                if i in powers:
                    unit=[a+b for a,b in zip(unit,powers[i])]
                else:
                    c*=constants.get(i,1)
                    unit=[a+b for a,b in zip(unit,weights.get(i,(0,0,0)))]
                    mon.append(renumber[i])
            elif i in target_powers:
                unit=[a+b for a,b in zip(unit,target_powers[i])]
            else:mon.append(i)
        out[(t['parameterPower'],tuple(unit),tuple(sorted(mon)))]+=c
    return {k:v for k,v in out.items() if v}
for row in q247['residuals']:
    if row['name'] in cert['deleted_rows']:assert not laurent(row,True)
identities=[]
for rc in cert['row_certificates']:
    src=laurent(q247['residuals'][rc['source_row']-1],True)
    dst=laurent(q244['residuals'][rc['target_row']-1],False)
    shift=rc['division_exponents']; multiplier=F(rc['primitive_multiplier'])
    adjusted={(a,tuple(e-d for e,d in zip(u,shift)),m):v*multiplier for (a,u,m),v in src.items()}
    assert adjusted==dst,rc
    identities.append(rc['source_row'])
assert len(identities)==216
# Guard and square rows must be literal in the target, not merely zero after normalization.
for unit in [(79,80,81),(94,95,96),(221,222,223)]:
    q,w,w2=map(renumber.__getitem__,unit)
    guards=[{(0,()):F(1),(0,tuple(sorted((q,w)))):F(-1)},
            {(0,(w,w)):F(1),(0,(w2,)):F(-1)}]
    for g in guards:assert any(poly(row)==g or poly(row)=={k:-v for k,v in g.items()} for row in q244['residuals'])

for a,b in zip(q244['residuals'],q250['residuals'][:216]):
    expected={}
    for (power,mon),value in poly(a).items():
        assert power in [0,1]
        expected[(0,tuple(sorted(mon+(250,)*power)))]=value
    assert expected==poly(b),a['name']
ladder=[]
for k,rem in enumerate([449,379,1,0,0,1]):
    idx=245+k
    prev=() if k==0 else (idx-1,idx-1)
    want={(0,(idx,)):F(1),(0,prev):F(-149**rem)}
    got=poly(q250['residuals'][216+k])
    assert got==want or got=={a:-b for a,b in want.items()}
    ladder.append(rem if k==0 else 2*ladder[-1]+rem)
assert ladder==[449,1277,2555,5110,10220,20441]
expanded=defaultdict(int)
for row in q250['residuals']:
    p=poly(row)
    assert all(a==0 and len(m)<=2 and c.denominator==1 for (a,m),c in p.items())
    for (_,ma),ca in p.items():
        for (_,mb),cb in p.items(): expanded[tuple(sorted(ma+mb))]+=int(ca*cb)
expanded={m:c for m,c in expanded.items() if c}
published=read('coefficients/quartic250-decimal.json')
assert expanded=={tuple(t['monomial']):int(t['coefficient']) for t in published['terms']}
height=149**898+1747145497790223592810060471184416344603224790540808983
assert len(expanded)==3362 and max(abs(c) for c in expanded.values())==height<2**6483
assert expanded[()]==height and expanded[(1,1,1,1)]==1
assert reduce(gcd,expanded.values())==1 and max(map(len,expanded))==4
assert {i for m in expanded for i in m}==set(range(1,251))
assert (9*(2*10220-1))//4+1==45988
assert 149**45988>=2**331995
assert 2**118*15**6>22**3*(345+7*331970)**6
assert 149**7>22202*2**20
report={'214_to_212':{'unchanged_rows':178,'changed_old_rows':changed,'deleted_old_rows':[64,65]},
        '212_to_247':{'unchanged_rows':186,'literal_cloned_rows':32},
        '247_to_244':{'laurent_identities':216,'deleted_identity_rows':3,'all_six_guards_checked':True},
        '244_to_250':{'unchanged_or_parameter_substituted_rows':216,'ladder':ladder},
        'expansion':{'terms':3362,'degree':4,'content':1,'all250_coordinates_used':True,
                     'height':'149^898 + 1747145497790223592810060471184416344603224790540808983',
                     'bits':height.bit_length(),'decimal_digits':len(str(height))},
        'threshold_integer_checks':True,'upstream_code_executed':False,
        'scope':'Finite identities only. The manuscript supplies the arithmetic and existential proofs.'}
(OUT/'250-verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
