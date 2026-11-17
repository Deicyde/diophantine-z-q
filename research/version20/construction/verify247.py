"""Independent finite verification of Carbon's 247 package; reads data only."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import reduce
from math import gcd
from pathlib import Path
import hashlib
import json
import sys

sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
(HERE.parents[2]/'build/version20').mkdir(parents=True,exist_ok=True)
PACKAGE=HERE/'inputs/carbon'
def read(path): return json.loads((PACKAGE/path).read_bytes())
def clean(p): return {k:v for k,v in p.items() if v}
def polynomial(row):
    p=defaultdict(F)
    for t in row['terms']:
        p[(t.get('parameterPower',0),tuple(sorted(t['monomial'])))]+=F(t['coefficient'])
    return clean(p)
def add_scaled(dst,src,scale):
    for k,v in src.items(): dst[k]+=scale*v
def row_multiple(expected,actual):
    assert expected and actual and expected.keys()==actual.keys()
    key=next(iter(expected))
    ratio=actual[key]/expected[key]
    assert ratio and all(actual[k]==ratio*v for k,v in expected.items())
    return ratio

certificate=read('certificates/v20-normalization244-certificate.json')
source_path=PACKAGE/certificate['source']
assert hashlib.sha256(source_path.read_bytes()).hexdigest()==certificate['source_sha256']
published=HERE.parents[1]/'version19/construction/inputs/carbon/family244/unbalanced244-quadratic.json'
assert source_path.read_bytes()==published.read_bytes(), 'Source must be the released 244 table'
q=read(certificate['source'])
norm=read(certificate['normalized244_target'])
explicit=read('tables/explicit247/explicit247-quadratic.json')
assert len(q['residuals'])==len(norm['residuals'])==216
assert len(explicit['residuals'])==219
scale={int(k):F(v) for k,v in certificate['coord_scales'].items()}
assert all(1<=i<=244 and v for i,v in scale.items()) and scale.get(1,1)==1
T=[{int(k)-1:F(v) for k,v in row.items()} for row in certificate['T_rows']]
Ti=[{int(k)-1:F(v) for k,v in row.items()} for row in certificate['T_inv_rows']]
assert len(T)==len(Ti)==216
for matrix in [T,Ti]:
    assert all(0<=j<216 for row in matrix for j in row)
for a,b in [(T,Ti),(Ti,T)]:
    for i,row in enumerate(a):
        out=defaultdict(F)
        for j,c in row.items(): add_scaled(out,b[j],c)
        assert clean(out)=={i:F(1)}, ('matrix inverse',i)

scaled=[]
for row in q['residuals']:
    p=polynomial(row)
    scaled.append({k:v*reduce(lambda x,i:x*scale.get(i,1), k[1],F(1)) for k,v in p.items()})
for i,row in enumerate(T):
    out=defaultdict(F)
    for j,c in row.items(): add_scaled(out,scaled[j],c)
    assert clean(out)==polynomial(norm['residuals'][i]), ('normalization',i+1)

perm={int(k):int(v) for k,v in certificate['permutation_247']['old_to_new'].items()}
invperm={int(k):int(v) for k,v in certificate['permutation_247']['new_to_old'].items()}
assert set(perm)==set(perm.values())==set(range(1,248))
assert all(invperm[v]==k for k,v in perm.items())
assert all(perm[i]==i for i in [1,245,246,247])
assert all(c['unpermuted247Id']==invperm[c['id']] for c in explicit['coordinates'])
ratios=[]
for i,row in enumerate(norm['residuals']):
    out=defaultdict(F)
    for (power,mon),c in polynomial(row).items():
        assert power in [0,1]
        assert not power or i==60
        shifted=mon+(247,)*power
        out[(0,tuple(sorted(perm[v] for v in shifted)))]+=c
    ratios.append(str(row_multiple(clean(out),polynomial(explicit['residuals'][i]))))
for i,expected in enumerate([
    {(0,()):F(149**5110),(0,(245,)):F(-1)},
    {(0,(245,245)):F(1),(0,(246,)):F(-1)},
    {(0,(246,246)):F(149),(0,(247,)):F(-1)}],216):
    row_multiple(expected,polynomial(explicit['residuals'][i]))
assert 2*(2*5110)+1==20441==2*10220+1

expansion=defaultdict(int)
for i,row in enumerate(explicit['residuals'],1):
    p=polynomial(row)
    assert row['id']==i
    assert all(power==0 and len(mon)<=2 and c.denominator==1 for (power,mon),c in p.items())
    assert reduce(gcd,(abs(int(c)) for c in p.values()))==1
    for (_,a),ca in p.items():
        for (_,b),cb in p.items(): expansion[tuple(sorted(a+b))]+=int(ca*cb)
expansion=clean(expansion)
decimal=read('tables/explicit247/quartic247-decimal.json')
assert decimal['variables']==247
assert all(t.get('parameterPower',0)==0 for t in decimal['terms'])
assert expansion=={tuple(t['monomial']):int(t['coefficient']) for t in decimal['terms']}
assert len(expansion)==3385 and max(map(len,expansion))==4
assert expansion[(1,1,1,1)]==1 and reduce(gcd,expansion.values())==1
assert {v for mon in expansion for v in mon}==set(range(1,248))
height=max(abs(c) for c in expansion.values())
assert height==expansion[()] and height.bit_length()==73780
height_remainder=height-149**10220
assert height_remainder==298442980098761875927809873

# Implement the printed PR145 convention without importing Carbon's renderer.
pieces=[]
for mon,c in sorted(expansion.items()):
    factors=[f'x{i}' if n==1 else f'x{i}^{n}' for i,n in sorted(Counter(mon).items())]
    if not factors or abs(c)!=1: factors.insert(0,str(abs(c)))
    pieces.append(('-' if c<0 else ('+' if pieces else ''))+'*'.join(factors))
plain=''.join(pieces).encode('ascii')
assert plain==(PACKAGE/'tables/explicit247/quartic247-decimal.txt').read_bytes()
assert len(plain)==96712 and hashlib.sha256(plain).hexdigest()=='455afb0b7143654119db3a68a85fec2fde566cf7fbdf3f7c84bd5d75b32719b9'
report={'source_sha256':certificate['source_sha256'],'matches_released_v19_source':True,
        'coordinate_scalings':len(scale),'input_fixed':True,'two_sided_matrix_inverse':True,
        'normalization_identities':216,'primitive_row_multipliers':ratios,
        'ladder':[5110,10220,20441],'occurring_variables':247,'monomials':len(expansion),
        'degree':4,'content':1,'input_fourth_coefficient':1,'coefficient_bits':height.bit_length(),
        'coefficient_decimal_digits':len(str(height)),'height':f'149^10220 + {height_remainder}',
        'plain_bytes':len(plain),'plain_sha256':hashlib.sha256(plain).hexdigest(),
        'scope':'Finite transformations and expansion only; arithmetic comes from the retained manuscript. No optimality claim.'}
(HERE.parents[2]/'build/version20/247-verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='primitive_row_multipliers'},indent=2))
