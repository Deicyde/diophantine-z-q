"""Independent exact check; reads inert data and printed TeX, no producer imports."""
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict, Counter
from hashlib import sha256
from math import comb, gcd
import json
import re

HERE = Path(__file__).resolve().parent
BASE = HERE
REPO = HERE.parents[2]
OUT = REPO / 'build/version19'
OUT.mkdir(parents=True, exist_ok=True)
SRC = HERE / 'inputs/jose/computation/quartic'
MS = REPO / 'manuscripts/quartic_v19.tex'
SHA = sha256(MS.read_bytes()).hexdigest()
assert sha256(MS.read_bytes()).hexdigest() == SHA
tex = MS.read_text(encoding='utf-8')
inputs = {}
download_manifest_path = HERE / 'inputs/jose/download-manifest.json'
download_manifest = json.loads(download_manifest_path.read_bytes())
assert download_manifest['commit'] == 'cd474ee67104586c9d71885a7c95e8a21f12ca0c'
pinned = {r['path']:r['sha256'] for r in download_manifest['files']}

def read(rel):
    p = SRC / rel
    b = p.read_bytes()
    inputs[p.relative_to(REPO).as_posix()] = dict(bytes=len(b), sha256=sha256(b).hexdigest())
    assert inputs[p.relative_to(REPO).as_posix()]['sha256'] == pinned['computation/quartic/'+rel]
    return json.loads(b)

def clean(p):
    return {k: Q(v) for k, v in p.items() if v}

def mon(c=1, power=0, variables=()):
    return {(power, tuple(sorted((i, e) for i, e in variables if e))): Q(c)} if c else {}

def add(*ps):
    d = defaultdict(Q)
    for p in ps:
        for k, v in p.items(): d[k] += v
    return clean(d)

def mul(a, b):
    d = defaultdict(Q)
    for (p, m), c in a.items():
        for (q, n), e in b.items():
            v = Counter(dict(m)); v.update(dict(n))
            d[p+q, tuple(sorted((i, x) for i, x in v.items() if x))] += c*e
    return clean(d)

def power(p, n):
    if n < 0:
        assert len(p) == 1
        (c, m), v = next(iter(p.items()))
        return mon(v**n, c*n, [(i, e*n) for i, e in m])
    result = mon()
    for _ in range(n): result = mul(result, p)
    return result

def sub(p, replacements):
    out = {}
    for (c, m), a in p.items():
        piece = mon(a, c)
        for i, e in m:
            piece = mul(piece, power(replacements.get(i, mon(variables=[(i, 1)])), e))
        out = add(out, piece)
    return out

def jp(terms):
    return add(*(mon(Q(t['coefficient']), t.get('parameterPower', 0),
                      Counter(t['monomial']).items()) for t in terms))

def rows(obj):
    return {r['name']: jp(r['terms']) for r in obj['residuals']}

def assert_same(a, b, title):
    if a != b:
        delta = add(a, mul(mon(-1), b))
        raise AssertionError((title, list(delta.items())[:6]))

def parse_printed_polynomial(s):
    s = re.sub(r'\\tag\{[^}]*\}', '', s)
    s = s.replace('\\\\', '').replace('&{}', '').replace('&', '')
    s = re.sub(r'\s+', '', s)
    out = {}
    for term in re.findall(r'[+-]?[^+-]+', s):
        sign = -1 if term.startswith('-') else 1
        body = term.lstrip('+-')
        p = mon(sign)
        pos = 0
        token = re.compile(r'(x_\{(\d+)\}|C|\d+)(?:\^\{(\d+)\})?')
        while pos < len(body):
            match = token.match(body, pos)
            assert match, (body, pos)
            atom, index, exponent = match.groups(); exponent = int(exponent or 1)
            if index: factor = mon(variables=[(int(index), exponent)])
            elif atom == 'C': factor = mon(power=exponent)
            else: factor = mon(int(atom)**exponent)
            p = mul(p, factor); pos = match.end()
        out = add(out, p)
    return out

printed = {}
for match in re.finditer(r'\\begin\{align\*\}(.*?)\\end\{align\*\}', tex, re.S):
    content = match.group(1)
    found = re.match(r'\s*q\^\{\[195\]\}_\{(\d+)\}&=(.*)', content, re.S)
    if found:
        printed[int(found.group(1))] = parse_printed_polynomial(found.group(2))
assert sorted(printed) == list(range(1, 176))
final = read('affine_laurent195_v45/quadratic-family.json')
for r in final['residuals']:
    assert_same(printed[r['id']], jp(r['terms']), ('printed row', r['id']))

# Extract the displayed matrix, independently of the JSON matrix.
matrix = [[Q(0) for _ in range(8)] for _ in range(8)]
matrix_text = tex.split('\\label{v19:195-maps}', 1)[1].split('\\endgroup', 1)[0]
for index, expr in re.findall(r's_\{(\d+)\}&=(.*?)\\end\{align\*\}', matrix_text, re.S):
    expr = re.sub(r'\s+', '', expr.replace('\\\\', '').replace('&{}', ''))
    terms = re.findall(r'([+-]?)(\\frac\{\d+\}\{\d+\}|\d+)r_\{(\d+)\}', expr)
    assert ''.join(a+b+'r_{'+c+'}' for a,b,c in terms) == expr
    for sign, coefficient, col in terms:
        frac = re.fullmatch(r'\\frac\{(\d+)\}\{(\d+)\}', coefficient)
        value = Q(*map(int, frac.groups())) if frac else Q(coefficient)
        matrix[int(index)-1][int(col)-1] += -value if sign == '-' else value
transform = read('primitive_basis196_v40/transform.json')
assert matrix == [[Q(x) for x in r] for r in transform['matrix']]

def determinant(a):
    a = [r[:] for r in a]; det = Q(1)
    for j in range(len(a)):
        pivot = next(i for i in range(j, len(a)) if a[i][j])
        if pivot != j: a[j], a[pivot] = a[pivot], a[j]; det = -det
        p = a[j][j]; det *= p
        for i in range(j+1, len(a)):
            q = a[i][j]/p
            for k in range(j+1, len(a)): a[i][k] -= q*a[j][k]
            a[i][j] = 0
    return det

det = determinant(matrix)
assert det == Q(1, 214450708242592116705963714180667354532074632082)

def parse_weight_table(begin, end):
    text = tex[tex.index(begin):tex.index(end, tex.index(begin))]
    d = {}
    for value, indices in re.findall(r'^(-?\d+) & \$([\d, ]+)\$', text, re.M):
        for i in indices.split(','):
            i = int(i); assert i not in d; d[i] = int(value)
    return d

weights = parse_weight_table('$a_i$ & Old indices', '\\end{longtable}')
scales = parse_weight_table('$k_j$ & New indices', '\\end{longtable}')
cert = read('affine_laurent195_v45/transformation.json')
assert weights == {int(k): v[0] for k,v in cert['laurent']['weights'].items()}
assert scales == {int(k):v for k,v in cert['parameter_scaling']['weights'].items()}
assert weights.get(1, 0) == scales.get(1, 0) == 0
assert weights.get(78, 0) == scales.get(78, 0) == 0
assert cert['laurent']['old_to_new'] == {str(i):i if i<79 else i-1 for i in range(1,197) if i !=79}
assert transform['coordinate_scaling'] == {'76':'1/3813373161796', '90':'1/3813373161796'}

# Verify the inert first-balancing data used before the displayed matrix.
unbalanced = read('laurent_recovery_v38/family196/quadratic.json')
balanced = read('laurent_recovery_v38/family196/balanced-quadratic.json')
balance = read('laurent_recovery_v38/family196/balancing.json')
assert inputs[(SRC/'laurent_recovery_v38/family196/quadratic.json').relative_to(REPO).as_posix()]['sha256'] == '3b6ab20da25bced159559c35e512e2bb2e56959b734b4265c8f80a7bd9cdb1c1'
balance_rows = {r['id']:r for r in balance['rows']}
balance_weights = {int(k):v for k,v in balance['weights'].items()}
assert balance_weights[1] == 0
for raw, target in zip(unbalanced['residuals'], balanced['residuals']):
    terms = []
    for t in raw['terms']:
        c = t.get('parameterPower', 0)
        terms.append(mon(Q(t['coefficient'])*149**c, 2*c+sum(balance_weights[i] for i in t['monomial']), Counter(t['monomial']).items()))
    rec = balance_rows[raw['id']]
    got = mul(add(*terms), mon(Q(rec['primitive_multiplier']), -rec['division_power']))
    assert_same(got, jp(target['terms']), ('balance',raw['id']))

paired = read('paired_redundancy196_v40/balanced-quadratic.json')
drop = {f'pair{i}.curve.{j}' for i in (1,3,4) for j in (0,1)}
assert rows(paired) == {k:v for k,v in rows(balanced).items() if k not in drop}
assert len(paired['residuals']) == 176
assert inputs[(SRC/'paired_redundancy196_v40/balanced-quadratic.json').relative_to(REPO).as_posix()]['sha256'] == transform['source_sha256']

# Bind the printed redundant-equation proof to the actual unbalanced blocks.
def fadd(*xs): return (add(*(x[0] for x in xs)), add(*(x[1] for x in xs)))
def fmul(a,b):
    return (add(mul(a[0],b[0]),mul(mon(2),mul(a[1],b[1]))),
            add(mul(a[0],b[1]),mul(a[1],b[0])))
def fscale(a,c): return (mul(mon(c),a[0]),mul(mon(c),a[1]))
def fv(i,j,second_scale=1): return (mon(variables=[(i,1)]),mon(second_scale,variables=[(j,1)]))
def proportional(a,b):
    assert a and set(a) == set(b)
    ratio = next(iter(a.values())) / b[next(iter(a))]
    assert ratio and a == mul(mon(ratio),b)
    return str(ratio)

raw_rows = rows(unbalanced)
one = (mon(),{})
D = (mon(11),mon(-6))
S,T = fv(17,18),fv(151,152)
physical_pairs = []
for number,start,Fi,Gi,Li,Mi,scale,label_shift in (
        (1,153,52,21,29,31,1,0), (3,163,56,25,37,39,2,0),
        (4,173,58,27,41,43,4,-1)):
    f,h,g,k,s = [fv(i,i+1) for i in range(start,start+10,2)]
    F,G = fv(Fi,Fi+1,2),fv(Gi,Gi+1,2)
    L,M = fadd(fv(Li,Li+1),(mon(label_shift),{})),fadd(fv(Mi,Mi+1),(mon(label_shift),{}))
    equations = {
      'square.f':fadd(F,fscale(fmul(f,f),-1)),
      'square.g':fadd(G,fscale(fmul(g,g),-1)),
      'secant':fadd(fmul(s,fadd(f,fscale(g,-1))),fscale(h,-1),fscale(k,-1)),
      'tangent':fadd(one,fscale(fmul(D,fadd(F,fmul(f,g),G)),-1),fscale(fmul(s,fadd(h,fscale(k,-1))),-1)),
      'ratio.primary.raw':fadd(fmul(h,L),fscale(fmul(f,S),scale)),
      'ratio.primary.regular':fadd(fmul(fadd(one,fscale(fmul(D,F),-1)),L),fscale(fmul(h,S),scale)),
      'ratio.alternate.raw':fadd(fmul(k,M),fscale(fmul(g,T),scale)),
      'ratio.alternate.regular':fadd(fmul(fadd(one,fscale(fmul(D,G),-1)),M),fscale(fmul(k,T),scale)),
      'curve':fadd(fmul(h,h),fscale(f,-1),fmul(D,fmul(F,f)))}
    for name,equation in equations.items():
        for component in (0,1):
            row_name = f'pair{number}.{name}.{component}'
            ratio = proportional(raw_rows[row_name],equation[component])
            physical_pairs.append(dict(row=row_name,multiplier=ratio))

# The exceptional S=T=0 branch: solve two retained linear rows exactly.
zero_ST = {i:{} for i in (17,18,151,152)}
linear = [sub(raw_rows[f'sharedT.reference.relation1.{j}'],zero_ST) for j in (0,1)]
a,b,c = [linear[0].get(key,Q(0)) for key in ((0,((15,1),)),(0,((16,1),)),(0,()))]
d,e,f = [linear[1].get(key,Q(0)) for key in ((0,((15,1),)),(0,((16,1),)),(0,()))]
linear_det = a*e-b*d
assert linear_det
x15,x16 = (b*f-c*e)/linear_det,(c*d-a*f)/linear_det
assert (x15,x16) == (Q(-15248,14161),Q(-79808,127449))
exception = dict(zero_ST)
exception.update({15:mon(x15),16:mon(x16),64:mon(x15*x15+2*x16*x16),65:mon(x15*x16)})
assert all(not sub(p,exception) for p in linear)
exceptional_residuals = [sub(raw_rows[f'sharedT.reference.relation3.{j}'],exception) for j in (0,1)]
assert exceptional_residuals == [mon(Q(1399113877520,928557)),mon(Q(866355785474,928557))]

primitive = read('primitive_basis196_v40/quadratic.json')
normalizations = read('primitive_basis196_v40/normalizations.json')
old_rows = rows(paired); selected = [old_rows[n] for n in transform['row_names']]
changed = dict(old_rows)
for i, name in enumerate(transform['row_names']):
    changed[name] = add(*(mul(mon(c), r) for c,r in zip(matrix[i],selected)))
coordinate_map = {i:mon(Q(1,3813373161796),variables=[(i,1)]) for i in (76,90)}
for r, factor in zip(primitive['residuals'], normalizations):
    got = mul(sub(changed[r['name']], coordinate_map), mon(Q(factor)))
    assert_same(got, jp(r['terms']), ('primitive basis',r['id']))
assert inputs[(SRC/'primitive_basis196_v40/quadratic.json').relative_to(REPO).as_posix()]['sha256'] == cert['source_sha256']

# Reconstruct from the printed affine formulas and the parsed weight lists.
affine = {50:add(mon(power=-1),mon(variables=[(50,1)])),
          72:add(mon(power=-1),mon(2,variables=[(50,1)]),mon(variables=[(72,1)])),
          73:add(mon(variables=[(51,1)]),mon(variables=[(73,1)]))}
assert affine == {int(i):jp(ts) for i,ts in cert['affine_substitutions'].items()}
clears = {r['name']:r['multiplyByParameterPower'] for r in cert['affine_rows']}
after_affine = {r['name']:mul(sub(jp(r['terms']),affine),mon(power=clears[r['name']])) for r in primitive['residuals']}

# Use the new coordinate 78 as the unit w, with coordinate 77 = w^-1.
laurent_map = {}
for i in range(1,197):
    if i in (77,78,79):
        laurent_map[i] = mon(variables=[(78, {77:-1,78:1,79:2}[i])])
    else:
        j = i if i < 79 else i - 1
        laurent_map[i] = mul(mon(variables=[(78,weights.get(i,0))]), mon(variables=[(j,1)]))
param_map = {j:mon(power=k,variables=[(j,1)]) for j,k in scales.items()}
unit_restriction = {77:mon(variables=[(78,-1)])}
assert not sub(after_affine['detector0.inverseWeightSquared.definition'],laurent_map)
guard_name = 'detector0.inverseWeight.definition'
final_rows = rows(final)
assert_same(final_rows[guard_name], add(mon(),mon(-1,variables=[(77,1),(78,1)])), 'literal retained guard')
assert_same(final_rows[guard_name], rows(primitive)[guard_name], 'unchanged guard sign')
for rec in cert['laurent']['rows']:
    old = primitive['residuals'][rec['source_row']-1]
    new = final['residuals'][rec['target_row']-1]
    assert old['name'] == new['name']
    got = sub(after_affine[old['name']],laurent_map)
    got = mul(got,mon(Q(rec['primitive_multiplier']), variables=[(78,-rec['division_exponents'][0])]))
    got = sub(got,param_map)
    got = mul(got,mon(power=-cert['parameter_scaling']['row_shifts'][new['name']]))
    expected = sub(printed[new['id']],unit_restriction)
    assert_same(got,expected,('Laurent final',new['id']))

# Expand only the parsed printed rows, not the upstream polynomial or comments.
expanded = add(*(mul(p,p) for p in printed.values()))
profiles = defaultdict(lambda:[Q(0),Q(0),Q(0)])
for (c,m),a in expanded.items():
    assert 0 <= c <= 2
    assert a.denominator == 1
    profiles[m][c] += a
assert len(expanded) == 2965 and len(profiles) == 2956
assert max(sum(e for i,e in m) for c,m in expanded) == 4
assert profiles[((1,4),)] == [1,0,0]
assert sum(any(i == 1 for c,m in p for i,e in m) for p in printed.values()) == 1
assert gcd(*(int(a) for a in expanded.values())) == 1
upstream_poly = read('affine_laurent195_v45/polynomial-family.json')
assert_same(expanded,jp(upstream_poly['terms']),'printed quartic expansion')

def shift(a,b):
    return [sum(a[k]*comb(k,j)*b**(k-j) for k in range(j,len(a))) for j in range(len(a))]

def ev(a,b): return sum(x*b**i for i,x in enumerate(a))
K = 126616122944180358034867798936
dominant = [0,0,22201]
support_min = None; shifted_checks = []
for m,a in profiles.items():
    sign = 1 if next(x for x in reversed(a) if x) > 0 else -1
    signed_shift = shift([sign*x for x in a],149)
    assert signed_shift[0] > 0 and all(x >= 0 for x in signed_shift)
    support_min = signed_shift[0] if support_min is None else min(support_min,signed_shift[0])
    for sign in (1,-1):
        b = shift([dominant[i]+sign*a[i] for i in range(3)],149**6)
        assert all(x>=0 for x in b), (m,a,sign,b)
    shifted_checks.append(dict(monomial=list(m),coefficients=[int(x) for x in a],
                               signed_at_149=[int(x) for x in signed_shift]))
low = {n:max(abs(ev(a,149**n)) for a in profiles.values()) for n in range(1,6)}
assert set(low.values()) == {K}
assert any(a == dominant for a in profiles.values())
assert any(a == [K,0,0] or a == [-K,0,0] for a in profiles.values())
assert 149**12 < K < 149**14
paper_paths = ['papers/quartic/quartic195_20261116_v45.tex',
               'papers/quartic/primitive_quadratic_bases_20261115_v40.tex',
               'papers/quartic/quartic196_redundancy_20261115_v40.tex']
for relative in paper_paths:
    p = SRC.parents[1] / relative
    b = p.read_bytes()
    inputs[p.relative_to(REPO).as_posix()] = dict(bytes=len(b), sha256=sha256(b).hexdigest())
    assert inputs[p.relative_to(REPO).as_posix()]['sha256'] == pinned[relative]

report = dict(manuscript_sha256=SHA, source_commit=download_manifest['commit'], inputs=inputs,
              parsed_rows=len(printed), matrix_entries=64, matrix_determinant=str(det),
              laurent_nonzero_weights=len(weights), final_nonzero_C_weights=len(scales),
              initial_balancing_rows=len(balanced['residuals']),primitive_rows=len(primitive['residuals']),
              redundant_block_components=len(physical_pairs),
              exceptional_stratum_values=[str(x15),str(x16)],
              exceptional_stratum_nonzero_residuals=['1399113877520/928557','866355785474/928557'],
              final_Laurent_rows=175, deleted_square_identity=True, literal_inverse_guard=True,
              parameter_terms=len(expanded), coordinate_monomials=len(profiles),
              parameter_degree=2, degree=4, input_fourth_power_coefficient=1,
              support_checks=len(profiles), minimum_signed_profile_at_149=int(support_min),
              height_at_N_1_through_5={str(n):int(x) for n,x in low.items()},
              dominant_profile=dominant, dominance_halfline='C >= 149^6',
              K_witnesses=[list(m) for m,a in profiles.items() if a == [K,0,0] or a == [-K,0,0]],
              dominant_profile_witnesses=[list(m) for m,a in profiles.items() if a == dominant],
              dominance_shift_checks=2*len(profiles), fixed_height=K,
              threshold_values={'149^12':149**12,'K':K,'149^14':149**14},
              exact_height='max(K,149^(2N+2)) for every integer N>=1',
              result='PASS: component check only, not release acceptance')
(OUT/'195-verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
(OUT/'195-coefficient-profiles.json').write_text(json.dumps(shifted_checks,indent=2)+'\n',encoding='utf-8')
(OUT/'195-redundant-block-components.json').write_text(json.dumps(physical_pairs,indent=2)+'\n',encoding='utf-8')
assert sha256(MS.read_bytes()).hexdigest() == SHA
print(json.dumps({k:v for k,v in report.items() if k!='inputs'},indent=2))
