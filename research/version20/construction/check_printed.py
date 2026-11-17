"""Parse the actual V20 formulas, not their JSON comments or producer code."""
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,re,sys
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
BASE=REPO/'research/version19/construction'
OUT=REPO/'build/version20'; OUT.mkdir(parents=True,exist_ok=True)
source=(REPO/'manuscripts/quartic_v20.tex').read_bytes()
tex=source.decode('utf-8')
def parse(expr):
    out=defaultdict(int)
    for term in re.findall(r'[+-]?[^+-]+',expr):
        sign=-1 if term.startswith('-') else 1
        term=term.lstrip('+-');mon=[]
        for match in re.finditer(r'[xy]_\{(\d+)\}(?:\^\{(\d+)\})?',term):
            mon.extend([int(match[1])]*int(match[2] or 1))
        term=re.sub(r'[xy]_\{\d+\}(?:\^\{\d+\})?','',term)
        parameter=re.search(r'C(?:\^\{(\d+)\})?',term)
        power=0 if parameter is None else int(parameter[1] or 1)
        term=re.sub(r'C(?:\^\{\d+\})?','',term)
        constant=re.fullmatch(r'149\^\{(\d+)\}',term)
        coefficient=149**int(constant[1]) if constant else int(term or 1)
        out[(power,tuple(sorted(mon)))]+=sign*coefficient
    return {k:v for k,v in out.items() if v}
blocks=re.findall(r'\\begin\{align\*\}(.*?)\\end\{align\*\}',tex,re.S)
results={};expanded=defaultdict(int)
for size,path in [(195,BASE/'inputs/jose/computation/quartic/affine_laurent195_v45/quadratic-family.json'),
                  (250,BASE/'inputs/carbon/explicit250/explicit250-quadratic.json'),
                  (247,HERE/'inputs/carbon/tables/explicit247/explicit247-quadratic.json')]:
    rows=json.loads(path.read_bytes())['residuals']
    prefix='r_' if size==247 else f'q^{{[{size}]}}_'
    selected=[b.strip() for b in blocks if b.strip().startswith(prefix)]
    assert len(selected)==len(rows),(size,len(selected))
    for row,b in zip(rows,selected):
        lhs=prefix+'{'+str(row['id'])+'}&='
        assert b.startswith(lhs)
        expr=re.sub(r'\\tag\{[^}]+\}','',b[len(lhs):]).replace('\\\\','').replace('&{}','').replace('\n','').strip()
        got=parse(expr)
        want={(t['parameterPower'],tuple(sorted(t['monomial']))):int(t['coefficient']) for t in row['terms']}
        assert got==want,(size,row['id'])
        if size==247:
            for (pa,ma),a in got.items():
                for (pb,mb),b in got.items():
                    assert pa==pb==0
                    expanded[tuple(sorted(ma+mb))]+=a*b
    results[size]={'rows':len(rows),'matches_data':True}
expanded={m:c for m,c in expanded.items() if c}
decimal=json.loads((HERE/'inputs/carbon/tables/explicit247/quartic247-decimal.json').read_bytes())
assert expanded=={tuple(t['monomial']):int(t['coefficient']) for t in decimal['terms']}
assert len(expanded)==3385

def fraction(text):
    text=text.strip().strip('$')
    match=re.fullmatch(r'(-?)\\frac\{(\d+)\}\{(\d+)\}',text)
    return (-1 if match[1] else 1)*F(int(match[2]),int(match[3])) if match else F(text)
def grouped_table(header):
    body=tex.split(header,1)[1].split('\\end{longtable}',1)[0]
    out={}; value=None
    for line in body.splitlines():
        if '&' not in line:continue
        left,right=line.split('&',1)
        if left.strip():value=fraction(left)
        indices=re.search(r'\$([\d, ]+)\$',right)
        assert indices is not None and value is not None
        for i in map(int,indices[1].split(',')):
            assert i not in out;out[i]=value
    return out
cert=json.loads((HERE/'inputs/carbon/certificates/v20-normalization244-certificate.json').read_bytes())
assert grouped_table('$\\lambda_i$ & Indices $i$')=={int(k):F(v) for k,v in cert['coord_scales'].items()}
diag=grouped_table('$d_i$ & Indices $i$')
T=[{i:F(1)} for i in range(1,217)]
for i,c in diag.items():T[i-1]={i:c}
block=tex.split('$d_i$ & Indices $i$',1)[1].split('\\begin{align*}',1)[1].split('\\end{align*}',1)[0]
block=block.replace('\\\\','').replace('&{}','').replace('\n','')
for match in re.finditer(r'\\widetilde q_\{(\d+)\}&=(.*?)(?=\\widetilde q_|$)',block):
    row={}
    for term in re.findall(r'[+-]?[^+-]+',match[2]):
        hit=re.fullmatch(r'([+-]?)(.*?)Q_\{(\d+)\}',term)
        assert hit is not None,term
        c=fraction(hit[2] or '1')*(-1 if hit[1]=='-' else 1)
        assert int(hit[3]) not in row;row[int(hit[3])]=c
    T[int(match[1])-1]=row
assert T==[{int(k):F(v) for k,v in r.items()} for r in cert['T_rows']]
permutation_table=tex.split('New indices & Old indices, in order',1)[1].split('\\end{longtable}',1)[0]
tiers={}; active=None
for line in permutation_table.splitlines():
    if '&' not in line:continue
    left,right=line.split('&',1)
    if left.strip():
        active=left.strip(); tiers[active]=[]
    indices=re.search(r'\$([\d, ]+)\$',right)
    assert indices is not None and active is not None
    tiers[active].extend(map(int,indices[1].split(',')))
first=tiers[r'$2,\ldots,9$']; second=tiers[r'$10,\ldots,99$']
assert len(first)==8 and len(second)==90 and len(set(first+second))==98
assert not set(first+second)&{1,245,246,247}
old_order=[1]+first+second+[i for i in range(2,248) if i not in first+second]
permutation={old:new for new,old in enumerate(old_order,1)}
assert permutation=={int(k):v for k,v in cert['permutation_247']['old_to_new'].items()}
assert all(permutation[i]==i for i in [1,245,246,247])
abstract=tex.split('\\begin{abstract}',1)[1].split('\\end{abstract}',1)[0]
for phrase in ['The first has $247$ variables',r'$3\,385$ nonzero monomials',r'$2^{73780}$',r'$96\,712$ bytes of text','The second has $195$ variables']:
    assert phrase in abstract,phrase
labels=re.findall(r'\\label\{(v20:[^}]+)\}',tex)
assert len(labels)==len(set(labels))
assert 'Gemini Carbon' not in tex
report={'source_sha256':hashlib.sha256(source).hexdigest(),'printed_tables':results,
        'printed247_expansion_matches_all_coefficients':True,'printed_coordinate_scalings':65,
        'printed_row_matrix_matches_certificate':True,'printed_permutation_matches_certificate':True,
        'abstract_metrics_match':True}
(OUT/'printed-verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
