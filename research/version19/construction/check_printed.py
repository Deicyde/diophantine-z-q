"""Compare actual typeset formulas with tables and independently collect their squares."""
from pathlib import Path
from collections import defaultdict
from math import gcd
from functools import reduce
import re,json,hashlib
R=Path(__file__).resolve().parent
REPO=R.parents[2]
OUT=REPO/'build/version19'
OUT.mkdir(parents=True, exist_ok=True)
draft=(REPO/'manuscripts/quartic_v19.tex').read_text(encoding='utf-8')
def parse(expr):
    out=defaultdict(int)
    for term in re.findall(r'[+-]?[^+-]+',expr):
        sign=-1 if term.startswith('-') else 1
        term=term.lstrip('+-');mon=[]
        for m in re.finditer(r'[xy]_\{(\d+)\}(?:\^\{(\d+)\})?',term):
            mon += [int(m[1])]*int(m[2] or 1)
        term=re.sub(r'[xy]_\{\d+\}(?:\^\{\d+\})?','',term)
        par=re.search(r'C(?:\^\{(\d+)\})?',term)
        power=0 if par is None else int(par[1] or 1)
        term=re.sub(r'C(?:\^\{\d+\})?','',term)
        p=re.fullmatch(r'149\^\{(\d+)\}',term)
        c=149**int(p[1]) if p else int(term or 1)
        out[(power,tuple(sorted(mon)))]+=sign*c
    return {k:v for k,v in out.items() if v}
results={};expanded=defaultdict(int)
for size,source in [(195,'inputs/jose/computation/quartic/affine_laurent195_v45/quadratic-family.json'),
                    (250,'inputs/carbon/explicit250/explicit250-quadratic.json')]:
    rows=json.loads((R/source).read_bytes())['residuals']
    blocks=re.findall(r'\\begin\{align\*\}(.*?)\\end\{align\*\}',draft,re.S)
    blocks=[b for b in blocks if b.strip().startswith(f'q^{{[{size}]}}_')]
    assert len(blocks)==len(rows)
    for row,b in zip(rows,blocks):
        prefix=f'q^{{[{size}]}}_{{{row["id"]}}}&='
        b=b.strip();assert b.startswith(prefix)
        b=re.sub(r'\\tag\{[^}]+\}','',b[len(prefix):]).replace(r'\\','').replace('&{}','').replace('\n','').strip()
        got=parse(b)
        want={(t['parameterPower'],tuple(t['monomial'])):int(t['coefficient']) for t in row['terms']}
        assert got==want,(size,row['id'])
        if size==250:
            for (pa,ma),a in got.items():
                for (pb,mb),b in got.items():
                    assert pa==pb==0
                    expanded[tuple(sorted(ma+mb))]+=a*b
    results[str(size)]={'printed_rows':len(rows),'matches_inert_data':True}
expanded={m:c for m,c in expanded.items() if c}
decimal=R/'coefficients/quartic250-decimal.json'
terms=json.loads(decimal.read_bytes())['terms']
expected={tuple(t['monomial']):int(t['coefficient']) for t in terms}
assert len(expected)==len(terms) and all(t.get('parameterPower',0)==0 for t in terms)
assert expanded==expected
assert len(expanded)==3362 and reduce(gcd,expanded.values())==1
assert max(abs(c) for c in expanded.values())==149**898+1747145497790223592810060471184416344603224790540808983
abstract=draft.split(r'\begin{abstract}')[1].split(r'\end{abstract}')[0]
assert 'The first has $250$ variables' in abstract and 'The second has $195$ variables' in abstract
assert r'$3\,362$ nonzero monomials' in abstract
assert r'Written out in plain algebraic notation with every coefficient in decimal, it is $85\,737$ bytes of text.' in abstract
assert len((R/'plain-text/quartic250-decimal.txt').read_bytes()) == 85737
labels=re.findall(r'\\label\{(v19:[^}]+)\}',draft)
assert len(labels)==len(set(labels))
report={'tables':results,'printed250_squares_match_all_decimal_coefficients':True,
        'source_sha256':hashlib.sha256((REPO/'manuscripts/quartic_v19.tex').read_bytes()).hexdigest()}
(OUT/'printed-verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
