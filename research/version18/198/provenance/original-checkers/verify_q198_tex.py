"""Parse visible TeX integer definitions and equations back into the exact table.

Comments, source hashes and JSON receipts are not used as substitutes for
parsing the printed coefficients. The recovered rows are expanded afresh.
"""
from pathlib import Path
from collections import defaultdict
from hashlib import sha256
import json,re

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parents[2]/'v18-198-dependency-inventory-20261114/package/H10-quartic198/circuits/inverse198'
texpath=HERE/'q198-rows.tex';tex=texpath.read_text()
body='\n'.join(line for line in tex.splitlines() if not line.lstrip().startswith('%'))
def math_clean(text):return text.replace(r'\\','').replace('&{}','').replace('&','').replace('={}','=') .strip()
aliases={}
for block in re.findall(r'\\begin\{aligned\}(.*?)\\end\{aligned\}',body,re.S):
    match=re.match(r'\s*\\mathsf\{k\}_\{(\d+)\}\s*&=\{\}\s*(.*)',block,re.S)
    if not match:continue
    i=int(match[1]);rhs=math_clean(match[2]);value=0
    for term in rhs.split('+'):
        m=re.fullmatch(r'\s*(\d+)(?:\\cdot\s*10\^\{(\d+)\})?\s*',term)
        assert m,term
        value+=int(m[1])*10**int(m[2] or 0)
    assert i not in aliases
    aliases[i]=value
assert set(aliases)==set(range(1,78))

coordinates=[]
for line in body.splitlines():
    m=re.fullmatch(r'\\\(Y_\{(\d+)\}\\\) & (\d+) & (-?\d+) & \\texttt\{(.*)\} \\\\',line)
    if not m:continue
    name=m[4].replace(r'\allowbreak{}','').replace(r'\_','_')
    coordinates.append({'id':int(m[1])+1,'formalId':int(m[2]),'rescalingExponent':int(m[3]),'name':name})
assert [co['id'] for co in coordinates]==list(range(1,199))

token=re.compile(r'(?:\\mathsf\{k\}_\{(?P<alias>\d+)\}|Y_\{(?P<y>\d+)\}(?:\^\{(?P<ye>\d+)\})?|A(?:\^\{(?P<ae>\d+)\})?|(?P<int>\d+))')
rows={}
for block in re.findall(r'\\begin\{equation\}(.*?)\\end\{equation\}',body,re.S):
    m=re.fullmatch(r'\\label\{q198:row:(\d+)\}\s*\\begin\{aligned\}\s*q_\{(\d+)\}\^\{\[198\]\}\s*&=\{\}\s*(.*?)\s*\\end\{aligned\}\s*',block,re.S)
    assert m,block[:120]
    rid=int(m[1]);assert rid==int(m[2]);rhs=math_clean(m[3]);rhs=re.sub(r'\s+','',rhs)
    if rhs[0] not in '+-':rhs='+'+rhs
    parsed={}
    for signed in re.findall(r'[+-][^+-]+',rhs):
        value=1 if signed[0]=='+' else -1;power=0;monomial=[];pos=1
        while pos<len(signed):
            match=token.match(signed,pos);assert match,(rid,signed,pos)
            if match['alias']:value*=aliases[int(match['alias'])]
            elif match['y'] is not None:
                yi=int(match['y']);assert 0<=yi<=197
                monomial += [yi+1]*int(match['ye'] or 1)
            elif match['int']:value*=int(match['int'])
            else:power+=int(match['ae'] or 1)
            pos=match.end()
        key=power,tuple(sorted(monomial));assert key not in parsed
        parsed[key]=value
    assert rid not in rows
    rows[rid]=parsed
assert set(rows)==set(range(1,185))
source=json.loads((SOURCE/'quadratic.json').read_text())
def decode(data):return {(t['parameterPower'],tuple(t['monomial'])):int(t['coefficient']) for t in data['terms']}
for co,want in zip(coordinates,source['coordinates']):assert all(co[k]==want[k] for k in co)
for row in source['residuals']:assert rows[row['id']]==decode(row),row['id']
expanded=defaultdict(int)
for p in rows.values():
    ts=list(p.items())
    for i,((a,m),c) in enumerate(ts):
        for j in range(i,len(ts)):
            (b,n),d=ts[j];expanded[a+b,tuple(sorted(m+n))]+=c*d*(1 if i==j else 2)
expanded={k:v for k,v in expanded.items() if v}
assert expanded==decode(json.loads((SOURCE/'polynomial.json').read_text()))
labels=re.findall(r'\\label\{([^}]+)\}',body)
assert len(labels)==len(set(labels))==185
assert 'q198:rows' not in labels
assert '\\documentclass' not in body and '\\usepackage' not in body
assert not re.search(r'(?:[A-Za-z]:[/\\]|(?:work|Users)/)',body)
assert len(expanded)==2945 and expanded[0,(1,1,1,1)]==1
report={'status':'PASS','component':'q198-rows.tex','component_sha256':sha256(texpath.read_bytes()).hexdigest(),
    'source_quadratic_sha256':sha256((SOURCE/'quadratic.json').read_bytes()).hexdigest(),
    'source_polynomial_sha256':sha256((SOURCE/'polynomial.json').read_bytes()).hexdigest(),
    'printed_integer_aliases_parsed':len(aliases),'printed_coordinates_parsed':len(coordinates),
    'printed_rows_parsed':len(rows),'all_row_coefficients_equal':True,'expanded_quartic_equal':True,
    'expanded_terms':len(expanded),'coordinate_convention':'Y_0=input x; source coordinate i is Y_(i-1); A is a coefficient',
    'defined_labels':labels,'root_owned_label':'q198:rows',
    'scope':'Literal TeX-to-polynomial roundtrip only; no additional arithmetic claims.'}
(HERE/'ROUNDTRIP.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in report.items() if k!='defined_labels'},indent=2))
