"""Independent finite verification of Brox's accepted 229-coordinate data.

This program implements the algebra directly. It neither imports nor executes
contributor programs. Arithmetic existence and soundness are separate proofs.
"""
from __future__ import annotations
import hashlib
import json
import math
import re
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / 'inputs/brox229'
BASE = 149
N = 15


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load(name):
    return json.loads((DATA / name).read_text(encoding='utf-8'))


def clean(p):
    return {k: c for k, c in p.items() if c}


def add(*polys):
    result = {}
    for p in polys:
        for k, c in p.items():
            result[k] = result.get(k, 0) + c
    return clean(result)


def scale(p, c):
    return clean({k: c*v for k, v in p.items()})


def mul(p, q):
    result = {}
    for (ep, mp), cp in p.items():
        for (eq, mq), cq in q.items():
            k = ep+eq, tuple(sorted(mp+mq))
            result[k] = result.get(k, 0) + cp*cq
    return clean(result)


def const(c):
    return {(0, ()): c} if c else {}


def x(i, e=0):
    return {(e, (i,)): 1}


def power(p, n):
    value = const(1)
    for _ in range(n):
        value = mul(value, p)
    return value


def field_add(*pairs):
    return add(*(p[0] for p in pairs)), add(*(p[1] for p in pairs))


def field_mul(p, q):
    return add(mul(p[0], q[0]), scale(mul(p[1], q[1]), 2)), add(mul(p[0], q[1]), mul(p[1], q[0]))


def pair(i, e=0):
    return x(i, e), x(i+1, e)


def terms(items, n, parameter, degree):
    answer = {}
    for term in items:
        require(set(term) == ({'parameterPower','monomial','coefficient'} if parameter else {'monomial','coefficient'}), 'unknown term fields')
        m = tuple(term['monomial'])
        require(all(type(i) is int and 1 <= i <= n for i in m), 'coordinate outside declared domain')
        require(tuple(sorted(m)) == m and len(m) <= degree, 'noncanonical monomial')
        raw = term['coefficient']
        require(isinstance(raw,str) and re.fullmatch(r'-?[1-9][0-9]*',raw), 'noncanonical integer coefficient')
        e = term['parameterPower'] if parameter else 0
        require(type(e) is int and e >= 0, 'invalid parameter exponent')
        key = (e,m)
        require(key not in answer, 'duplicate term')
        answer[key] = int(raw)
    return answer


def rows(document, n, count, parameter):
    require(document['variables'] == n and document['inputCoordinate'] == 1, 'coordinate convention')
    if parameter:
        require([c['id'] for c in document['coordinates']] == list(range(1,n+1)), 'coordinate inventory')
    rs = document['residuals']
    require(len(rs) == count, 'row count')
    clone_ids = dict(zip(range(176,207), [*range(34,47),*range(83,101)]))
    for i,r in enumerate(rs,1):
        expected = {'id','name','terms'}
        if parameter and n == 229 and i in clone_ids:
            expected.add('clonedFrom195Row')
            require(r.get('clonedFrom195Row') == clone_ids[i], 'cloned-row provenance')
        require(set(r) == expected and r['id'] == i, 'row fields or numbering')
    return [terms(r['terms'],n,parameter,2) for r in rs]


def authenticate():
    manifest = json.loads((HERE/'INPUTS.json').read_text(encoding='utf-8'))
    for item in manifest['files']:
        p = (HERE/item['path']).resolve()
        require(p.is_relative_to(HERE.resolve()), 'input path escapes construction')
        data = p.read_bytes()
        require(len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], 'input digest: '+item['path'])
    parent = HERE.parents[2]/'research/version19/construction/inputs/jose/computation/quartic/affine_laurent195_v45/quadratic-family.json'
    require(parent.read_bytes() == (DATA/'source/quadratic195.json').read_bytes(), 'retained 195 table differs')


def graft_checks(parent, source):
    changed = {22,24,25,34,36,37,175}
    require(all(parent[i-1] == source[i-1] for i in range(1,176) if i not in changed), 'parent row changed')
    require(source[174] == add(parent[174],scale(power(x(77),2),12)), 'aggregate 14 to 26')
    old_coords = [7,8,9,10,*range(86,100),*range(134,150)]
    mapping = dict(zip(old_coords,range(196,230)))
    old_rows = [*range(34,47),*range(83,101)]
    for old,new in zip(old_rows,range(176,207)):
        copied = {(e,tuple(sorted(mapping.get(i,i) for i in m))):c for (e,m),c in source[old-1].items()}
        require(copied == source[new-1], f'cloned row {new}')
    for i,r in enumerate(parent,1):
        used = {j for _,m in r for j in m} & set(old_coords)
        if i not in old_rows:
            require(not used or (i==175 and used=={86}), 'unexpected parent detector consumer')
    theta = [F(0),F(-1,2),F(-1),F(1,2399),F(-32,407)]
    alpha = [(22*t-3)**2 for t in theta]
    es = [F(1)]
    for a in alpha:
        es = [es[0]]+[es[j]+a*es[j-1] for j in range(1,len(es))]+[a*es[-1]]
    L=math.lcm(*(a.denominator for a in es))
    integers = [int(L*a) for a in es]
    require(integers == [7878870169,6786192246520,1229741066709366,42042541279847500,476802068222265625,1738195040039062500], 'reflected coefficients')
    _,e1,e2,e3,e4,e5 = integers
    for j,(argument,r,s,v,w,start,guard) in enumerate([(2,74,75,76,None,22,26),(86,87,88,89,91,34,38),(200,201,202,203,205,176,180)]):
        q=x(77); T=x(argument); R=x(r); S=x(s); V=x(v,1 if j==0 else 0); W=const(1) if w is None else x(w)
        expected = [add(power(add(scale(T,22),scale(q,-3)),2),scale(mul(R,q),-1)),
                    add(power(R,2),scale(mul(S,q),-1)),
                    add(scale(mul(R,S),L),scale(mul(add(q,W),S),-e1),scale(mul(add(q,W),R),e2),scale(mul(V,q),-1)),
                    add(mul(S,V),scale(mul(add(q,W),add(scale(S,e3),scale(R,-e4),scale(q,e5))),-1))]
        signs=[1,1,1,1] if j==0 else [1,-1,1,-1]
        for offset,(p,sign) in enumerate(zip(expected,signs)):
            require(source[start+offset-1] == scale(p,sign), f'contact row {start+offset}')
        helpers={r,s,v}
        for i,row in enumerate(source,1):
            require(not ({a for _,m in row for a in m}&helpers) or start <= i < start+4, 'contact helper escapes its four rows')
        u,inv=(77,78) if j==0 else (90,91) if j==1 else (204,205)
        require(source[guard-1] == add(const(1),scale(mul(x(u),x(inv)),-1)), 'literal inverse guard')
    D = (const(11),const(-6))
    Q = (x(77),{})
    total = ({},{})
    for s,f,g in [(160,(152,0),156),(170,(162,1),166),(180,(172,1),176)]:
        total = field_add(total,field_mul(pair(s),pair(s)),field_mul(field_mul(Q,D),field_add(pair(*f),pair(g))))
    total=field_add(total,field_mul(Q,pair(192)))
    require(source[174] == add(total[0],scale(mul(x(77),add(x(2),scale(x(86),-1))),2),scale(power(x(77),2),26)), 'rational aggregate')
    require(source[206] == add(total[1],scale(mul(x(77),add(x(2),scale(x(86),-2),x(200))),2),scale(power(x(77),2),-8)), 'sqrt(2) aggregate')
    for start,s,f,g,k,l in [(111,160,(152,0),156,154,158),(127,170,(162,1),166,164,168),(143,180,(172,1),176,174,178)]:
        negative_f = tuple(scale(v,-1) for v in pair(*f))
        value = field_add(field_mul(field_add(pair(g),negative_f),pair(s)),field_mul((x(77,1),{}),field_add(pair(k),pair(l))))
        require(source[start-1:start+1] == list(value), 'secant components')
    for start,scalar,left,right,out in [(155,x(112),pair(182,1),pair(184),pair(192)),(157,x(77),pair(186,1),pair(192),pair(190))]:
        product=field_mul(left,right)
        expected=field_add(field_mul((scalar,{}),out),tuple(scale(v,-1) for v in product))
        require(source[start-1:start+1] == list(expected), 'inverse-Vieta components')
    return {'unchanged_parent_rows':168,'cloned_rows':31,'cloned_coordinates':34,'contact_rows':12,'isolated_contact_helpers':9,'aggregate_components':2,'field_component_rows':10}


def specialize(source, transform):
    require(transform['base']==BASE and transform['fixed_N']==N and transform['variables']==229 and transform['inputCoordinate']==1, 'normalization parameters')
    a,b=transform['coordinate_powers'],transform['row_powers']
    require(len(a)==229 and len(b)==207 and a[0]==0, 'normalization lengths or input')
    require(all(type(k) is int for k in a+b), 'nonintegral exponents')
    require(all(F(BASE)**k*F(BASE)**(-k)==1 for k in a+b), 'inverse scalars')
    output=[]
    for j,r in enumerate(source):
        row={}
        for (e,m),c in r.items():
            key=(0,m); row[key]=row.get(key,F(0))+c*F(BASE)**(N*e+b[j]+sum(a[i-1] for i in m))
        require(all(c.denominator==1 for c in row.values()), f'noninteger normalized row {j+1}')
        row=clean({k:int(c) for k,c in row.items()})
        require(math.gcd(*row.values())==1, f'nonprimitive row {j+1}')
        output.append(row)
    return output


def expand(rs):
    return add(*(mul(r,r) for r in rs))


def render(poly):
    pieces=[]
    for (e,m),c in sorted(poly.items()):
        require(e==0, 'parameter in literal polynomial')
        factors=[]
        if abs(c)!=1 or not m: factors.append(str(abs(c)))
        for i,n in sorted(Counter(m).items()):
            factors.append(f'x{i}'+(f'^{n}' if n>1 else ''))
        pieces.append(('-' if c<0 else '+' if pieces else '')+'*'.join(factors))
    return ''.join(pieces).encode('ascii')


def parse_literal(data):
    text=data.decode('ascii'); require(text and not any(c.isspace() for c in text), 'literal whitespace')
    result={}; pos=0
    for match in re.finditer(r'[+-]?[^+-]+',text):
        require(match.start()==pos, 'literal unparsed segment'); pos=match.end(); term=match.group()
        sign=-1 if term.startswith('-') else 1
        if term[0] in '+-': term=term[1:]
        factors=term.split('*'); coefficient=sign; m=[]
        for j,factor in enumerate(factors):
            if re.fullmatch(r'[1-9][0-9]*',factor):
                require(j==0, 'coefficient order');coefficient*=int(factor)
            else:
                match_x=re.fullmatch(r'x([1-9][0-9]*)(?:\^([234]))?',factor)
                require(match_x is not None, 'literal factor')
                i=int(match_x[1]); require(1<=i<=229,'literal coordinate');m.extend([i]*int(match_x[2] or 1))
        require(m==sorted(m) and len(m)<=4,'literal monomial')
        key=(0,tuple(m));require(key not in result,'duplicate literal monomial');result[key]=coefficient
    require(pos==len(text),'literal trailing segment')
    return result


def main():
    authenticate()
    parent=rows(load('source/quadratic195.json'),195,175,True)
    source=rows(load('source/quadratic229-v62.json'),229,207,True)
    graft=graft_checks(parent,source)
    final=specialize(source,load('transformation.json'))
    require(final==rows(load('quadratic.json'),229,207,False),'normalized source does not equal compact rows')
    polynomial=expand(final)
    require(polynomial==terms(load('polynomial.json')['terms'],229,False,4),'expanded coefficient mismatch')
    literal=render(polynomial)
    require(literal==(DATA/'quartic229-N15.txt').read_bytes(),'plain text mismatch')
    require(parse_literal(literal)==polynomial,'independent literal parse mismatch')
    used=sorted({i for _,m in polynomial for i in m});height=max(abs(c) for c in polynomial.values())
    require(used==list(range(1,230)),'variable support');require(len(polynomial)==3312,'monomial count')
    require(max(len(m) for _,m in polynomial)==4,'degree');require(math.gcd(*polynomial.values())==1,'content')
    require(polynomial[(0,(1,1,1,1))]==1,'leading input coefficient')
    require(height==BASE**30,'coefficient height');require(len(literal)==74007,'plain text bytes')
    require(hashlib.sha256(literal).hexdigest()=='45bdea1ea7876bf6ec10b5427f9403cf1f94c144fab35817aa545bcb2cea1975','plain text hash')
    source_fixed=[clean({(0,m):sum(c*BASE**(N*e) for (e,mm),c in row.items() if mm==m) for _,m in row}) for row in source]
    source_poly=expand(source_fixed)
    require(set(source_poly)==set(polynomial) and max(abs(c) for c in source_poly.values())==BASE**32,'source height and support')
    return {'scope':'Finite data verification only; no arithmetic proof or manuscript coverage claimed.','graft':graft,'rows':len(final),'variables':len(used),'monomials':len(polynomial),'degree':4,'content':1,'input_quartic_coefficient':1,'height':str(height),'height_bits':height.bit_length(),'bytes':len(literal),'plain_sha256':hashlib.sha256(literal).hexdigest(),'source_height':str(BASE**32),'input_coordinate_fixed':True,'all_diagonal_inverse_products':True}


if __name__=='__main__':
    print(json.dumps(main(),indent=2))
