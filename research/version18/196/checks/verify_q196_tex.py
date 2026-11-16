"""Independently parse the visible 196-coordinate TeX and compare exact data."""
from pathlib import Path
from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
from functools import reduce
from math import gcd
import re,json

import argparse
import sys

if not __debug__:
    raise SystemExit('Run without -O; assertions are required.')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-root', type=Path, required=True)
parser.add_argument('--rows', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
ROOT = args.source_root.resolve()
SOURCE = ROOT / 'computation/quartic/laurent_recovery_v38'
texpath = args.rows.resolve()
OUTPUT = args.output.resolve()
if OUTPUT.is_relative_to(ROOT) or OUTPUT == texpath or OUTPUT.exists():
    raise SystemExit('Output must be new and outside the source inputs.')
OUTPUT.parent.mkdir(parents=True, exist_ok=True)
tex = texpath.read_text(encoding='utf-8')
body='\n'.join(line for line in tex.splitlines() if not line.lstrip().startswith('%'))
def clean(x):return x.replace(r'\\','').replace('&{}','').replace('&','').replace('={}','=').strip()
aliases={}
for block in re.findall(r'\\begin\{aligned\}(.*?)\\end\{aligned\}',body,re.S):
    match=re.match(r'\s*\\mathsf\{k\}_\{(\d+)\}\s*&=\{\}\s*(.*)',block,re.S)
    if not match:continue
    value=0
    for term in clean(match[2]).split('+'):
        m=re.fullmatch(r'\s*(\d+)(?:\\cdot\s*10\^\{(\d+)\})?\s*',term);assert m,term
        value+=int(m[1])*10**int(m[2] or 0)
    i=int(match[1]);assert i not in aliases;aliases[i]=value
assert set(aliases)==set(range(1,len(aliases)+1))
# Parse both constant definitions numerically rather than importing generator values.
hm=re.search(r'H=(\d+)\^\{(\d+)\}',body);assert hm
km=re.search(r'K=(\d+)\\cdot(\d+)\^\{(\d+)\}',body);assert km
H=int(hm[1])**int(hm[2]);K=int(km[1])*int(km[2])**int(km[3])
def scale(token):
    m=re.fullmatch(r'(-?)(\d+)?([HK])?(?:\^\{(-?\d+)\})?',token);assert m and (m[2] or m[3]),token
    v=Fraction({'H':H,'K':K}[m[3]])**int(m[4] or 1) if m[3] else Fraction(1)
    assert m[3] or not m[4]
    return (-1 if m[1] else 1)*int(m[2] or 1)*v
coordinates=[]
for line in body.splitlines():
    m=re.fullmatch(r'\\\(Y_\{(\d+)\}\\\) & (\d+) & \\\((.*?)\\\) & (-?\d+) & (-?\d+) & (-?\d+) & \\texttt\{(.*)\} \\\\',line)
    if not m:continue
    coordinates.append({'id':int(m[1])+1,'parent_id':int(m[2]),'scale':scale(m[3]),
        'weight':list(map(int,m.group(4,5,6))),'name':m[7].replace(r'\allowbreak{}','').replace(r'\_','_')})
assert [co['id'] for co in coordinates]==list(range(1,197))
assert [co['parent_id'] for co in coordinates]==[i for i in range(1,199) if i not in (80,95)]
base=re.search(r'R=Y_\{(\d+)\},\\quad w_0=Y_\{(\d+)\},\\quad w_1=Y_\{(\d+)\}',body);assert base
assert [coordinates[int(i)]['parent_id'] for i in base.groups()]==[116,78,93]
assert r'X_j^{[198]}=c_jR^{a_j}w_0^{b_j}w_1^{e_j}Y_i' in body
deleted={}
for match in re.finditer(r'X_\{(\d+)\}\^\{\[198\]\}=(.*?)(?:,|\.)',body):
    j=int(match[1]);rhs=match[2];weight=[0,0,0]
    for symbol,exponent in re.findall(r'(R|w_[01])\^\{(-?\d+)\}',rhs):weight[{'R':0,'w_0':1,'w_1':2}[symbol]]=int(exponent)
    assert re.sub(r'(R|w_[01])\^\{-?\d+\}','',rhs)==''
    deleted[j]=weight
assert deleted=={80:[0,4,0],95:[-1,0,4]}
guardpowers={}
for match in re.finditer(r'Y_\{(\d+)\}=(R|w_[01])\^\{(-?\d+)\}',body):
    powers=[0,0,0];powers[{'R':0,'w_0':1,'w_1':2}[match[2]]]=int(match[3])
    guardpowers[coordinates[int(match[1])]['parent_id']]=powers
assert guardpowers=={115:[2,0,0],77:[0,-1,0],79:[0,2,0],92:[0,0,-1],94:[0,0,2]}
rowmultipliers={}
for line in body.splitlines():
    m=re.fullmatch(r'\\\((\d+)\\\) & \\\((\d+)\\\) & (-?\d+) & (-?\d+) & (-?\d+) & \\\((.*?)\\\) \\\\',line)
    if not m:continue
    i=int(m[2]);assert i not in rowmultipliers
    rowmultipliers[i]=(int(m[1]),tuple(map(int,m.group(3,4,5))),scale(m[6]))
assert set(rowmultipliers)==set(range(1,183))
assert r'q_i^{[196]}=\eta_i R^{-s_R}w_0^{-s_0}w_1^{-s_1}f_r(\Phi(\mathbf Y))' in body

token=re.compile(r'(?:\\mathsf\{k\}_\{(?P<alias>\d+)\}|Y_\{(?P<y>\d+)\}(?:\^\{(?P<ye>\d+)\})?|A(?:\^\{(?P<ae>\d+)\})?|(?P<int>\d+))')
rows={}
for block in re.findall(r'\\begin\{equation\}(.*?)\\end\{equation\}',body,re.S):
    m=re.fullmatch(r'\\label\{q196:row:(\d+)\}\s*\\begin\{aligned\}\s*q_\{(\d+)\}\^\{\[196\]\}\s*&=\{\}\s*(.*?)\s*\\end\{aligned\}\s*',block,re.S);assert m
    rid=int(m[1]);assert rid==int(m[2]);rhs=re.sub(r'\s+','',clean(m[3]))
    if rhs[0] not in '+-':rhs='+'+rhs
    p={}
    for signed in re.findall(r'[+-][^+-]+',rhs):
        value=1 if signed[0]=='+' else -1;ap=0;mon=[];pos=1
        while pos<len(signed):
            t=token.match(signed,pos);assert t,(rid,signed,pos)
            if t['alias']:value*=aliases[int(t['alias'])]
            elif t['y'] is not None:
                y=int(t['y']);assert 0<=y<196;mon.extend([y+1]*int(t['ye'] or 1))
            elif t['int']:value*=int(t['int'])
            else:ap+=int(t['ae'] or 1)
            pos=t.end()
        key=ap,tuple(sorted(mon));assert key not in p;p[key]=value
    assert rid not in rows;rows[rid]=p
assert set(rows)==set(range(1,183))
source=json.loads((SOURCE/'family196/quadratic.json').read_text(encoding='utf-8'))
cfg=json.loads((SOURCE/'config196.json').read_text(encoding='utf-8'))
parent=json.loads((ROOT/'sources/h10_quartic198/circuits/inverse198/quadratic.json').read_text(encoding='utf-8'))
assert all(parent['coordinates'][j-1]['name'] in body for j in (80,95))
for got,want in zip(coordinates,source['coordinates']):
    assert all(got[key]==want[key] for key in ('id','name','parent_id'))
    j=got['parent_id'];assert got['name']==parent['coordinates'][j-1]['name']
    assert got['scale']==Fraction(cfg['constants'].get(str(j),'1'))
    assert got['weight']==cfg['weights'].get(str(j),[0,0,0])
for j,w in deleted.items():assert w==cfg['powers'][str(j)]
certificate=json.loads((SOURCE/'family196/certificate.json').read_text(encoding='utf-8'))
for row in certificate['rows']:
    assert rowmultipliers[row['target_row']]==(row['source_row'],tuple(row['division_exponents']),Fraction(row['primitive_multiplier']))
def decode(row):return {(t['parameterPower'],tuple(t['monomial'])):int(t['coefficient']) for t in row['terms']}
for row in source['residuals']:
    p=rows[row['id']];assert p==decode(row)
    assert max(len(mon) for ap,mon in p)<=2
    assert reduce(gcd,(abs(cf) for (ap,mon),cf in p.items() if ap==0))==1
# Verify all row identities again using the parsed map and parsed multipliers.
oldpowers=dict(deleted);oldpowers.update(guardpowers)
for oldid,power in zip((116,78,93),((1,0,0),(0,1,0),(0,0,1))):oldpowers[oldid]=power
byold={co['parent_id']:co for co in coordinates}
def laurent(poly,old):
    answer=defaultdict(Fraction)
    for (ap,mon),cf in poly.items():
        cf=Fraction(cf);powers=[0,0,0];rest=[]
        for index in mon:
            oldid=index if old else coordinates[index-1]['parent_id']
            if old and oldid not in deleted:
                co=byold[oldid];cf*=co['scale']
                powers=[a+b for a,b in zip(powers,co['weight'])]
            if oldid in oldpowers:powers=[a+b for a,b in zip(powers,oldpowers[oldid])]
            else:rest.append(byold[oldid]['id'])
        answer[ap,tuple(sorted(rest)),tuple(powers)]+=cf
    return {k:v for k,v in answer.items() if v}
for i,(oldrow,shift,multiplier) in rowmultipliers.items():
    left=laurent(decode(parent['residuals'][oldrow-1]),True)
    transformed={(ap,mon,tuple(a-b for a,b in zip(power,shift))):cf*multiplier for (ap,mon,power),cf in left.items()}
    assert transformed==laurent(rows[i],False),i
assert {oldrow for oldrow,shift,multiplier in rowmultipliers.values()}==set(range(1,185))-{58,59}
for r in (58,59):assert laurent(decode(parent['residuals'][r-1]),True)=={}
expanded=defaultdict(int)
for p in rows.values():
    terms=list(p.items())
    for i,((a,m),c) in enumerate(terms):
        for j in range(i,len(terms)):
            (b,n),d=terms[j];expanded[a+b,tuple(sorted(m+n))]+=c*d*(1 if i==j else 2)
expanded={k:v for k,v in expanded.items() if v}
assert expanded==decode(json.loads((SOURCE/'family196/polynomial.json').read_text(encoding='utf-8')))
assert len(expanded)==2943 and expanded[0,(1,1,1,1)]==1
assert len({mon for ap,mon in expanded})==2943
assert max(len(mon) for ap,mon in expanded)==4
assert {i for ap,mon in expanded for i in mon}==set(range(1,197))
labels=re.findall(r'\\label\{([^}]+)\}',body)
assert len(labels)==len(set(labels))==184 and 'q196:rows' not in labels
assert '\\documentclass' not in body and '\\usepackage' not in body
assert not re.search(r'(?:[A-Za-z]:[/\\]|(?:work|Users)/)',body)
raw=(SOURCE/'family196/quadratic.json').read_bytes();assert b'\r' not in raw
crlf_sha=sha256(raw.replace(b'\n',b'\r\n')).hexdigest()
assert crlf_sha=='cb7a58486ca9b9bee156bee83e5c14488a1df06d2cb80305ff1293639d3be61b'
report={'status':'PASS','component_sha256':sha256(texpath.read_bytes()).hexdigest(),
 'source_quadratic_sha256':sha256((SOURCE/'family196/quadratic.json').read_bytes()).hexdigest(),
 'source_polynomial_sha256':sha256((SOURCE/'family196/polynomial.json').read_bytes()).hexdigest(),
 'coordinate_count':len(coordinates),'rows':len(rows),'integer_aliases':len(aliases),
 'old198_coordinate_map_exact':True,'all_Laurent_weights_and_nine_constants_exact':True,
 'all_182_printed_row_multipliers_exact':True,'all_182_Laurent_identities_reverified':True,
 'two_deleted_defining_rows_vanish':True,'source_quadratic_CRLF_hash':crlf_sha,
 'deleted_old198_coordinates':sorted(deleted),'all_row_coefficients_equal':True,
 'all_rows_primitive':True,'expanded_quartic_equal':True,'quartic_terms':len(expanded),
 'degree':4,'content':1,'all_coordinates_used':True,
 'convention':'Y_0=input; source coordinate i is Y_(i-1); A is a coefficient',
 'defined_labels':labels,'root_owned_label':'q196:rows',
 'scope':'Exact visible-TeX transcription and parent-map check; no new arithmetic claims.'}
OUTPUT.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in report.items() if k!='defined_labels'},indent=2))
