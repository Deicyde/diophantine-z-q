"""Read-only, independently written checks of the supplied research candidates.

Imports no author builder/checker. These finite identities do not accept an
arithmetic theorem or discharge a changed application contract.
"""
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict
import hashlib, json, math, re, sys
import sympy as sp

ROOT = Path(__file__).resolve().parent
EXP = Path('/tmp/claude-1000/-home-freer-math-diophantine-z-q/78a63063-c94e-475f-86a6-1c128ce9e4b9/scratchpad/explore')
PARENT = Path('/tmp/codex-glazer389-review-3j08z564/mixed/build/mixed380')
sys.set_int_max_str_digits(0)
def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def audit_table(root):
    src = read(root/'final/integer-candidate-ir.json')
    cert = read(root/'balanced/diagonal-certificate.json')
    target = read(root/'balanced/integer-ir.json')
    poly = read(root/'balanced/polynomial.json')
    ids = {c['id'] for c in src['coordinates']}
    E = int(src['fixedParameter']['value'].split('^')[1])
    p2 = {int(i):int(v) for i,v in cert['twoPowers'].items()}
    p3 = {int(i):int(v) for i,v in cert['threePowers'].items()}
    assert p2.keys() == p3.keys() == ids and p2[0] == p3[0] == 0
    assert target['coordinates'] == src['coordinates']
    assert len(src['residuals']) == len(target['residuals']) == len(cert['rows'])
    full = defaultdict(int)
    for old,new,receipt in zip(src['residuals'],target['residuals'],cert['rows']):
        assert old['id'] == new['id'] == receipt['id'] and old['name']==new['name']
        row = defaultdict(Q)
        for t in old['terms']:
            m=tuple(sorted(t['monomial'])); assert len(m)<=2 and set(m)<=ids
            row[m] += Q(t['coefficient'])*Q(3)**(E*t['sPower']+sum(p3[i] for i in m))*Q(2)**sum(p2[i] for i in m)
        row={m:v for m,v in row.items() if v}
        divisor=Q(int(receipt['divisorNumerator']),int(receipt['divisorDenominator']))
        assert divisor
        row={m:v/divisor for m,v in row.items()}
        assert all(v.denominator==1 for v in row.values())
        row={m:int(v) for m,v in row.items()}
        assert math.gcd(*row.values())==1
        actual={tuple(t['monomial']):int(t['coefficient']) for t in new['terms']}
        assert len(actual)==len(new['terms']) and row==actual
        terms=sorted(row.items())
        for i,(m,a) in enumerate(terms):
            for j in range(i,len(terms)):
                n,b=terms[j];full[tuple(sorted(m+n))]+=a*b*(1 if j==i else 2)
    cmap={c['sourceId']:c['id'] for c in poly['coordinates']}
    assert cmap.keys()==ids and cmap[0]==0 and set(cmap.values())==set(range(len(ids)))
    expected={tuple(sorted(cmap[i] for i in m)):v for m,v in full.items() if v}
    actual={tuple(t['monomial']):int(t['coefficient']) for t in poly['terms']}
    assert len(actual)==len(poly['terms']) and expected==actual
    table=root/f'quartic-{len(ids)}-balanced-decimal.txt'; parsed={}
    for line in table.read_text().splitlines():
        if line.startswith('#'):continue
        coefficient,monomial=line.split('\t'); m=[]
        if monomial!='1':
            for factor in monomial.split('*'):
                match=re.fullmatch(r'x(\d+)(?:\^(\d+))?',factor);assert match
                m.extend([int(match[1])]*int(match[2] or '1'))
        key=tuple(m);assert key not in parsed;parsed[key]=int(coefficient)
    assert parsed==expected and expected[(0,0,0,0)]==1
    assert {i for m in expected for i in m}==set(range(len(ids)))
    assert max(map(len,expected))==4 and math.gcd(*expected.values())==1
    return {'path':str(root),'coordinates':len(ids),'rows':len(src['residuals']),
            'monomials':len(expected),'digits':max(len(str(abs(v))) for v in expected.values()),
            'anchor':E,'table_sha256':sha(table),'full_diagonal_and_coefficient_check':True}

def raw_polys(root):
    d=read(root/'raw-translated-ir.json')
    symbols={c['id']:sp.Symbol(c['name']) for c in d['coordinates']}
    rows={}
    for row in d['residuals']:
        rows[row['name']]=sp.Add(*(sp.Rational(t['coefficient'])*sp.Symbol('S')**t['sPower']*sp.prod(symbols[i] for i in t['monomial']) for t in row['terms']))
    return rows,{str(s):s for s in symbols.values()}

def audit_algebra():
    old,o=raw_polys(PARENT);new,n=raw_polys(ROOT/'algebra17')
    changes=[name for name in old.keys()&new.keys() if sp.expand(new[name]-old[name])!=0]
    assert old.keys()-new.keys()=={'scalar.W2.definition'} and not new.keys()-old.keys()
    expected={'scalar.preparationT.definition','scalar.Bh.definition','scalar.secondConic',
              'scalar.shiftedS.rootTimesInverseRoot.definition.0','scalar.shiftedS.rootTimesInverseRoot.definition.1'}
    assert set(changes)==expected,(changes,expected)
    rowops=[]
    for k,(a,b) in enumerate([(sp.Rational(-39,8),18),(sp.Rational(9,2),sp.Rational(-39,4))]):
        name=f'scalar.shiftedS.rootTimesInverseRoot.definition.{k}'
        assert sp.expand(new[name]-old[name]-a*old['S.chart.x.0.definition']-b*old['S.chart.x.1.definition'])==0
        rowops.append([name,str(a),str(b)])
    ri=n['scalar.rInverse'];N=n['scalar.N'];e=n['scalar.normalized_e'];Bh=n['scalar.Bh.quadratic']
    r=sp.cancel((old['scalar.rInverse.definition']+1)/ri)
    assert ri not in r.free_symbols and old['scalar.rInverse.definition']==new['scalar.rInverse.definition']
    W2=o['scalar.W2.quadratic'];To=o['scalar.preparationT.quadratic'];Tn=n['scalar.preparationT']
    rhsT=sp.solve(old['scalar.preparationT.definition'],To)[0]
    rhsB=sp.solve(old['scalar.Bh.definition'],Bh)[0]
    mu=sp.cancel(42*r*W2*e/rhsB.subs(To,rhsT))
    assert mu==184460384539620
    # Eliminate unique private witnesses. Both directions are rational because r*ri=1.
    oldsub={W2:N**2,To:rhsT.subs(W2,N**2),Bh:42*r*N**2*e/mu,ri:1/r}
    newsub={Tn:42*r*N**2,Bh:42*r*N**2*e,ri:1/r}
    for name in ['scalar.W2.definition','scalar.preparationT.definition','scalar.Bh.definition']:
        assert sp.cancel(old[name].xreplace(oldsub))==0
    for name in ['scalar.preparationT.definition','scalar.Bh.definition']:
        assert sp.cancel(new[name].xreplace(newsub))==0
    assert sp.cancel(old['scalar.secondConic'].xreplace(oldsub)-new['scalar.secondConic'].xreplace(newsub))==0
    assert not any(v.free_symbols&{W2,To,Bh,Tn} for k,v in old.items() if k not in expected|{'scalar.W2.definition'})
    assert not any(v.free_symbols&{W2,To,Bh,Tn} for k,v in new.items() if k not in expected)
    return {'changed_common_rows':sorted(changes),'deleted':'scalar.W2.definition','row_operations':rowops,'Bh_forward_scale':str(mu),'bidirectional_rational_transport':True}

def audit_chain(root,k):
    d=read(root/'raw-translated-ir.json');names={c['name']:c['id'] for c in d['coordinates']};gates={g['coordinateId']:g for g in d['gates']}
    blocks=[]
    for block in range(3):
        prefix=f'detector{block}.';powers={names[prefix+'q1']:1}
        def expression(terms):
            assert len(terms)==1
            t=terms[0];assert Q(t['coefficient'])==1 and t['sPower']==0
            return sum(power(i) for i in t['monomial'])
        def power(i):
            if i not in powers:
                g=gates[i]
                if g['operation']=='quadratic_assignment':v=expression(g['expression'])
                else:
                    assert g['operation']=='rational_quotient'
                    v=expression(g['numerator'])-expression(g['denominator'])
                powers[i]=v
            return powers[i]
        want={'q12':23,'mixedHigh.quadratic':46,f'q{k}':2*k-1,f'E{k}.power2.quadratic':2*(2*k-1),f'E{k}.power3.quadratic':3*(2*k-1)}
        for name,v in want.items():assert power(names[prefix+name])==v
        blocks.append({'block':block,'exact_target_powers':want,'all_denominators_powers_of_positive_q1':True})
    return {'path':str(root),'order':k,'blocks':blocks}

if __name__=='__main__':
    algebra=audit_algebra();print('algebra',json.dumps(algebra),flush=True)
    tables=[]
    for path in [ROOT/'algebra17',ROOT/'combined']+sorted(p.parent.parent for p in (EXP/'compose/build').glob('*/balanced/summary.json')):
        result=audit_table(path);tables.append(result);print('table',json.dumps(result),flush=True)
    chains=[audit_chain(ROOT/'combined',46)]
    for name,k in [('i48_triA31_1692',48),('i50_triA31_1512',50)]:chains.append(audit_chain(EXP/'compose/build'/name,k))
    assert (ROOT/'combined/final/integer-candidate-ir.json').read_bytes()==(EXP/'compose/build/p46_triA_2010/final/integer-candidate-ir.json').read_bytes()
    result={'algebra':algebra,'tables':tables,'chains':chains,'composed_source_reproduced_exactly':True,'scope':'Finite identities and complete coefficient checks; no global theorem or independent-acceptance record.'}
    (ROOT/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
    print('All finite checks passed.',flush=True)
