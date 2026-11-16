"""Independent exact 198 -> 196 audit. Reads data only; no upstream imports."""
import json, hashlib, re, copy
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
from math import gcd

HERE=Path(__file__).resolve().parent
ROOT=HERE/'source'
D=ROOT/'computation/quartic/laurent_recovery_v38'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
def need(ok, msg):
    if not ok: raise AssertionError(msg)
    checks.append(msg)
def clean(p): return {k:v for k,v in p.items() if v}
def decode(row, remap=None):
    p={}
    for t in row['terms']:
        a=int(t['parameterPower']); ids=t['monomial']
        need(ids==sorted(ids), 'canonical term')
        m=tuple(sorted(remap[i] if remap else i for i in ids))
        k=(a,m); need(k not in p, 'no repeated term')
        p[k]=F(t['coefficient']); need(bool(p[k]),'nonzero term')
    return p
def square_sum(rows):
    out=defaultdict(F)
    for row in rows:
        terms=list(decode(row).items())
        for (a,m),v in terms:
            for (b,n),w in terms: out[a+b,tuple(sorted(m+n))]+=v*w
    return clean(out)

parent_file=ROOT/'sources/h10_quartic198/circuits/inverse198/quadratic.json'
local=HERE.parent/'v18-198-dependency-inventory-20261114/package/H10-quartic198/circuits/inverse198/quadratic.json'
need(parent_file.read_bytes()==local.read_bytes(),'parent is byte-identical to frozen audited Conant table')
need(digest(parent_file)=='c55d7eefe41f62fee88b467e3ea8f6be8ba1e66f6a94b30eb74b39f6f6e7efad','parent hash')
old=read(parent_file); new=read(D/'family196/quadratic.json'); cfg=read(D/'config196.json'); cert=read(D/'family196/certificate.json')
names={x['name']:x['id'] for x in old['coordinates']}

# Transcribe the paper's maps independently by semantic coordinate names.
weights={}; constants={}; powers={}
for j in (0,1):
    def power(k): return (0,k,0) if j==0 else (0,0,k)
    for suffix,k in [('normalized.s',-1),('factored.v',-1),('normalized.p',1),('normalized.p2.quadratic',2),('actualW.0',-2),('actualW.1',-2),('normOver2w0',-2),('B',-2)]:
        weights[names[f'detector{j}.'+suffix]]=power(k)
    for name,i in names.items():
        mat=re.fullmatch(r'amplified\.det'+str(j)+r'\.(factor[0-4]|product[1-3])\.[01]',name)
        if mat:
            rp=j if mat[1].startswith('factor') else (0 if mat[1]=='product1' else -j)
            weights[i]=(rp,*power(-2)[1:])
    for suffix,k in [('q1',-1),('inverseWeight',1),('inverseWeightSquared',2),('inverseWeightFourthPower',4)]:
        powers[names[f'detector{j}.'+suffix]]=power(k)
powers[names['detector1.inverseWeightFourthPower']]=(-1,0,4)
powers[names['scalar.forced_positive_parameter']]=(1,0,0)
powers[names['scalar.r_power_2']]=(2,0,0)
H=31581660**14; K=82479248*H
for name,c in [('scalar.W2.quadratic.rescaled',F(1,H)),('scalar.b.quadratic',F(-1,K)),('normalized_scalar.scaled_e',-K),('normalized_scalar.s',K),('normalized_scalar.p',K),('normalized_scalar.factored.q',K),('normalized_scalar.p2.quadratic',K*K),('normalized_scalar.factored.q2',K*K),('normalized_scalar.factored.v',-1)]: constants[names[name]]=F(c)
need(weights=={int(i):tuple(w) for i,w in cfg['weights'].items()},'all paper coordinate weights match config')
need(powers=={int(i):tuple(w) for i,w in cfg['powers'].items()},'all paper retained and deleted power formulas match config')
need(constants=={int(i):F(c) for i,c in cfg['constants'].items()},'all nine paper constant scalings match config')
need(not(set(powers)&set(weights)) and not(set(powers)&set(constants)),'base units and power coordinates are fixed')
need(1 not in powers and 1 not in weights and 1 not in constants,'input coordinate fixed')
removed={80,95}; retained=[i for i in range(1,199) if i not in removed]
to_old={i:oldid for i,oldid in enumerate(retained,1)}
need(new['variables']==196 and len(new['coordinates'])==196,'196 coordinates including input')
for x in new['coordinates']:
    need(x['parent_id']==to_old[x['id']] and x['name']==old['coordinates'][x['parent_id']-1]['name'],'ordered coordinate map')
need({int(k):v for k,v in cert['old_to_new'].items()}=={v:k for k,v in to_old.items()},'certificate coordinate map exact')

def laurent(row, source):
    out=defaultdict(F)
    for (a,mon),c in decode(row,None if source else to_old).items():
        es=[0,0,0]; rest=[]
        for i in mon:
            if source: c*=constants.get(i,F(1))
            if i in powers: w=powers[i]
            else:
                rest.append(i); w=weights.get(i,(0,0,0)) if source else (0,0,0)
            es=[x+y for x,y in zip(es,w)]
        out[(a,tuple(rest),*es)]+=c
    return clean(out)

deleted_names=['detector0.inverseWeightFourthPower.definition','detector1.inverseWeightFourthPower.definition']
old_rows=[r for r in old['residuals'] if r['name'] not in deleted_names]
need(len(old_rows)==len(new['residuals'])==182,'182 rows with only two deletions')
guard_names=['inputSquare.definition','scalar.rPair1.definition','scalar.four_contact_product.definition','scalar.forced_prime.definition','scalar.r_power_2.definition','detector0.inverseWeight.definition','detector0.inverseWeightSquared.definition','detector1.inverseWeight.definition','detector1.inverseWeightSquared.definition']
for r in old['residuals']:
    if r['name'] in deleted_names: need(laurent(r,True)=={},'deleted row is an identity: '+r['name'])
row_results=[]
def check_row(a,b,c):
    need(a['name']==b['name'],'retained row ordering')
    left=laurent(a,True); right=laurent(b,False)
    shift=c['division_exponents']; multiplier=F(c['primitive_multiplier'])
    rhs={(k[0],k[1],*(x+y for x,y in zip(k[2:],shift))):v/multiplier for k,v in right.items()}
    need(left==rhs,'exact Laurent identity: '+a['name'])
for a,b,c in zip(old_rows,new['residuals'],cert['rows']):
    need((c['source_row'],c['target_row'])==(a['id'],b['id']),'row certificate coverage')
    check_row(a,b,c)
    need(max(len(t['monomial']) for t in b['terms'])<=2,'quadratic row')
    need(all(F(t['coefficient']).denominator==1 for t in b['terms']),'integer row')
    need(gcd(*(int(t['coefficient']) for t in b['terms']))==1,'primitive row')
    if a['name'] in guard_names: need(decode(a)==decode(b,to_old),'guard is literally retained: '+a['name'])
    row_results.append({'old':a['id'],'new':b['id'],'name':a['name'],'verified':True})

# Check the actual scalar and power guard formulas, not just their preservation.
by_name={r['name']:decode(r) for r in old['residuals']}
def form(terms): return {(a,tuple(sorted(m))):F(c) for a,m,c in terms}
literal={
 'inputSquare.definition':[(0,[1,1],1),(0,[45],-1)],
 'scalar.rPair1.definition':[(0,[],6255001),(0,[45],255102),(0,[45,45],2601),(0,[103],-4)],
 'scalar.four_contact_product.definition':[(0,[],14315517724),(0,[45],291790992),(0,[45,103],15531948),(0,[103],767410608),(0,[103,103],-512),(0,[104,116],1)],
 'scalar.forced_prime.definition':[(0,[],1),(0,[104,116],22201),(1,[104],-1)],
 'scalar.r_power_2.definition':[(0,[115],1),(0,[116,116],-1)],
 'detector0.inverseWeight.definition':[(0,[],1),(0,[77,78],-1)],
 'detector0.inverseWeightSquared.definition':[(0,[78,78],1),(0,[79],-1)],
 'detector1.inverseWeight.definition':[(0,[],1),(0,[92,93],-1)],
 'detector1.inverseWeightSquared.definition':[(0,[93,93],1),(0,[94],-1)]}
for name,terms in literal.items():need(by_name[name]==form(terms),'literal nonvanishing or power formula: '+name)
def add(*ps):
    o=defaultdict(F)
    for p in ps:
        for k,v in p.items():o[k]+=v
    return clean(o)
def mul(p,q):
    o=defaultdict(F)
    for i,a in p.items():
        for j,b in q.items():o[i+j]+=a*b
    return clean(o)
def scale(p,c):return {k:v*c for k,v in p.items()}
v={0:F(6255001,4),1:F(255102,4),2:F(2601,4)}
r=add({0:-14315517724,1:-291790992},scale(mul({1:1},v),-15531948),scale(v,-767410608),scale(mul(v,v),512))
prod={0:1}
for aa,bb in [(51,103),(51,2503),(51,2504),(1632,80471)]:prod=mul(prod,{1:aa,0:bb})
need(r==prod,'RJ equals four strictly positive factors at u=X^2')

def verify_polynomial(table,filename):
    p=square_sum(table['residuals']); delivered=read(D/'family196'/filename)
    need(p==decode(delivered),'all expanded coefficients match '+filename)
    need({i for a,m in p for i in m}==set(range(1,197)),'every coordinate occurs '+filename)
    need(max(len(m) for a,m in p)==4,'exact degree four '+filename)
    need(p[(0,(1,1,1,1))]==1,'coefficient of input fourth power is one '+filename)
    ps=defaultdict(dict)
    for (a,m),v in p.items():ps[m][a]=int(v)
    need(len(ps)==2943,'2943 coordinate monomials '+filename)
    return p,ps
up,ups=verify_polynomial(new,'polynomial.json')
need({k:int(v) for k,v in up.items() if k[0]}=={(1,(102,)):-2,(1,(102,102,114)):-44402,(2,(102,102)):1},'three exact A-dependent terms')
need(all(len(x)==1 for x in ups.values()),'unbalanced profiles pure powers, no cancellation')
fixed=max(abs(v) for (a,m),v in up.items() if a==0)
need(fixed==484991541504995159662206970923766531374664106904986910720,'unbalanced fixed maximum')
need(149**26<fixed<149**27,'coefficient crossover at N=7')
need(149**3>44402,'A squared dominates all linear coefficients for every N>=1')

bal=read(D/'family196/balanced-quadratic.json'); bc=read(D/'family196/balancing.json')
need(bal['coordinates']==new['coordinates'] and len(bal['residuals'])==182,'balanced coordinate and row coverage')
for a,b,c in zip(new['residuals'],bal['residuals'],bc['rows']):
    o=defaultdict(F)
    for (e,m),v in decode(a).items():o[2*e+sum(bc['weights'][str(i)] for i in m)-c['division_power'],m]+=v*149**e*F(c['primitive_multiplier'])
    need(clean(o)==decode(b),'exact balanced row identity '+a['name'])
bp,bps=verify_polynomial(bal,'balanced-polynomial.json')
KB=11903780636513165769654680680436132271178681610029854792
need(any(p=={2:KB} or p=={2:-KB} for p in bps.values()),'balanced exact maximum attained')
for p in bps.values():
    need(max(p)<=2,'balanced parameter degree at most two')
    need(sum(abs(v)*149**a for a,v in p.items())<=KB*149**2,'balanced height upper bound at 149, hence all larger C')
    top=max(p)
    need(abs(p[top])*149**top>sum(abs(v)*149**a for a,v in p.items() if a<top),'balanced profile never vanishes for C>=149')

# Mutations of equations and certificates must be rejected by the same identities.
negatives=[]
for kind in ['coefficient','division_shift','primitive_multiplier']:
    a,b,c=copy.deepcopy((old_rows[50],new['residuals'][50],cert['rows'][50]))
    if kind=='coefficient':b['terms'][0]['coefficient']=str(F(b['terms'][0]['coefficient'])+1)
    elif kind=='division_shift':c['division_exponents'][0]+=1
    else:c['primitive_multiplier']=str(F(c['primitive_multiplier'])*2)
    try:check_row(a,b,c)
    except AssertionError:negatives.append(kind)
    else:raise AssertionError('corruption accepted: '+kind)
result={'commit':'5c35db3253a70b0875acec4b451cdaac4da3c8fd','status':'PASS','independent_checks':len(checks),'variables':196,'existential_variables':195,'rows':182,'monomials':2943,'degree':4,'content':1,'unbalanced_fixed_maximum':str(fixed),'unbalanced_height':'max(K_fixed,149^(4N+2))','coefficient_crossover_N':7,'balanced_height':'11903780636513165769654680680436132271178681610029854792 * 149^(2N)','corruption_controls_rejected':negatives,'row_identities':row_results,'inputs':{str(p.relative_to(ROOT)):digest(p) for p in [parent_file,D/'config196.json',D/'family196/quadratic.json',D/'family196/polynomial.json',D/'family196/balanced-quadratic.json',D/'family196/balanced-polynomial.json',D/'family196/certificate.json',D/'family196/balancing.json']},'scope':'Exact all-solution algebraic equivalence and coefficient audit; inherited 198 arithmetic premises not independently re-proved here.'}
(HERE/'RESULT.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k not in ['row_identities','inputs']},indent=2))
