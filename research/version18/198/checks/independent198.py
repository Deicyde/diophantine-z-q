"""Independent exact 204 -> affine200 -> inverse198 -> balanced198 audit.

Imports no package producer or checker. SymPy performs all substitutions,
field reductions and row-square expansions. The frozen package is read only.
"""
from pathlib import Path
from collections import defaultdict,Counter
from hashlib import sha256
from math import gcd,lcm
import json,sys
from portable_io import independent_paths, pinned_file
import sympy as s

PKG,PINS,ARCHIVE,OUTPUT=independent_paths()
CIR=PKG/'circuits'
FINAL=CIR/'inverse198'
source=PKG/'source/computation/quartic/reciprocal204_v27/unbalanced-quadratic.json'
x=(s.Symbol('parameter'),)+s.symbols('x1:229');rho=s.Symbol('rho')
rev={v:i for i,v in enumerate(x)}
checks=[]
def need(ok,message):
    if not ok:raise AssertionError(message)
    checks.append(message)
def read(p):return json.loads(p.read_text(encoding='utf-8'))
def decode(row,mp=None):
    out={}
    for t in row['terms']:
        a=int(t['parameterPower']);m=tuple(t['monomial'])
        need(tuple(sorted(m))==m,'canonical serialized monomial')
        if mp:m=tuple(sorted(mp[i] for i in m))
        need((a,m) not in out,'no duplicate serialized term')
        out[a,m]=s.Rational(t['coefficient'])
    return out
def expression(p):return s.Add(*(v*x[0]**a*s.Mul(*(x[i] for i in m)) for (a,m),v in p.items()))
def collect(expr):
    out={}
    for mon,c in s.expand(expr).as_coefficients_dict().items():
        if not c:continue
        powers=mon.as_powers_dict();a=int(powers.pop(x[0],0));ids=[]
        for v,k in powers.items():
            if v!=1:ids.extend([rev[v]]*int(k))
        out[a,tuple(sorted(ids))]=c
    return out
def primitive(expr):
    data=collect(expr);den=lcm(*(int(v.q) for v in data.values()));g=gcd(*(int(v*den) for v in data.values()))
    if data[min(data)]<0:g=-g
    return {k:v*den/g for k,v in data.items()}
def field(i):return x[i]+rho*x[i+1]
def half(i):return x[i]+2*rho*x[i+1]
def components(expr):
    p=s.rem(s.Poly(s.expand(expr),rho),s.Poly(rho*rho-2,rho))
    return p.nth(0),p.nth(1)
def sum_squares(rows):
    out=defaultdict(lambda:s.S.Zero)
    for row in rows:
        for k,v in collect(expression(row)**2).items():out[k]+=v
    return {k:v for k,v in out.items() if v}
def profiles(poly):
    out=defaultdict(dict)
    for (a,m),v in poly.items():out[m][a]=int(v)
    return out
def serialize_profiles(ps):return [{'monomial':list(m),'coefficients':{str(a):str(v) for a,v in p.items()}} for m,p in sorted(ps.items())]

pins=read(PINS)
zipfile=ARCHIVE
need(sha256(zipfile.read_bytes()).hexdigest()==pins['zip_sha256'],'selected archive hash')
for f in pins['files']:
    need(sha256(pinned_file(PKG,f['path']).read_bytes()).hexdigest()==f['sha256'],'frozen package hash '+f['path'])
need(sha256(source.read_bytes()).hexdigest()=='21da11b4a5c9f11d8a3253162283cbd339c0f35599ab9d578a2302009f725536','pinned 204 source hash')

parent=read(source);affine=read(CIR/'affine200/quadratic.json')
unbalanced=read(FINAL/'quadratic.json');balanced=read(FINAL/'balanced-quadratic.json')
need(unbalanced['fixedParameter']['symbol']=='A' and unbalanced['fixedParameter']['value']=='149^(2N+1)','unbalanced parameter convention')
need(balanced['fixedParameter']['symbol']=='C' and balanced['fixedParameter']['value']=='149^N','balanced parameter convention')
need(balanced['coordinates']==unbalanced['coordinates'],'balanced coordinate metadata and input order retained')
D=11-6*rho;R=x[118];R2=x[117]
S=field(19);TH=field(183)

# Independently transcribed affine odd-fourth-label step, in parent formal IDs.
f,h,g,k,sl=(field(i) for i in (205,207,209,211,213))
F,G=half(60),half(29)
L2,L3,L4,LP4=field(35),field(39),field(43),field(45)
changed={}
for rid,name,formula in [
        (2,'affine.Lucas.C',(L2-R)*L4-R*field(48)),
        (4,'affine.Lucas.AT',(L2+R)*L3-R*field(50)),
        (6,'affine.Lucas.F',L3*L3+field(48)**2-field(48)*field(50)-half(52))]:
    for offset,part in enumerate(components(formula)):changed[rid+offset]=(name+'.'+str(offset),part)
added_formulas=[('pair4.square.f',F-f*f),('pair4.square.g',G-g*g),
    ('pair4.curve',h*h-f+D*f*F),('pair4.secant',sl*(f-g)-h-k),
    ('pair4.tangent',sl*(h-k)-1+D*(F+f*g+G)),
    ('pair4.ratio.primary.raw',h*(L4-1)+4*f*S),
    ('pair4.ratio.primary.regular',(1-D*F)*(L4-1)+4*h*S),
    ('pair4.ratio.alternate.raw',k*(LP4-1)+4*g*TH),
    ('pair4.ratio.alternate.regular',(1-D*G)*(LP4-1)+4*k*TH)]
affine_expected=[]
for row in parent['residuals']:
    rid=row['id']
    if 122<=rid<=139:continue
    name,q=row['name'],expression(decode(row))
    if rid in changed:name,q=changed[rid]
    if rid==144:
        q=s.expand(q-(x[173]-x[175])**2-2*(x[174]-x[176])**2+4*components(sl*sl+D*(f+g))[0])
        name='affine.weighted.aggregate'
    affine_expected.append((name,primitive(q),rid))
for name,formula in added_formulas:
    for j,part in enumerate(components(formula)):affine_expected.append((name+'.'+str(j),primitive(part),None))
affine_ids=[*range(1,169),*range(183,215)]
amap={i:formal for i,formal in enumerate(affine_ids,1)}
need(len(affine_expected)==186,'affine 200 row count')
need(len(affine['coordinates'])==200,'affine 200 coordinate count')
for row,(name,data,rid) in zip(affine['residuals'],affine_expected):
    need(row['name']==name and decode(row,amap)==data,'independent affine row '+name)
apoly=sum_squares([decode(row) for row in affine['residuals']])
need(apoly==decode(read(CIR/'affine200/polynomial.json')),'independent affine expanded coefficients')

# Rescale each inherited row in SymPy's Laurent ring, retaining R2=R^2 separately.
weight_certificate=read(CIR/'inverse-vieta-rescaling-search.json')
w={int(i):int(e) for i,e in weight_certificate['weights'].items()}
fids=[1,*range(4,155),*range(183,229)]
fmap={i:formal for i,formal in enumerate(fids,1)}
compact={formal:i for i,formal in fmap.items()}
need(len(fids)==198 and len(set(fids))==198,'198 distinct coordinates including input')
need([co['id'] for co in unbalanced['coordinates']]==list(range(1,199)),'consecutive coordinate IDs')
need([co['formalId'] for co in unbalanced['coordinates']]==fids,'complete formal coordinate map')
for co in unbalanced['coordinates']:
    need(co['rescalingExponent']==w.get(co['formalId'],0),'coordinate Laurent exponent')
substitution={x[i]:x[i]*R**w.get(i,0) for i in fids if i not in (117,118)}
substitution[R2]=R*R
def rescale(expr):
    q=s.expand(expr.xreplace(substitution))
    least=min(int(mon.as_powers_dict().get(R,0)) for mon in q.as_coefficients_dict())
    q=s.expand(q*R**(-least));out=s.S.Zero
    for mon,c in q.as_coefficients_dict().items():
        powers=mon.as_powers_dict();e=int(powers.pop(R,0));need(e>=0,'nonnegative residual R power')
        term=c*R2**(e//2)*R**(e%2)
        for v,k in powers.items():term*=v**k
        out+=term
    return primitive(out),least

deleted_rows=set(range(104,122))|set(range(140,145))
expected=[]
for name,data,sourceid in affine_expected:
    if sourceid in deleted_rows:continue
    if name=='scalar.r_power_2.definition':q,power=data,0
    else:q,power=rescale(expression(data))
    expected.append((name,q,power))

# The ten physical scaled field equations are independent of the producer's unscaled chart.
u,v,z,m,r,p,r2=(field(i) for i in range(215,229,2))
physical=[('inverse_vieta.product',u*v-R2*p),('inverse_vieta.r',p*z-r),
    ('inverse_vieta.sum',r*(u+v+z+2*m)+D*R2),
    ('inverse_vieta.pair',R2*p+z*(u+v)-m*m),('inverse_vieta.r2',r2-r*r),
    ('inverse_vieta.fusquare',half(56)*r2-u*u),('inverse_vieta.fvsquare',half(25)*r2-v*v),
    ('inverse_vieta.primary',field(35)*(m+u)-2*R*S),
    ('inverse_vieta.alternate',field(37)*(m+v)+2*R*TH),
    ('inverse_vieta.scalar',field(107)*(m+z)+2*S)]
for name,formula in physical:
    for j,part in enumerate(components(formula)):expected.append((name+'.'+str(j),primitive(part),None))
aggregate=8*(x[4]-x[90])+56+4*x[225]
for fi,gi,si in [(185,189,193),(195,199,203),(205,209,213)]:
    aggregate+=4*components(field(si)**2+D*(field(fi)+field(gi)))[0]
expected.append(('inverse_vieta.unweighted.aggregate',primitive(aggregate),None))
need(len(expected)==184,'198 family has 184 rows')
for row,(name,data,power) in zip(unbalanced['residuals'],expected):
    need(row['name']==name and decode(row,fmap)==data,'independent inverse198 row '+name)
    if power is not None:need(row['dividedRPower']==power,'recorded R divisor '+name)

# A finite proof of the zero-stratum guard, before interpreting Laurent inverses.
X,Rs,contact=s.symbols('X R contact')
beta=51*X*X+2504;cache=(51*X*X+2501)**2/4
contact_expression=-14315517724-291790992*X*X-15531948*X*X*cache-767410608*cache+512*cache*cache
need(s.expand(contact_expression-beta*(beta-1)*(beta-2401)*(32*beta+343))==0,'positive four-contact polynomial identity')
rows_by_name={name:data for name,data,power in expected}
q=expression(rows_by_name['scalar.four_contact_product.definition'])
need(s.expand(q.subs({x[47]:X*X,x[105]:cache,x[106]:contact,R:Rs})-(Rs*contact-contact_expression))==0,'literal rescaled contact guard')
need(primitive(expression(rows_by_name['scalar.forced_prime.definition']))==primitive(1+22201*R*x[106]-x[0]*x[106]),'literal forced-prime normalization')

# Verify every balanced row directly from the exact stored integer weight list.
bw={int(i):int(e) for i,e in read(FINAL/'balancing-weights.json')['weights'].items()}
need(set(bw)==set(range(1,199)) and bw[1]==0,'balancing fixes the input and covers all coordinates')
balanced_expected=[]
for original,actual in zip(unbalanced['residuals'],balanced['residuals']):
    repl={x[0]:149*x[0]**2,**{x[i]:x[i]*x[0]**bw[i] for i in range(1,199)}}
    raw=s.expand(expression(decode(original)).xreplace(repl))
    least=min(int(mon.as_powers_dict().get(x[0],0)) for mon in raw.as_coefficients_dict())
    data=primitive(s.expand(raw*x[0]**(-least)))
    need(data==decode(actual),'independent balanced row '+original['name'])
    need(actual['dividedCPower']==least,'recorded C divisor')
    need(max(a for a,m in data)<=1,'balanced row parameter degree')
    balanced_expected.append(data)

K=31581660**28;J=5898050446009651968;H=(J*K)**2
statistics={};allpoly={};allprofiles={}
for label,table,filename in [('unbalanced',unbalanced,'polynomial.json'),('balanced',balanced,'balanced-polynomial.json')]:
    need(table['inputCoordinate']==1 and table['variables']==198,'input included, fixed variable count')
    need(table['fixedParameter']['quantified'] is False,'coefficient parameter not quantified')
    rows=[decode(row) for row in table['residuals']]
    for data in rows:
        need(max(len(m) for a,m in data)==2,'every residual has exact coordinate degree two')
        need(all(v.q==1 for v in data.values()),'integral row coefficients')
        need(gcd(*(int(v) for v in data.values()))==1,'formally primitive coefficient row')
        if label=='unbalanced':
            need(len({m for a,m in data})==len(data),'unbalanced residual has no mixed parameter profile')
            need(gcd(*(int(v)*149**(3*a) for (a,m),v in data.items()))==1,'unbalanced rows primitive at every allowed parameter')
    polynomial=sum_squares(rows);stored=decode(read(FINAL/filename))
    need(polynomial==stored,'independent full '+label+' expansion')
    need({i for a,m in polynomial for i in m}==set(range(1,199)),'all 198 coordinates occur')
    need(max(len(m) for a,m in polynomial)==4,'exact total degree four')
    need(polynomial.get((0,(1,1,1,1)))==1,'parameter-independent coefficient of input X^4 is one')
    ps=profiles(polynomial)
    need(ps[(1,1,1,1)]=={0:1},'fixed-member content one witness')
    statistics[label]={'variables_including_input':198,'existential_variables':197,'quadratic_rows':184,
        'degree':4,'integer_content_for_every_member':1,'coordinate_profiles':len(ps),
        'parameter_separated_terms':len(polynomial),'profile_types':{str(k):v for k,v in Counter(tuple(sorted(p)) for p in ps.values()).items()},
        'unit_coefficient_monomial':[1,1,1,1]}
    allpoly[label]=polynomial;allprofiles[label]=ps

ups=allprofiles['unbalanced'];bps=allprofiles['balanced']
need(len(ups)==2945 and len(allpoly['unbalanced'])==2945,'unbalanced exact support')
need(all(len(p)==1 for p in ups.values()),'unbalanced support cannot cancel for nonzero A')
parameter_part={m:p for m,p in ups.items() if any(p)}
need(parameter_part=={(104,):{1:-2},(104,104,116):{1:-44402},(104,104):{2:1}},'complete polynomial-in-A part')
need(max(abs(p.get(0,0)) for p in ups.values())==H,'unbalanced constant height attained')
need(44402<=149**3,'unbalanced linear coefficients bounded by A^2 for allowed A')
need(149**210<H<=149**214,'unbalanced height crossover exactly 53')
statistics['unbalanced'].update(parameter='A=149^(2N+1), N>=1',exact_height='max(H0,A^2)',height_crossover_N=53,
    coefficient_formula='P0(x)-2*A*x104-44402*A*x104^2*x116+A^2*x104^2')
need(len(bps)==2945 and len(allpoly['balanced'])==2959,'balanced profile and separated term counts')
opposite={}
for mon,pf in bps.items():
    if set(pf)=={1}:need(pf[1]**2<=H*K,'linear height envelope')
    else:
        need(set(pf)<={0,2},'allowed balanced profile degrees')
        need(abs(pf.get(0,0))*K+abs(pf.get(2,0))*H<=H*K,'constant/quadratic height envelope')
        if pf.get(0,0)*pf.get(2,0)<0:
            need(pf[0]%2==0 and pf[2]%2==1,'opposite-sign profile nonzero for odd C')
            opposite[mon]=pf
need(any(p=={0:H} for p in bps.values()) and any(p=={2:K} for p in bps.values()),'both balanced height branches attained')
need(K*149**112<H<=K*149**114,'balanced crossover exactly 57')
need(len(str(H))==458,'constant maximum has 458 decimal digits')
need(bps[(6,6,87,115)]=={1:-2},'balanced polynomial requires C, not polynomial-in-A convention')
statistics['balanced'].update(parameter='C=149^N, N>=1; A=149*C^2',exact_height='max(H0,K0*C^2)',height_crossover_N=57,
    opposite_sign_profiles=len(opposite),support_fixed_for_every_allowed_N=True,
    linear_C_profiles=685,not_polynomial_in_A_example={'monomial':[6,6,87,115],'coefficient':'-2C'})

# Formal row primitivity and primitivity after specialization are different.
specialized_nonprimitive=[]
for row in balanced['residuals']:
    data=decode(row);monomials=[m for a,m in data]
    need(len(set(monomials))==len(monomials),'no mixed parameter profile within a residual')
    g=gcd(*(int(v)*149**a for (a,m),v in data.items()))
    if g!=1:
        need(row['id']==54 and g==149,'only balanced row 54 has specialized nonunit content')
        constants=[abs(int(v)) for (a,m),v in data.items() if a==0]
        need(len(constants)==1 and constants[0]%149==0 and constants[0]%(149*149)!=0,'row 54 has exact 149-adic content one')
        specialized_nonprimitive.append({'row_id':54,'name':row['name'],'content_for_every_N_ge_1':149})
need(len(specialized_nonprimitive)==1,'complete specialized row-content census')

# Regression checks compare actual independent specifications, not saved receipts.
bad=dict(allpoly['balanced']);bad[0,(1,1,1,1)]+=1
need(bad!=decode(read(FINAL/'balanced-polynomial.json')),'coefficient corruption rejected')
wrong_scalar=field(107)*(m+z)+S
need(primitive(components(wrong_scalar)[0])!=expected[-3][1],'missing scalar factor two rejected')

report={'status':'PASS','archive_sha256':pins['zip_sha256'],'authenticated_package_files':len(pins['files']),
    'python':sys.version,'sympy':s.__version__,'statistics':statistics,
    'H0':'(5898050446009651968*31581660^28)^2','K0':'31581660^28','H0_decimal_digits':458,
    'balanced_opposite_sign_profiles':serialize_profiles(opposite),'specialized_nonprimitive_rows':specialized_nonprimitive,
    'row_checks':{'204_to_affine200':186,'affine200_to_inverse198':184,'inverse198_to_balanced198':184},
    'all_expanded_tables_checked':['affine200/polynomial.json','inverse198/polynomial.json','inverse198/balanced-polynomial.json'],
    'files':{n:sha256((FINAL/n).read_bytes()).hexdigest() for n in ['quadratic.json','polynomial.json','balanced-quadratic.json','balanced-polynomial.json','balancing-weights.json']},
    'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'assertions':len(checks),
    'scope':'Exact finite algebra and coefficient specification only. No audit of inherited infinite arithmetic or Busy Beaver theorems.'}
OUTPUT.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in report.items() if k!='balanced_opposite_sign_profiles'},indent=2))
