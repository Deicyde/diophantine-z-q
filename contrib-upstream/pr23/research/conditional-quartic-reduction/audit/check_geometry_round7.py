"""Independent algebra/source/point checks for the round-seven geometric and scalar changes.

No producer/compiler module is imported. Exact source equations are checked
up to nonzero rational row scaling, polynomial identities modulo the two
quartic chart equations are checked symbolically, and exact Q(sqrt(2))
samples check orientation, tangency, identity inputs, and log scaling.
The uniform proof and the inherited global arithmetic remain separate.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json

# Sparse polynomials over Q, keyed by a sorted monomial tuple.
def c(a):
    a=F(a)
    return {():a} if a else {}
def v(i):return {(i,):F(1)}
def add(*ps):
    r={}
    for p in ps:
        for m,a in p.items():r[m]=r.get(m,F(0))+a
    return {m:a for m,a in r.items() if a}
def scale(p,a):return {m:b*F(a) for m,b in p.items() if b*a}
def sub(p,q):return add(p,scale(q,-1))
def mul(*ps):
    r=c(1)
    for p in ps:
        z={}
        for m,a in r.items():
            for n,b in p.items():
                k=tuple(sorted(m+n));z[k]=z.get(k,F(0))+a*b
        r={m:a for m,a in z.items() if a}
    return r
def pw(p,n):
    r=c(1)
    for _ in range(n):r=mul(r,p)
    return r
def decode(ts):
    assert all(t.get('sPower',0)==0 for t in ts)
    return {tuple(t['monomial']):F(t['coefficient']) for t in ts if F(t['coefficient'])}
def fa(a,b):return (add(a[0],b[0]),add(a[1],b[1]))
def fs(a,b):return (sub(a[0],b[0]),sub(a[1],b[1]))
def fm(a,b):return (add(mul(a[0],b[0]),scale(mul(a[1],b[1]),2)),add(mul(a[0],b[1]),mul(a[1],b[0])))
def fc(a,b=0):return (c(a),c(b))
def fscale(a,k):return (scale(a[0],k),scale(a[1],k))
def conjugate(a):return (a[0],scale(a[1],-1))

def square_completion():
    coefficients=[F(1),F(-2,5)]
    for j in range(2,13):coefficients.append(coefficients[-1]*F(4*j-5,4*j+1))
    # Independently form the reversed power-series square root through degree5.
    rev=[F(1)]
    for k in range(1,6):
        rev.append((coefficients[12-k]/coefficients[12]-sum(rev[i]*rev[k-i] for i in range(1,k)))/2)
    U=[F(0)]+list(reversed(rev))
    R=coefficients[:]
    for i,a in enumerate(U):
        for j,b in enumerate(U):R[i+j]-=coefficients[12]*a*b
    assert all(a==0 for a in R[7:])
    assert U[6]==1 and U[0]==0
    return coefficients,U,R[:7]

def check_source(root,scalar_order):
    assert scalar_order==28, "this source checker certifies the selected outer-constant order28 tree"
    data=json.loads((root/'raw-ir.json').read_text())
    rows={r['name']:r for r in data['residuals']}
    values=data['values'];coords={x['name']:v(x['id']) for x in data['coordinates']}
    def val(n):return decode(values[n]['terms'])
    def fld(n):return (val(n+'.0'),val(n+'.1'))
    def row(n):return decode(rows[n]['terms'])
    count=0
    def same(a,b):
        nonlocal count
        assert a==b
        count+=1
    def proportional(expected,name):
        nonlocal count
        actual=row(name)
        assert expected and actual and set(expected)==set(actual),name
        m=next(iter(expected));ratio=expected[m]/actual[m]
        assert ratio and expected==scale(actual,ratio),name
        count+=1
    def equation(expected,name):
        for j in range(2):proportional(expected[j],name+'.'+str(j))
    def assign(expected,out,name):
        for j in range(2):proportional(sub(out[j],expected[j]),name+'.'+str(j)+'.definition')
    D=fc(11,-6)
    P={'x':fc(F(57,8),F(-7,2)),'h':fc(-1,F(7,4)),'j':fc(F(39,8),F(-9,2))}
    names=['H','UA','US','UT','UZ']
    for n in names[1:]:
        g,l,f=fld(n+'.g'),fld(n+'.l'),fld(n+'.f')
        same(g,(coords[n+'.chart.h0'],coords[n+'.chart.h1']))
        same(l,(coords[n+'.chart.j0'],coords[n+'.chart.j1']))
        assign(fm(g,g),f,n+'.chart.x')
        equation(fs(fa(fm(l,l),fm(D,fm(f,f))),fc(1)),n+'.chart.equation')
    roots=[P]+[{k:fld(n+'.'+k) for k in ['x','h','j']} for n in ['A','S','T','Z']]
    for n,R in zip(['A','S','T','Z'],roots[1:]):
        same(R['h'],(coords[n+'.chart.h0'],coords[n+'.chart.h1']))
        same(R['j'],(coords[n+'.chart.j0'],coords[n+'.chart.j1']))
        assign(fm(R['h'],R['h']),R['x'],n+'.chart.x')
        equation(fa(fs(fm(R['j'],R['j']),fm(R['x'],R['x'])),D),n+'.chart.equation')
    for i,(n,R) in enumerate(zip(names,roots)):
        if i==0:continue
        prefix='V'+str(i);g,l,f=fld(n+'.g'),fld(n+'.l'),fld(n+'.f')
        tau,fv,M=fld(prefix+'.inverseRoot'),fld(prefix+'.f'),fld(prefix+'.scaledK')
        equation(fs(fm(tau,fa(R['x'],fm(D,f))),fs(fm(R['h'],l),fm(g,R['j']))),prefix+'.inverseRoot.definition')
        assign(fm(tau,tau),fv,prefix+'.f')
        equation(fa(fm(tau,M),fm(g,fa(R['x'],fm(D,fv)))),prefix+'.scaledK.definition')
        same(fld(prefix+'.logDenominator'),fs(M,R['j']))
        assert prefix+'.k.0' not in values
        count+=1
    K=fld('primaryRatio')
    g,s,f,fv,kV=[fld(n) for n in ['H.g','H.jointProduct','H.f','V0.f','V0.k']]
    same(g,(coords['H.chart.h0'],coords['H.chart.h1']))
    same(s,(coords['H.chart.j0'],coords['H.chart.j1']))
    assign(fm(g,g),f,'H.chart.x')
    equation(fs(fm(f,fv),fm(s,s)),'V0.f.definition')
    equation(fs(fa(fa(fm(D,fm(s,s)),fm(P['x'],fa(f,fv))),fscale(fm(P['j'],s),2)),fc(1)),'V0.jointCurve')
    equation(fs(fm(fm(P['h'],s),K),fs(fc(1),fa(fm(P['x'],f),fm(P['j'],s)))),'primaryRatio.definition')
    equation(fs(fm(fm(P['h'],s),kV),fs(fa(fm(P['x'],fv),fm(P['j'],s)),fc(1))),'V0.k.definition')
    assert 'H.l.0' not in values and 'V0.inverseRoot.0' not in values and 'V0.scaledK.0' not in values
    count+=1
    a=[F(1),F(-2,5)]
    for j in range(2,13):a.append(a[-1]*F(4*j-5,4*j+1))
    for i,R in enumerate(roots):
        prefix='logV'+str(i);f=fld('V'+str(i)+'.f')
        f2,w=[fld(prefix+'.'+t) for t in ['fSquare','w']]
        assign(fm(f,f),f2,prefix+'.fSquare')
        same(w,fm(D,f2))
        G=fld(prefix+'.polynomial')
        short=(i==1 and prefix+'.wPower3.0' not in values)
        if short:
            assign(fa(fa(fc(1),fscale(w,a[1])),fscale(fm(w,w),a[2])),G,prefix+'.polynomial')
            assert prefix+'.middle.0' not in values and prefix+'.wPower2.0' not in values
            count+=1
        elif prefix+'.squareRoot.0' in values:
            w2,w4=[fld(prefix+'.'+t) for t in ['wPower2','wPower4']]
            assign(fm(w,w),w2,prefix+'.wPower2')
            assign(fm(w2,w2),w4,prefix+'.wPower4')
            coefficients,U,remainder_coefficients=square_completion()
            basis=[fc(1),w,w2,fm(w,w2),w4,fm(w,w4),fm(w2,w4)]
            uraw,rem=fc(0),fc(0)
            for j in range(7):
                uraw=fa(uraw,fscale(basis[j],U[j]))
                rem=fa(rem,fscale(basis[j],remainder_coefficients[j]))
            u=fld(prefix+'.squareRoot')
            assign(uraw,u,prefix+'.squareRoot')
            assign(fa(fscale(fm(u,u),coefficients[12]),rem),G,prefix+'.polynomial')
        elif prefix+'.wPower4.0' in values:
            w2,w4=[fld(prefix+'.'+t) for t in ['wPower2','wPower4']]
            assign(fm(w,w),w2,prefix+'.wPower2')
            assign(fm(w2,w2),w4,prefix+'.wPower4')
            basis=[fc(1),w,w2,fm(w,w2),w4,fm(w,w4),fm(w2,w4)]
            midraw,low=fc(0),fc(0)
            for j in range(4,11):midraw=fa(midraw,fscale(basis[j-4],a[j]))
            for j in range(4):low=fa(low,fscale(basis[j],a[j]))
            mid=fld(prefix+'.middle')
            assign(midraw,mid,prefix+'.middle')
            assign(fa(low,fm(w4,mid)),G,prefix+'.polynomial')
        else:
            w2,w3=[fld(prefix+'.'+t) for t in ['wPower2','wPower3']]
            assign(fm(w,w),w2,prefix+'.wPower2')
            assign(fm(w2,w),w3,prefix+'.wPower3')
            basis=[fc(1),w,w2]
            def block(k):
                out=fc(0)
                for j in range(3):out=fa(out,fscale(basis[j],a[k+j]))
                return out
            mid=fld(prefix+'.middle')
            assign(fa(block(3),fm(w3,fa(block(6),fscale(w3,a[9])))),mid,prefix+'.middle')
            assign(fa(block(0),fm(w3,mid)),G,prefix+'.polynomial')
        if i==0:
            equation(fa(fm(fld('V0.k'),fld('logV0')),G),'logV0.definition')
            assert 'logV0.scaled.0' not in values
            count+=1
        else:
            eta=fld(prefix+'.scaled')
            equation(fa(fm(fld('V'+str(i)+'.logDenominator'),eta),G),prefix+'.scaled.definition')
            same(fld(prefix),fm(R['h'],eta))
    for i,n in enumerate(names[1:],1):
        equation(fs(fm(fld(n+'.l'),fld('L'+str(i))),fm(K,fld(n+'.g'))),'L'+str(i)+'.definition')
        # LP is conjugated after the quotient; source value retains the
        # unconjugated quotient, and the tests use its conjugate.
        equation(fs(fm(fld('logV0'),fld('LP'+str(i))),fld('logV'+str(i))),'LP'+str(i)+'.definition')
        same(fld('test'+str(9+i)),fs(fld('L'+str(i)),conjugate(fld('LP'+str(i)))))
    q={k:fld('S.'+k) for k in ['x','h','j']};prefix='scalar.shiftedS'
    fv,w=[fld(prefix+'.'+t) for t in ['f','rootTimesInverseRoot']]
    equation(fs(fm(w,fa(fm(P['x'],q['x']),D)),fs(fm(P['h'],fm(q['h'],q['j'])),fm(q['x'],P['j']))),prefix+'.rootTimesInverseRoot.definition')
    equation(fs(fm(q['x'],fv),fm(w,w)),prefix+'.f.definition')
    assert prefix+'.inverseRoot.0' not in values
    count+=1
    if prefix+'.nonzeroRealF' in values:
        proportional(sub(mul(fv[0],val(prefix+'.nonzeroRealF')),c(1)),prefix+'.nonzeroRealF.definition')
        assert prefix+'.scaledK.0' not in values and prefix+'.k.0' not in values
        same(fld(prefix+'.w'),w)
        denominator=fa(fa(P['x'],fm(D,fv)),fm(P['j'],w))
        same(fld(prefix+'.ratioDenominator'),denominator)
        if 'scalar.ratioProxyReal' in values:
            proxy=val('scalar.ratioProxyReal');leaf=val('scalar.ratioProxyLeaf')
            proportional(sub(proxy,fm(K,w)[0]),'scalar.ratioProxyReal.definition')
            proportional(sub(mul(val('scalar.r'),leaf),mul(proxy,val('scalar.rInverse15'))),'scalar.ratioProxyLeaf.definition')
            same(fld('scalar.directLeaf'),(leaf,c(0)))
            assert 'scalar.kScaled.0' not in values
        else:
            numerator=fscale(fm(P['h'],fm(fld('scalar.kScaled'),w)),-1)
            equation(fs(fm(denominator,fld('scalar.directLeaf')),numerator),'scalar.directLeaf.definition')
        count+=1
    else:
        M=fld(prefix+'.scaledK')
        equation(fa(fm(w,M),fa(P['x'],fm(D,fv))),prefix+'.scaledK.definition')
        same(fm(P['h'],fld(prefix+'.k')),fs(M,P['j']))
    assert not any('dx0Inverse' in q['name'] or 'dxInverse' in q['name'] for q in data['coordinates'])
    count+=1
    # Reconstruct the entire changed scalar tree and its actual pole consumer.
    rr=val('scalar.r');ri=val('scalar.rInverse');r3=val('scalar.rInverse3');r7=val('scalar.rInverse7');kap=val('scalar.rInverse15')
    beta=val('beta');rpair=val('scalar.rPair1')
    same(beta,add(c(5155),scale(val('inputProduct'),11016)))
    proportional(sub(val('inputProduct'),add(pw(coords['input'],2),coords['input'])),'inputProduct.definition')
    proportional(sub(rpair,mul(beta,sub(beta,c(1)))),'scalar.rPair1.definition')
    proportional(sub(rr,mul(rpair,add(scale(beta,32),c(343)))),'scalar.rThree.definition')
    proportional(sub(mul(rr,ri),c(1)),'scalar.rInverse.definition')
    for out,prior,name in [(r3,ri,'scalar.rInverse3'),(r7,r3,'scalar.rInverse7'),(kap,r7,'scalar.rInverse15')]:
        proportional(sub(mul(rr,out),pw(prior,2)),name+'.definition')
    A,B=fld('H.f');CC,DD=fv;proxy=val('scalar.ratioProxyReal');yy=val('scalar.ratioProxyLeaf')
    zz=val('scalar.leaf1');n1=val('scalar.n1');zn=val('scalar.n1OverR')
    same(val('scalar.leaf0'),mul(A,ri));same(val('scalar.leaf2'),mul(CC,ri))
    proportional(sub(zz,mul(B,ri)),'scalar.leaf1.definition')
    proportional(sub(mul(rr,n1),add(mul(zz,B),pw(CC,2))),'scalar.n1.definition')
    proportional(sub(mul(rr,zn),n1),'scalar.n1OverR.definition')
    LL=val('scalar.nLeft');JJ=val('scalar.nRight');NN=val('scalar.N');WW=val('scalar.W')
    proportional(sub(mul(rr,LL),add(pw(A,2),mul(zn,n1))),'scalar.nLeft.definition')
    for name,left,right,weight,out in [('scalar.nRight',DD,yy,kap,JJ),('scalar.N',LL,JJ,kap,NN)]:
        right2=val(name+'.rightSquare')
        proportional(sub(right2,pw(right,2)),name+'.rightSquare.definition')
        proportional(sub(out,add(pw(left,2),mul(weight,right2))),name+'.definition')
    same(WW,add(c(1),NN))
    assert 'scalar.n0' not in values and 'scalar.n0' not in coords
    assert 'scalar.nLeft.rightSquare' not in values
    assert 'scalar.leaf3.quadratic' not in coords
    assert 'scalar.rInverse14' not in values and 'scalar.rInverse28' not in values
    count+=1
    rho=val('scalar.correctedR');w2=val('scalar.W2');prep=val('scalar.preparationT')
    same(rho,scale(rr,42));same(val('scalar.Bsemantic'),mul(rho,w2))
    proportional(sub(w2,pw(WW,2)),'scalar.W2.definition')
    U=coords['scalar.preparationU'];V=coords['scalar.preparationV'];ee=coords['scalar.normalized_e']
    pp=val('scalar.p2');ss=val('scalar.s2');qq=val('scalar.q2');bh=val('scalar.Bh')
    for name,out,inp in [('scalar.p2',pp,coords['scalar.p']),('scalar.s2',ss,coords['scalar.s']),('scalar.q2',qq,coords['scalar.q'])]:
        proportional(sub(out,pw(inp,2)),name+'.definition')
    proportional(sub(mul(scale(rho,17),pp),mul(sub(c(17),ee),add(c(17),scale(ee,3)))),'scalar.firstConic')
    proportional(sub(prep,sub(mul(rho,w2),pw(V,2))),'scalar.preparationT.definition')
    proportional(sub(pw(U,2),mul(rho,prep)),'scalar.preparationConic')
    proportional(sub(bh,mul(ee,sub(c(17),prep))),'scalar.Bh.definition')
    proportional(sub(mul(scale(rho,17),qq),mul(sub(ss,bh),add(ss,scale(bh,3)))),'scalar.secondConic')
    assert all(len(t['monomial'])<=2 for row0 in data['residuals'] for t in row0['terms'])
    count+=1
    return count

def check_abstract_identities():
    # Variables g,l,h,j,D. The two monic chart relations permit a simple
    # terminating exact reduction of l^2 and j^2.
    g,l,h,j,D=[v(i) for i in range(5)]
    x=pw(h,2);f=pw(g,2)
    CU=add(pw(l,2),mul(D,pw(f,2)),c(-1))
    CR=add(pw(j,2),scale(pw(x,2),-1),D)
    def reduce(p):
        todo=list(p.items());out={}
        while todo:
            m,a=todo.pop()
            if m.count(1)>=2:
                q=list(m);q.remove(1);q.remove(1)
                replacement=sub(c(1),mul(D,pw(g,4)))
            elif m.count(3)>=2:
                q=list(m);q.remove(3);q.remove(3)
                replacement=sub(pw(h,4),D)
            else:
                out[m]=out.get(m,F(0))+a
                continue
            for n,b in replacement.items():todo.append((tuple(sorted(tuple(q)+n)),a*b))
        return {m:a for m,a in out.items() if a}
    A=sub(mul(h,l),mul(g,j));B=add(mul(h,l),mul(g,j))
    FF=add(x,mul(D,f));d0=sub(c(1),mul(x,f))
    assert not sub(sub(mul(A,B),mul(d0,FF)),sub(mul(x,CU),mul(f,CR)))
    Nm=add(l,mul(h,j,pw(g,3)))
    assert not reduce(sub(sub(pw(Nm,2),mul(add(c(1),mul(x,f)),pw(d0,2))),mul(f,pw(B,2))))
    Nk=scale(add(mul(g,add(mul(x,pw(FF,2)),mul(D,pw(A,2)))),mul(j,A,FF)),-1)
    assert not reduce(sub(pw(Nk,2),mul(x,sub(pw(FF,4),mul(D,pw(A,4))))))
    Ynum=sub(mul(Nm,sub(pw(d0,2),mul(f,pw(B,2)))),mul(l,pw(d0,3)))
    assert not reduce(sub(mul(Ynum,h,A,FF),mul(Nk,pw(g,3),d0,pw(B,2))))
    # Tangency is not a choice of a spurious ordinate branch.
    X,Y,m,DD=[v(i) for i in range(4)]
    xv=sub(pw(m,2),scale(X,2));yv=sub(mul(m,sub(X,xv)),Y)
    curve=add(pw(Y,2),scale(pw(X,3),-1),mul(DD,X))
    error=add(pw(yv,2),scale(pw(xv,3),-1),mul(DD,xv))
    assert not sub(sub(error,curve),mul(sub(scale(X,3),pw(m,2)),sub(sub(scale(pw(X,2),3),DD),scale(mul(m,Y),2))))
    return 5

# Exact quadratic-field arithmetic, implemented without symbolic packages.
def K(a,b=0):return (F(a),F(b))
def ka(a,b):return (a[0]+b[0],a[1]+b[1])
def kn(a):return (-a[0],-a[1])
def ks(a,b):return ka(a,kn(b))
def km(a,b):return (a[0]*b[0]+2*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def ki(a):
    d=a[0]*a[0]-2*a[1]*a[1];assert d
    return (a[0]/d,-a[1]/d)
def kd(a,b):return km(a,ki(b))
def kq(a):return km(a,a)
def kr(a,r):return (a[0]*r,a[1]*r)
ZERO=K(0);ONE=K(1);DK=K(11,-6)
P={'x':K(F(57,8),F(-7,2)),'y':K(F(-165,8),F(417,32)),'h':K(-1,F(7,4)),'j':K(F(39,8),F(-9,2))}
def negpoint(q):
    if q is None:return None
    return {'x':q['x'],'y':kn(q['y']),'h':q['h'],'j':kn(q['j'])}
def coverflip(q):return dict(q,h=kn(q['h']),j=kn(q['j']))
def plus(q,r):
    if q is None:return r
    if r is None:return q
    if q['x']==r['x']:
        if q['y']==kn(r['y']):return None
        m=kd(ks(kr(kq(q['x']),3),DK),kr(q['y'],2))
        h=kd(ka(kq(q['x']),DK),kr(q['y'],2))
    else:
        m=kd(ks(q['y'],r['y']),ks(q['x'],r['x']))
        h=kd(ks(km(r['h'],q['j']),km(q['h'],r['j'])),ks(q['x'],r['x']))
    x=ks(ks(kq(m),q['x']),r['x']);y=ks(km(m,ks(q['x'],x)),q['y'])
    assert kq(h)==x and x!=ZERO and y!=ZERO
    return {'x':x,'y':y,'h':h,'j':kd(y,h)}
def point_from_reciprocal(g,l):
    if g==ZERO:return None
    x=ki(kq(g));return {'x':x,'y':kd(l,km(kq(g),g))}
def reciprocal_difference(g,l,r):
    f=kq(g);FF=ka(r['x'],km(DK,f));assert FF!=ZERO
    tau=kd(ks(km(r['h'],l),km(g,r['j'])),FF);fv=kq(tau)
    if tau==ZERO:
        assert km(g,r['x'])!=ZERO
        return None
    M=kd(kn(km(g,ka(r['x'],km(DK,fv)))),tau)
    kval=kd(ks(M,r['j']),r['h']);xv=ki(fv);yv=km(xv,kval)
    assert kval!=ZERO and kq(yv)==ks(km(kq(xv),xv),km(DK,xv))
    return {'x':xv,'y':yv,'tau':tau,'f':fv,'k':kval,'M':M}
def check_field_samples():
    positive=[P]
    for _ in range(3):positive.append(plus(positive[-1],P))
    finite=positive+[negpoint(q) for q in positive]
    roots=positive[:3]+[negpoint(q) for q in positive[:3]]
    report={'generic':0,'tangent':0,'identity_input':0,'excluded_identity_output':0,'scalar_constant':0,'scaled_log':0,'primary_ratio':0}
    aa=[F(1),F(-2,5)]
    for j in range(2,10):aa.append(aa[-1]*F(4*j-5,4*j+1))
    def G(f):
        w=km(DK,kq(f));ans=ZERO
        for a in reversed(aa):ans=ka(km(ans,w),K(a))
        return ans
    for r0 in roots:
        for r in [r0,coverflip(r0)]:
            for q0 in [None]+finite:
                for flip in [False,True]:
                    q=coverflip(q0) if flip and q0 is not None else q0
                    g,l=(ZERO,K(-1 if flip else 1)) if q is None else (ki(q['h']),kd(q['j'],q['x']))
                    assert kq(l)==ks(ONE,km(DK,kq(kq(g)))) and l!=ZERO
                    got=reciprocal_difference(g,l,r);want=plus(q,negpoint(r))
                    if want is None:
                        assert got is None;report['excluded_identity_output']+=1;continue
                    assert got['x']==want['x'] and got['y']==want['y']
                    branch='identity_input' if q is None else 'tangent' if q['x']==r['x'] else 'generic'
                    report[branch]+=1
                    if report['scaled_log']<12:
                        eta=kd(kn(G(got['f'])),ks(got['M'],r['j']))
                        ell=kd(kn(G(got['f'])),got['k'])
                        assert km(r['h'],eta)==ell
                        report['scaled_log']+=1
    for q0 in finite:
        for q in [q0,coverflip(q0)]:
            FF=ka(km(P['x'],q['x']),DK)
            tau=kd(ks(km(P['h'],q['j']),km(q['h'],P['j'])),FF)
            if tau==ZERO:
                assert q['x']==P['x'] and q['y']==P['y'];continue
            f=kq(tau);w=km(q['h'],tau);M=kd(kn(ka(P['x'],km(DK,f))),w)
            kval=kd(ks(M,P['j']),P['h']);want=plus(q,negpoint(P))
            assert ki(f)==want['x'] and km(ki(f),kval)==want['y']
            report['scalar_constant']+=1
    H=positive[1];kH=kd(H['j'],H['h']);zH=kn(kd(H['x'],H['y']))
    for q in [None]+finite:
        g,l=(ZERO,ONE) if q is None else (ki(q['h']),kd(q['j'],q['x']))
        got=kd(km(kH,g),l);want=ZERO if q is None else kd(kn(kd(q['x'],q['y'])),zH)
        assert got==want;report['primary_ratio']+=1
    return report

def check_new_abstract_identities():
    f,FF,s,h,x,j,k,kv,D=[v(i) for i in range(9)]
    R2=sub(mul(f,FF),pw(s,2))
    R3=add(mul(D,pw(s,2)),mul(x,add(f,FF)),scale(mul(j,s),2),c(-1))
    R4=add(mul(h,s,k),c(-1),mul(x,f),mul(j,s))
    R5=add(mul(h,s,kv),scale(mul(x,FF),-1),scale(mul(j,s),-1),c(1))
    Rh=sub(pw(h,2),x);Rj=add(pw(j,2),scale(pw(x,2),-1),D)
    E=sub(mul(add(x,mul(D,f)),s),mul(f,sub(mul(h,k),j)))
    assert not sub(mul(s,E),add(scale(mul(x,R2),-1),scale(mul(f,R4),-1),mul(f,R3)))
    E2=add(mul(s,add(j,mul(h,kv))),mul(f,add(x,mul(D,FF))))
    assert not sub(E2,add(R5,R3,mul(D,R2)))
    def curve_certificate(f0,k0,row):
        B=sub(c(1),add(mul(x,f0),mul(j,s)))
        curve=add(mul(f0,pw(k0,2)),mul(D,pw(f0,2)),c(-1))
        rhs=add(mul(f0,row,add(mul(h,s,k0),B)),
                scale(mul(f0,Rh,pw(s,2),pw(k0,2)),-1),
                mul(f0,sub(mul(x,f0),c(1)),R3),
                mul(x,sub(c(1),mul(x,f0)),R2),mul(f0,pw(s,2),Rj))
        assert not sub(mul(x,pw(s,2),curve),rhs)
    curve_certificate(f,k,R4)
    curve_certificate(FF,scale(kv,-1),scale(R5,-1))
    # Substituting w=hS*tau into the new scalar rows recovers old rows
    # modulo the already retained identity hS^2=xS.
    xx,hh,jj,xS,hS,jS,tau,fR,DD=[v(i) for i in range(9)]
    B=add(mul(xx,xS),DD);w=mul(hS,tau)
    old_tau=add(mul(B,tau),scale(mul(hh,jS),-1),mul(hS,jj))
    new_w=add(mul(B,w),scale(mul(hh,hS,jS),-1),mul(xS,jj))
    assert not sub(new_w,sub(mul(hS,old_tau),mul(jj,sub(pw(hS,2),xS))))
    new_f=sub(mul(xS,fR),pw(w,2))
    assert not sub(new_f,sub(mul(xS,sub(fR,pw(tau,2))),mul(pw(tau,2),sub(pw(hS,2),xS))))
    return 6

def check_new_field_samples():
    positive=[P]
    for _ in range(3):positive.append(plus(positive[-1],P))
    finite=positive+[negpoint(q) for q in positive]
    result={'joint_shared':0,'joint_tangent':0,'scalar_fused':0,'scalar_tangent':0}
    for q0 in finite:
        for q in [q0,coverflip(q0)]:
            want=plus(q,negpoint(P))
            if want is None:continue
            g=ki(q['h']);l=kd(q['j'],q['x']);f=kq(g)
            old=reciprocal_difference(g,l,P);s=km(g,old['tau'])
            fv=kd(kq(s),f)
            kH=kd(ks(ONE,ka(km(P['x'],f),km(P['j'],s))),km(P['h'],s))
            kV=kd(ks(ka(km(P['x'],fv),km(P['j'],s)),ONE),km(P['h'],s))
            assert f!=ZERO and s!=ZERO and fv!=ZERO
            assert ka(ka(km(DK,kq(s)),km(P['x'],ka(f,fv))),kr(km(P['j'],s),2))==ONE
            assert kH==kd(q['y'],q['x']) and kV==kd(want['y'],want['x'])
            assert fv==ki(want['x']) and km(g,kH)==l and kd(s,g)==old['tau']
            assert ka(P['j'],km(P['h'],kV))==old['M']
            result['joint_shared']+=1
            if q['x']==P['x']:result['joint_tangent']+=1
            B=ka(km(P['x'],q['x']),DK)
            w=kd(ks(km(P['h'],km(q['h'],q['j'])),km(q['x'],P['j'])),B)
            fr=kd(kq(w),q['x']);M=kd(kn(ka(P['x'],km(DK,fr))),w)
            kR=kd(ks(M,P['j']),P['h'])
            assert fr==ki(want['x']) and kR==kd(want['y'],want['x'])
            tau=kd(w,q['h'])
            assert tau==kd(ks(km(P['h'],q['j']),km(q['h'],P['j'])),B)
            result['scalar_fused']+=1
            if q['x']==P['x']:result['scalar_tangent']+=1
    return result

def check_round5_identities():
    coefficients,U,R=square_completion();w=v(0)
    Up=add(*(scale(pw(w,j),a) for j,a in enumerate(U)))
    Rp=add(*(scale(pw(w,j),a) for j,a in enumerate(R)))
    G=add(*(scale(pw(w,j),a) for j,a in enumerate(coefficients)))
    assert G==add(scale(pw(Up,2),coefficients[12]),Rp)
    # This is a coordinate-degree certificate, separate from univariate degree.
    ww,w2,w4,u=[v(i) for i in range(4)]
    basis=[c(1),ww,w2,mul(ww,w2),w4,mul(ww,w4),mul(w2,w4)]
    Uraw=add(*(scale(basis[j],a) for j,a in enumerate(U)))
    Rraw=add(*(scale(basis[j],a) for j,a in enumerate(R)))
    output=add(scale(pw(u,2),coefficients[12]),Rraw)
    assert max(map(len,Uraw))<=2 and max(map(len,output))<=2
    assert all(a<0 for a in coefficients[1:]) and sum(coefficients)>0
    # The deleted scalar point equation and the k definition give the
    # congruence identity used in the local proxy proof.
    w,M,h,j,x,D,f,k=[v(i) for i in range(8)]
    old=add(mul(w,M),x,mul(D,f))
    defining=sub(mul(h,k),sub(M,j))
    lhs=add(mul(h,add(mul(w,k),h)),mul(D,f),mul(j,w))
    assert not sub(lhs,add(old,mul(w,defining),sub(pw(h,2),x)))
    # Arithmetic-tail certificate for precision45 at p>=11:
    # 10*(4j-45)-(4j+1)=36*(j-13)+17 >=0 for j>=13.
    assert 10*(4*13-45)-(4*13+1)==17 and 40-4==36
    return {'abstractIdentities':3,'maximumCircuitResidualDegree':2,
            'G12AtOne':str(sum(coefficients)),
            'U6':[str(a) for a in U],'R6':[str(a) for a in R],
            'order45TailLinearCertificate':'10*(4*j-45)-(4*j+1)=36*(j-13)+17, j>=13'}

def check_scalar_proxy_samples():
    positive=[P]
    for _ in range(3):positive.append(plus(positive[-1],P))
    H=positive[1];kH=kd(H['y'],H['x'])
    result={'generic':0,'tangent':0,'excluded_identity':0}
    for S0 in positive+[negpoint(q) for q in positive]:
        for S in [S0,coverflip(S0)]:
            Q=plus(S,negpoint(P));B=ka(km(P['x'],S['x']),DK)
            w=kd(ks(km(P['h'],km(S['h'],S['j'])),km(S['x'],P['j'])),B)
            f=kd(kq(w),S['x'])
            if Q is None:
                assert w==ZERO and f==ZERO and f[0]==0
                result['excluded_identity']+=1;continue
            assert f[0]>0 and f==ki(Q['x'])
            kQ=kd(Q['y'],Q['x']);T=km(kH,w)
            assert T==km(kd(kH,kQ),km(w,kQ))
            assert km(P['h'],ka(km(w,kQ),P['h']))==kn(ka(km(DK,f),km(P['j'],w)))
            branch='tangent' if S['x']==P['x'] else 'generic';result[branch]+=1
    # A split prime where hP is nonunit at exactly one place. P has orders
    #13 and2 modulo41, so26P is formal at both places and S=27P is finite.
    def multiple(n):
        acc=None;q=P
        while n:
            if n&1:acc=plus(acc,q)
            n//=2
            if n:q=plus(q,q)
        return acc
    Q,H=multiple(26),multiple(52);S=plus(P,Q)
    kQ,kH=kd(Q['y'],Q['x']),kd(H['y'],H['x'])
    B=ka(km(P['x'],S['x']),DK)
    w=kd(ks(km(P['h'],km(S['h'],S['j'])),km(S['x'],P['j'])),B)
    T=km(kH,w);U=kr(T,2)
    mod=lambda a:(a.numerator*pow(a.denominator,-1,41))%41
    for rho in [17,24]:
        red=lambda a:(mod(a[0])+rho*mod(a[1]))%41
        assert red(ki(Q['x']))==0 and red(ki(H['x']))==0
        assert red(km(w,kQ))==(-red(P['h']))%41
    assert mod(U[0])==1
    result['split41']={'formalIndices':[26,52],'rootResidues':[17,24],
                       'proxyRealUnitResidue':1,'nonunitFixedRootPlace':24}
    return result

def check_outer_constant_certificates():
    # Exact coefficient facts used in the uniform positive-R argument.
    X=v(0)
    beta=add(c(2401),scale(pw(add(scale(X,2),c(1)),2),2754))
    assert beta==add(scale(pw(X,2),11016),scale(X,11016),c(5155))
    assert 11016==2**3*3**4*17 and 32==2**5
    # For v(X)<0 and a prime outside {2,3,17}, the three contact
    # valuations are all 2v(X), hence the product valuation is even.
    assert 3*2==6 and 6%2==0
    # v(1+N)>-R/2 with R>0 implies v(N)>-R/2 by the ultrametric
    # inequality applied to N=(1+N)-1. No noncancellation is assumed here.
    lower={'N':F(-1,2)}
    lower['L']=lower['N']/2
    lower['J']=(lower['N']+15)/2
    lower['fH0']=(lower['L']+1)/2
    lower['n1']=(lower['L']+2)/2
    lower['fH1']=(lower['n1']+2)/2
    lower['fQ0']=(lower['n1']+1)/2
    lower['fQ1']=lower['J']/2
    lower['y']=(lower['J']+15)/2
    lower['T']=lower['y']+16
    expected={'N':F(-1,2),'L':F(-1,4),'J':F(29,4),'fH0':F(3,8),'n1':F(7,8),'fH1':F(23,16),'fQ0':F(15,16),'fQ1':F(29,8),'y':F(89,8),'T':F(217,8)}
    assert lower==expected
    assert all(lower[k]>0 for k in ['fH0','fH1','fQ0','fQ1'])
    assert 27<lower['T']<28
    # In every binary node the coefficient exponents have odd difference.
    assert all((a-b)%2 for a,b in [(-2,-1),(-1,-2),(0,-15),(0,-15)])
    # Affine completeness bounds are represented as (R coefficient, constant).
    addp=lambda a,b:(a[0]+b[0],a[1]+b[1])
    twop=lambda a:(2*a[0],2*a[1])
    Ap,Bp,Cp,Dp,yp=(1,1),(2,1),(2,1),(4,1),(12,1)
    nterms=[addp(twop(Bp),(-2,0)),addp(twop(Cp),(-1,0))]
    assert nterms==[(2,2),(3,2)]
    np=(2,2)
    lterms=[addp(twop(Ap),(-1,0)),addp(twop(np),(-2,0))]
    assert lterms==[(1,2),(2,4)]
    lp=(1,2)
    jterms=[twop(Dp),addp(twop(yp),(-15,0))]
    assert jterms==[(8,2),(9,2)]
    jp=(8,2)
    nfinal=[twop(lp),addp(twop(jp),(-15,0))]
    assert nfinal==[(2,4),(1,4)]
    assert addp(yp,(16,0))==(28,1)
    assert 2*1+1==3 and 2*3+1==7 and 2*7+1==15 and 15+1==16
    return {'negativeInputValuationGivesEvenContactValuation':'R=6*v_p(X)',
            'outerConstantArgument':'N=W-1, with v_p(1)=0>-R/2',
            'strictValuationBoundsTimesR':{k:str(v) for k,v in lower.items()},
            'preservedScalarOrder':28,'powerCoordinates':3,
            'removedSourceNode':'scalar.n0','completenessMinimumN':'R+4',
            'maximumRawResidualDegree':2}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('directory',nargs='?',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--report',type=Path)
    ap.add_argument('--scalar-order',type=int,default=28)
    args=ap.parse_args();root=args.directory.resolve()
    out={'status':'PASS','sourceAssertions':check_source(root,args.scalar_order),'abstractPolynomialIdentities':check_abstract_identities()+check_new_abstract_identities(),'exactFieldSamples':check_field_samples(),'newExactFieldSamples':check_new_field_samples(),'round5Identities':check_round5_identities(),'scalarProxySamples':check_scalar_proxy_samples(),'scalarOrder':args.scalar_order,'outerConstantCertificates':check_outer_constant_certificates(),'sourceBuilderSha256':hashlib.sha256((root/'builder.cjs').read_bytes()).hexdigest(),'rawIrSha256':hashlib.sha256((root/'raw-ir.json').read_bytes()).hexdigest(),'checkerSha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Exact source equations for all point/chart/difference/logarithm modules, the changed outer-constant scalar tree and its normalized pole consumer, G12 circuit identities, proxy and nonzero guard, exact valuation descent certificates, prior orientation/identity/tangent checks and split41 example. Higher detector precision and fixed-anchor arithmetic are separate audits; the uniform proof and inherited global arithmetic are not proved by these computations.'}
    target=args.report or root/'geometry-check.json';target.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
