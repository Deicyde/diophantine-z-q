"""Independently reconstruct the primary-root tests and mixed-order detector products.

Reconstructs the round-eight order45 weights and uniform order12 pair, affine guard98t-1,
the contact-unit normalization and seven-node weights without a stored e, G12/G2 logs and all product consumers. No producer is imported.

Uses only Python's standard library; imports neither builder nor compiler.
The output verifies source equations, not the inherited global theorems.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json

def dec(terms):
    out={}
    for t in terms:
        k=(int(t.get('sPower',0)),tuple(t['monomial']))
        out[k]=out.get(k,F(0))+F(t['coefficient'])
    return {k:v for k,v in out.items() if v}
def const(c):
    c=F(c)
    return {(0,()):c} if c else {}
def add(*polys):
    out={}
    for p in polys:
        for k,v in p.items():out[k]=out.get(k,F(0))+v
    return {k:v for k,v in out.items() if v}
def scale(p,c):return {k:v*F(c) for k,v in p.items() if v*F(c)}
def mul(p,q):
    out={}
    for (s,a),v in p.items():
        for (t,b),w in q.items():
            k=(s+t,tuple(sorted(a+b)))
            out[k]=out.get(k,F(0))+v*w
    return {k:v for k,v in out.items() if v}
def sig(p):
    if not p:return ()
    items=sorted(p.items());lead=items[0][1]
    return tuple((k,v/lead) for k,v in items)
def fmul(a,b):return [add(mul(a[0],b[0]),scale(mul(a[1],b[1]),2)),add(mul(a[0],b[1]),mul(a[1],b[0]))]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('directory',nargs='?',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--report',type=Path);ap.add_argument('--high',type=int,choices=[45],default=45);ap.add_argument('--anchor',default='3^2790');args=ap.parse_args();high=args.high
    d=args.directory.resolve();data=json.loads((d/'raw-ir.json').read_text())
    rows={sig(dec(r['terms'])) for r in data['residuals']}
    names={c['name']:c for c in data['coordinates']}
    vals={k:dec(v['terms']) for k,v in data['values'].items()}
    checked=[]
    def check(label,p):
        assert not p or sig(p) in rows,label
        checked.append(label)
    def var(name):return {(0,(names[name]['id'],)):F(1)}
    def val(name):return vals[name]
    def field(name):return [val(name+'.0'),val(name+'.1')]
    def field_check(label,actual,expected):
        for k in range(2):check(label+'.'+str(k),add(actual[k],scale(expected[k],-1)))
    one=const(1);zero=const(0);fone=[one,zero]
    lam=var('lambda');a=var('lambda.positiveA');b=var('lambda.positiveB')
    check('lambda shifted sum of two squares',add(lam,const(F(-32,1225)),scale(mul(a,a),-1),scale(mul(b,b),-1)))
    assert not any('w0Inverse' in c['name'] for c in data['coordinates'])
    assert not any('w0Inverse' in r['name'] for r in data['residuals'])
    assert not any('w0Inverse' in g['name'] for g in data['guards'])
    dfield=[const(11),const(-6)];acc=fone
    for name in ('A','S','T','Z'):
        h=field(name+'.h');j=field(name+'.j');x=field(name+'.x')
        field_check(name+' square abscissa',x,fmul(h,h))
        j2=fmul(j,j);x2=fmul(x,x)
        for k in range(2):check(name+' root chart '+str(k),add(j2[k],scale(x2[k],-1),dfield[k]))
        new=field('heightProduct.'+name);field_check(name+' height product',new,fmul(acc,x));acc=new
    field_check('height product alias',field('heightProduct'),acc)
    c0,c1=acc;s0=val('heightProduct.scale0');s1=val('heightProduct.scale1')
    check('first square scale',add(s0,scale(mul(c0,c0),-1)))
    check('linear-combination square scale',add(s1,scale(mul(add(c0,c1),add(c0,c1)),-1)))
    assert 'heightProduct.x1Square' not in vals
    checked.append('removed old inner square')
    scales=[one,s0,s1]
    def fconj(a):return [a[0],scale(a[1],-1)]
    # Independently reconstruct G12 by binomial square-root expansion at infinity.
    # This differs from the producer coefficient-by-coefficient subtraction algorithm.
    coeff=[F(1),F(-2,5)]
    for j in range(2,13):coeff.append(coeff[-1]*F(4*j-5,4*j+1))
    assert all(c<0 for c in coeff[1:]) and sum(coeff)>0
    checked.append('G12 positive minimum on [0,1]')
    def uv_mul(a,b,degree):
        out=[F(0)]*(degree+1)
        for i,v in enumerate(a):
            for j,w in enumerate(b):
                if i+j<=degree:out[i+j]+=v*w
        return out
    tail=[F(0)]+[coeff[12-j]/coeff[12] for j in range(1,6)]
    power=[F(1)]+[F(0)]*5;rootseries=power.copy();binom=F(1)
    for k in range(1,6):
        power=uv_mul(power,tail,5);binom*=F(3-2*k,2*k)
        rootseries=[a+binom*b for a,b in zip(rootseries,power)]
    ucoeff=[F(0)]*7
    for k,c in enumerate(rootseries):ucoeff[6-k]=c
    usq=uv_mul(ucoeff,ucoeff,12)
    remainder=[a-coeff[12]*b for a,b in zip(coeff,usq)]
    assert not any(remainder[7:])
    assert [coeff[12]*a+b for a,b in zip(usq,remainder)]==coeff
    checked.append('independent binomial G12 completion identity')
    for i in range(5):
        pre='logV'+str(i);f=field('V'+str(i)+'.f');f2=field(pre+'.fSquare');w=field(pre+'.w')
        field_check(pre+' f square',f2,fmul(f,f));field_check(pre+' w',w,fmul(dfield,f2))
        if i==1:
            w2=fmul(w,w)
            want=[add(fone[k],scale(w[k],coeff[1]),scale(w2[k],coeff[2])) for k in range(2)]
        else:
            w2=field(pre+'.wPower2');w4=field(pre+'.wPower4')
            field_check(pre+' w2',w2,fmul(w,w));field_check(pre+' w4',w4,fmul(w2,w2))
            basis=[fone,w,w2,fmul(w,w2),w4,fmul(w,w4),fmul(w2,w4)]
            u=field(pre+'.squareRoot')
            expectedU=[add(*(scale(basis[j][k],ucoeff[j]) for j in range(7))) for k in range(2)]
            field_check(pre+' square-completion polynomial',u,expectedU)
            u2=fmul(u,u)
            want=[add(scale(u2[k],coeff[12]),*(scale(basis[j][k],remainder[j]) for j in range(7))) for k in range(2)]
        out=field(pre+'.polynomial');field_check(pre+' polynomial',out,want)
        lv=field(pre)
        if i==0:
            prod=fmul(lv,field('V0.k'))
            for k in range(2):check(pre+' quotient '+str(k),add(prod[k],out[k]))
        else:
            eta=field(pre+'.scaled');prod=fmul(eta,field('V'+str(i)+'.logDenominator'))
            for k in range(2):check(pre+' scaled quotient '+str(k),add(prod[k],out[k]))
            field_check(pre+' unscaled alias',lv,fmul(field(['','A','S','T','Z'][i]+'.h'),eta))
    expected=[]
    for name in ('H','UA','US','UT','UZ'):expected.append(field(name+'.g'))
    for i in range(5):expected.append(fconj(field('V'+str(i)+'.f')))
    for i in range(1,5):expected.append([add(a,scale(b,-1)) for a,b in zip(field('L'+str(i)),fconj(field('LP'+str(i))))])
    expected.append([add(field('L1')[0],scale(val('beta'),-1)),field('L1')[1]])
    expected.append([val('Lucas.F0'),val('Lucas.F1')])
    assert len(expected)==16
    for i,z in enumerate(expected):
        actual=field('test'+str(i));assert actual==z,'test semantic alias '+str(i)
        checked.append('test semantic alias '+str(i))
    for name in ('H','UA','US','UT','UZ'):
        field_check(name+' inverse root square',field(name+'.f'),fmul(field(name+'.g'),field(name+'.g')))
    tests={m:[] for m in (1,12,high)}
    for i in range(16):
        m=12 if i in (1,10) else high if i==0 or i>=11 else 1
        j=len(tests[m]);z=field('test'+str(i));zs=field('testSquare.'+str(m)+'.'+str(j))
        field_check('test square '+str(i),zs,fmul(z,z));tests[m].append(zs)
    def product(name,ys):
        if len(ys)==1:return [fone,ys[0]]
        cut=len(ys)//2;left=product(name+'.left',ys[:cut]);right=product(name+'.right',ys[cut:]);out=[fone]
        for k in range(1,len(left)+len(right)-1):
            p=[zero,zero]
            for i in range(max(0,k-len(right)+1),min(k,len(left)-1)+1):
                q=fmul(left[i],right[k-i]);p=[add(p[j],q[j]) for j in range(2)]
            actual=field(name+'.co'+str(k));field_check(name+'.co'+str(k),actual,p);out.append(actual)
        return out
    assert len(tests[12])==2 and len(tests[1])==8 and len(tests[high])==6
    mixed1,mixed12=tests[12]
    mixedProduct=field('mixedTestProduct')
    field_check('mixed coefficient product',mixedProduct,fmul(mixed1,mixed12))
    co={}
    for m,sizes in ((1,[4,4]),(high,[3,3])):
        pos=0;co[m]=[]
        for j,size in enumerate(sizes):
            co[m].append(product('symmetric.'+str(m)+'.group'+str(j),tests[m][pos:pos+size]));pos+=size
        assert pos==len(tests[m])
    for r in range(3):
        pre='detector'+str(r);q1=val(pre+'.q1');qhigh=val(pre+'.q'+str(high))
        t=val(pre+'.t');delta=add(scale(t,98),const(-1));A=scales[r]
        check(pre+' scaled parameter',add(t,scale(mul(A,lam),-1)))
        cs=[F(1)]
        for root in (F(0),F(-1,49),F(-1,50),F(-1,2450),F(-32,1225)):
            nxt=[F(0)]*(len(cs)+1)
            for k,c in enumerate(cs):nxt[k]+=root*c;nxt[k+1]+=c
            cs=nxt
        t2=val(pre+'.Fsquare');middle=val(pre+'.Fmiddle');ft=val(pre+'.F')
        check(pre+' F square',add(t2,scale(mul(t,t),-1)))
        check(pre+' F middle',add(middle,scale(add(mul(t2,add(t,const(cs[4]))),scale(t,cs[3]),const(cs[2])),-1)))
        check(pre+' F final',add(ft,scale(add(mul(t2,middle),scale(t,cs[1]),const(cs[0])),-1)))
        ad=val(pre+'.Adelta');ad2=val(pre+'.Adelta4.half.square');ad4=val(pre+'.Adelta4.square')
        check(pre+' A delta',add(ad,scale(mul(A,delta),-1)))
        check(pre+' A delta square',add(ad2,scale(mul(ad,ad),-1)))
        check(pre+' A delta fourth',add(ad4,scale(mul(ad2,ad2),-1)))
        check(pre+' direct order1 weight',add(mul(ft,q1),scale(mul(ad4,A),-1)))
        d2=val(pre+'.delta2')
        check(pre+' delta square',add(d2,scale(mul(delta,delta),-1)))
        E=val(pre+'.eDelta')
        check(pre+' inverse R',add(E,scale(mul(q1,d2),-1)))
        assert pre+'.eWeight' not in vals and pre+'.delta3' not in vals
        q1square=val(pre+'.q1SquaredForWeights');q1cube=val(pre+'.q1CubedForWeights')
        check(pre+' early order1 square',add(q1square,scale(mul(q1,q1),-1)))
        check(pre+' early order1 cube',add(q1cube,scale(mul(q1square,q1),-1)))
        ma,mb,mc,md=[val(pre+'.mix'+letter) for letter in 'ABCD']
        q12=val(pre+'.q12');mh=val(pre+'.mixedHigh')
        check(pre+' mixed weight A',add(ma,scale(mul(E,E),-1)))
        check(pre+' mixed weight B',add(mb,scale(mul(ma,E),-1)))
        check(pre+' mixed weight C',add(mc,scale(mul(mb,q1cube),-1)))
        check(pre+' mixed weight D',add(md,scale(mul(mc,mc),-1)))
        check(pre+' low weight',add(mul(E,q12),scale(mul(md,md),-1)))
        check(pre+' high intermediate square',add(mh,scale(mul(q12,q12),-1)))
        check(pre+' high weight',add(mul(q1cube,qhigh),scale(mul(mh,mh),-1)))
        assert q1square==val(pre+'.E1.power2')
        assert q1cube==val(pre+'.E1.power3')
        checked.extend([pre+' existing square reused',pre+' existing cube reused'])
        products=[]
        for m,q in ((1,q1),(high,qhigh)):
            name=pre+'.E'+str(m);maxdeg=max(len(c)-1 for c in co[m]);powers=[one,q]
            for k in range(2,maxdeg+1):
                actual=val(name+'.power'+str(k));check(name+' power '+str(k),add(actual,scale(mul(powers[k//2],powers[(k+1)//2]),-1)));powers.append(actual)
            acc=fone
            for j,c in enumerate(co[m]):
                p=[zero,zero]
                for k,cj in enumerate(c):p=[add(p[z],mul(cj[z],powers[k])) for z in range(2)]
                factor=field(name+'.block'+str(j));field_check(name+' factor '+str(j),factor,p)
                new=field(name+'.product'+str(j));field_check(name+' product '+str(j),new,fmul(acc,factor));acc=new
            field_check(name+' alias',field(name),acc);products.append(acc)
        pure=field(pre+'.pure');field_check(pre+' pure product',pure,fmul(*products))
        assert pre+'.q1q12' not in vals
        assert not any(c['name'].startswith(pre+'.q1q12') for c in data['coordinates'])
        checked.append(pre+' obsolete mixed-weight product absent')
        mixed=field(pre+'.mixed')
        want=[add(one,mul(q12,add(mixed1[0],mixed12[0])),mul(mh,mixedProduct[0])),
              add(mul(q12,add(mixed1[1],mixed12[1])),mul(mh,mixedProduct[1]))]
        field_check(pre+' mixed factor',mixed,want)
        w=field(pre+'.W');field_check(pre+' full product',w,fmul(pure,mixed))
        n=val(pre+'.normOver2w0');check(pre+' norm quotient',add(mul(w[0],n),scale(mul(w[0],w[0]),F(-1,2)),mul(w[1],w[1])))
        check(pre+' pole input',add(mul(val(pre+'.B'),val(pre+'.eDelta')),scale(mul(n,n),-1)))
    assert data['fixedParameter']=={'name':'S','value':args.anchor,'coordinate':False}
    checked.append('requested fixed anchor declaration')
    assert max(sp+len(m) for row in data['residuals'] for sp,m in dec(row['terms']))<=2
    checked.append('all source residuals quadratic after S lifting')
    contact=[F(0),F(1,49),F(1,50),F(1,2450),F(32,1225)]
    assert [98*x-1 for x in contact]==[F(-1),F(1),F(24,25),F(-24,25),F(39,25)]
    assert min(F(32,1225)-x for x in contact)>=0
    assert 98*F(32,1225)-1>0
    checked.append('new contact values and guard positivity threshold')
    # One fully expanded symbolic identity for the mixed block, independent of IR aliases.
    def av(i):return {(0,(i,)):F(1)}
    avA=[av(0),av(1)];avB=[av(2),av(3)];u=av(4);v=u
    left=fmul([add(one,mul(u,avA[0])),mul(u,avA[1])],
              [add(one,mul(v,avB[0])),mul(v,avB[1])])
    ab=fmul(avA,avB);uv=mul(u,v)
    right=[add(one,mul(u,avA[0]),mul(v,avB[0]),mul(uv,ab[0])),
           add(mul(u,avA[1]),mul(v,avB[1]),mul(uv,ab[1]))]
    assert left==right
    # Independently reconstruct each Laurent exponent pair (e, delta).
    def exponent_op(a,b,c=(0,0)):return tuple(x+y-z for x,y,z in zip(a,b,c))
    ep=(1,0);delta=(0,1);E=exponent_op(ep,delta);q1=(1,-1)
    cube=exponent_op(exponent_op(q1,q1),q1)
    ma=exponent_op(E,E);mb=exponent_op(ma,E)
    mc=exponent_op(mb,cube);md=exponent_op(mc,mc)
    low=exponent_op(md,md,E);mh=exponent_op(low,low);hi=exponent_op(mh,mh,cube)
    exponent_pairs=[ma,mb,mc,md,low,mh,hi]
    assert exponent_pairs==[(2,2),(3,3),(6,0),(12,0),(23,-1),(46,-2),(89,-1)]
    assert low==(2*12-1,-1) and hi==(2*high-1,-1)
    # Multiplying semantic tests by delta changes delta^-3 to delta^-1.
    for order in (1,12,high):
        assert exponent_op((2*order-1,-3),(0,2))==(2*order-1,-1)
    report={'status':'PASS','abstractLaurentIdentities':7,'semanticNormalizationIdentities':3,'laurentExponentPairs':exponent_pairs,'abstractUniformPairIdentities':2,'testOrders':[high,12,1,1,1,1,1,1,1,1,12,high,high,high,high,high],'sourceAssertions':len(checked),'checks':checked,'rawCounts':data['counts'],'builderSha256':hashlib.sha256((d/'builder.cjs').read_bytes()).hexdigest(),'rawIrSha256':hashlib.sha256((d/'raw-ir.json').read_bytes()).hexdigest(),'highOrder':high,'anchor':args.anchor,'guard':'98*t-1','thirdScale':'(C0+C1)^2','scope':'Exact G12/G2 source polynomials and consumers, including independently generated completion coefficients, primary inverse-root test aliases with U_A strengthened to order12, uniform order12 pair reusing the stored q12 square, orders1/12/high, all product circuits and seven-node weight powers with actual common subexpression reuse and no stored e or delta cube, affine guard98t-1, shorter positive square scale and norm consumers. Uniform local/completeness proofs are separate; inherited global arithmetic not verified.'}
    (args.report or d/'detector-source-check.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2))
if __name__=='__main__':main()
