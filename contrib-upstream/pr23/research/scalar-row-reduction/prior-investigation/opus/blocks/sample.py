"""Sample the raw IR over F_p (p=7 mod 8) on its chart varieties; find affine relations among coordinates."""
import json,random,sys
from fractions import Fraction
P=1000000007  # check p%8
assert P%8==7
def frac(s):
    n,d=(s.split('/')+['1'])[:2]; return int(n)*pow(int(d),P-2,P)%P
def sqrt(a):
    a%=P
    if a==0: return 0
    if pow(a,(P-1)//2,P)!=1: return None
    return pow(a,(P+1)//4,P)  # P%4==3
R2=sqrt(2)
def load(path):
    d=json.load(open(path))
    for r in d['residuals']:
        r['t']=[(frac(t['coefficient']),t['monomial'],t['sPower']) for t in r['terms']]
    return d
def ev(r,val,S):
    s=0
    for c,m,sp in r['t']:
        v=c*pow(S,sp,P)
        for i in m: v=v*val[i]%P
        s+=v
    return s%P
def lin(r,val,S,unk):
    # residual linear in unknowns unk; return (const, {u:coef})
    const=0; co={u:0 for u in unk}
    for c,m,sp in r['t']:
        v=c*pow(S,sp,P); us=[i for i in m if i in unk]; 
        for i in m:
            if i not in unk: v=v*val[i]%P
        if not us: const+=v
        elif len(us)==1: co[us[0]]+=v
        else: raise ValueError('nonlinear')
    return const%P,{u:c%P for u,c in co.items()}
def emb(a): return ((a[0]+a[1]*R2)%P,(a[0]-a[1]*R2)%P)
def unemb(p,m): inv2=pow(2,P-2,P); return ((p+m)*inv2%P,(p-m)*inv2*pow(R2,P-2,P)%P)
def kmul(a,b): return ((a[0]*b[0]+2*a[1]*b[1])%P,(a[0]*b[1]+a[1]*b[0])%P)
D=(11,P-6)
def sample(d,S):
    name={c['name']:c['id'] for c in d['coordinates']}
    val={}
    rnd=lambda: random.randrange(1,P)
    for c in d['coordinates']:
        if c['kind'] in ('base','input'): val[c['id']]=rnd()
    # lambda
    val[name['lambda']]=(frac('32/1225')+val[name['lambda.positiveA']]**2+val[name['lambda.positiveB']]**2)%P
    Dp,Dm=emb(D)
    for n in ['A','S','T','Z']:
        while True:
            h=(rnd(),rnd()); x=kmul(h,h); xp,xm=emb(x)
            jp=sqrt(xp*xp-Dp); jm=sqrt(xm*xm-Dm)
            if jp is not None and jm is not None: break
        j=unemb(jp,jm)
        val[name[n+'.chart.h0']],val[name[n+'.chart.h1']]=h; val[name[n+'.chart.j0']],val[name[n+'.chart.j1']]=j
    for n in ['UA','US','UT','UZ']:
        while True:
            g=(rnd(),rnd()); f=kmul(g,g); fp,fm=emb(f)
            lp=sqrt(1-Dp*fp*fp); lm=sqrt(1-Dm*fm*fm)
            if lp is not None and lm is not None: break
        l=unemb(lp,lm)
        val[name[n+'.chart.h0']],val[name[n+'.chart.h1']]=g; val[name[n+'.chart.j0']],val[name[n+'.chart.j1']]=l
    # H joint: s^2 (D fU + xP) + s (2 jP fU) + (xP fU^2 - fU)=0 per embedding
    xP=(frac('57/8'),frac('-7/2')); jP=(frac('39/8'),frac('-9/2'))
    while True:
        g=(rnd(),rnd()); f=kmul(g,g); sol=[]
        for k,(fe,De,xe,je) in enumerate(zip(emb(f),emb(D),emb(xP),emb(jP))):
            a=(De*fe+xe)%P; b=2*je*fe%P; c=(xe*fe*fe-fe)%P
            disc=sqrt(b*b-4*a*c)
            if disc is None: sol=None; break
            sol.append((-b+disc)*pow(2*a,P-2,P)%P)
        if sol: break
    s=unemb(*sol)
    val[name['H.chart.h0']],val[name['H.chart.h1']]=g; val[name['H.chart.j0']],val[name['H.chart.j1']]=s
    res={r['id']:r for r in d['residuals']}
    gates=d['gates']; i=0
    while i<len(gates):
        g=gates[i]
        if g['operation']=='field_quotient_component':
            g2=gates[i+1]; unk=[g['coordinateId'],g2['coordinateId']]
            c1,a1=lin(res[g['definitionResidualId']],val,S,unk); c2,a2=lin(res[g2['definitionResidualId']],val,S,unk)
            det=(a1[unk[0]]*a2[unk[1]]-a1[unk[1]]*a2[unk[0]])%P
            inv=pow(det,P-2,P)
            val[unk[0]]=(-c1*a2[unk[1]]+c2*a1[unk[1]])*inv%P
            val[unk[1]]=(-c2*a1[unk[0]]+c1*a2[unk[0]])*inv%P
            i+=2
        else:
            u=g['coordinateId']; c,a=lin(res[g['definitionResidualId']],val,S,[u])
            val[u]=(-c)*pow(a[u],P-2,P)%P; i+=1
    bad=[r['name'] for r in d['residuals'] if ev(r,val,S)!=0]
    return val,bad
if __name__=='__main__':
    d=load(sys.argv[1]); S=pow(3,2130,P)
    val,bad=sample(d,S); print('nonzero residuals:',bad)
