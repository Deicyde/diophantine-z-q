# C3: break bound (N5 L820-834) and dyadic paragraph (N5 L848-865) on Galois number fields,
# using PARI's ramification groups at one prime P | p (= the local Galois extension).
#  (a) delta := sum_{i>=0}(|G_i|-1) equals v_P(different)   [Hilbert]
#  (b) delta <= e-1+e*v_p(e)
#  (c) delta/e = 1-1/e + int_0^inf (1-1/|G^u|) du   (exact, via Herbrand phi)
#  (d) last upper break u_last <= 2 delta/e
#  (e) p=2 only: U^{3e+1} subset U^4 modulo P^n, n in {5e+2, 6e+3}
import cypari2
from fractions import Fraction as Fr
pari=cypari2.Pari(); pari.allocatemem(2*10**9)
order=pari('(g)->my(o=Vec(g[2]));if(#o,vecprod(o),1)')
fields=[(2,'polcyclo(8)'),(2,'polcyclo(16)'),(2,'polcyclo(32)'),(2,'polcompositum(x^4-2,x^2+1)[1]'),
        (2,'polcompositum(polcyclo(8),x^4-2)[1]'),(2,'polcompositum(x^2-3,polcyclo(8))[1]'),
        (2,'polcompositum(x^3-2,x^2+x+1)[1]'),(2,'polcompositum(x^2+1,x^2-6)[1]'),
        (2,'polcompositum(polcyclo(16),x^2-3)[1]'),
        (3,'polcyclo(9)'),(3,'polcyclo(27)'),(3,'polcompositum(x^3-3,x^2+x+1)[1]'),
        (3,'polcompositum(x^3-2,x^2+x+1)[1]'),(5,'polcyclo(25)'),(5,'polcompositum(x^5-5,polcyclo(5))[1]')]
allok=True
for p,ps in fields:
    pol=pari(ps); nf=pari.nfinit(pol); gal=pari.galoisinit(nf)
    pr=pari.idealprimedec(nf,p)[0]; e=int(pari('(P)->P.e')(pr))
    R=pari.idealramgroups(nf,gal,pr); G=[int(order(g)) for g in R[1:]]  # G[i]=|G_i|, i>=0
    assert G[0]==e
    delta=sum(g-1 for g in G)
    dv=int(pari.idealval(nf,pari('(K)->K.diff')(nf),pr))
    vpe=int(pari.valuation(e,p))
    # upper numbering: phi(m) for integer lower index m, breaks where G_m != G_{m+1}
    phi=lambda m: sum(Fr(G[i],e) for i in range(1,m+1)) if m>=1 else Fr(m)
    breaks=[i for i in range(len(G)) if (G[i+1] if i+1<len(G) else 1)!=G[i]]
    ub=[phi(i) for i in breaks]; ulast=ub[-1] if ub else 0
    integ=Fr(0); prev=Fr(0)
    for i,u in zip(breaks,ub):
        if u>prev: integ+=(u-prev)*(1-Fr(1,G[i]))
        prev=max(prev,u)
    ok=(delta==dv) and delta<=e-1+e*vpe and Fr(delta,e)==1-Fr(1,e)+integ and ulast<=Fr(2*delta,e)
    line=f"p={p} {ps}: e={e} |G_i|={G} delta={delta} vP(diff)={dv} bound={e-1+e*vpe} upper breaks={[str(u) for u in ub]} 2delta/e={Fr(2*delta,e)} ok={ok}"
    if p==2:
        ok4=True
        for n in (5*e+2,6*e+3):
            bid=pari.idealstar(nf,pari.idealpow(nf,pr,n),1)
            cyc=[int(c) for c in pari('(b)->b.cyc')(bid)]
            pi=pari('(P)->P.gen[2]')(pr); deg=int(pari.poldegree(pol)); basis=[pari('matid(%d)[,%d]'%(deg,k+1)) for k in range(deg)]
            for j in range(3*e+1,n):
                for w in basis:
                    x=pari.nfeltadd(nf,1,pari.nfeltmul(nf,pari.nfeltpow(nf,pi,j),w))
                    c=[int(t) for t in pari.ideallog(nf,x,bid)]
                    if any(ci%pari.gcd(4,di)!=0 for ci,di in zip(c,cyc)): ok4=False
        line+=f" U^(3e+1) in U^4: {ok4}"; ok=ok and ok4
    allok&=ok; print(line,flush=True)
print("ALL OK:",allok)
