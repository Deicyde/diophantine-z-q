# C2: local square-root criterion (N5 L683-689), checked on finite levels.
# Claim: a finite-order character psi of Q_p^x has a square root iff psi(-1)=1.
# Unit part check: for psi a character of (Z/p^k)^x, psi = phi^2 for a character phi of
# (Z/p^(k+2))^x  iff  psi(-1)=1.  (Uniformizer factor Z is always 2-divisible.)
import cypari2, itertools
from fractions import Fraction as Fr
pari=cypari2.Pari()
def chars(n):
    G=pari.znstar(n,1); cyc=[int(c) for c in pari("(G)->G.cyc")(G)]
    els=[x for x in range(1,n) if pari.gcd(x,n)==1]
    logs={x:[int(t) for t in pari.znlog(x,G)] for x in els} if cyc else {x:[] for x in els}
    out=[]
    for c in itertools.product(*[range(d) for d in cyc]):
        out.append({x:sum(Fr(ci*li,di) for ci,li,di in zip(c,logs[x],cyc))%1 for x in els})
    return out
bad=0; tested=0
for p,k in [(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(5,1),(5,2),(7,1),(7,2),(11,1),(13,1)]:
    n=p**k; N=p**(k+2)
    low=chars(n); high=chars(N)
    sq=set()
    for ph in high:
        sq.add(tuple(sorted((x,(2*v)%1) for x,v in ph.items())))
    for ps in low:
        lift=tuple(sorted((x,ps[x%n]) for x in high[0].keys()))
        has=lift in sq
        even=(ps[n-1]==0)
        tested+=1
        if has!=even: bad+=1; print("COUNTEREXAMPLE",p,k,ps)
    print(f"p={p} k={k}: {len(low)} characters checked")
print("tested",tested,"mismatches",bad)
