# Check each local statement separately against brute-force local solubility (selmer.loc_p / loc_inf):
# LocalReal: Loc_R(a,b) <-> a > 0.  Local2 (l=3 mod 4): Loc_2 <-> a odd and b = 1 mod 4.
# Local3 (l = 2 mod 3): Loc_3 <-> b = 1 mod 3.  LocalBad (q | l): Loc_q <-> (a,b) in span{(l,1),(3,-l)}.
# LocalGood (p not dividing 6l): Loc_p <-> p does not divide a, b.
import sys
sys.path.insert(0,'scratch/pc-from-rc')
from selmer import factor, loc_p, loc_inf, sqfree_divs
from compare import cls_q, add
bad=0; n=0
samples=[l for l in range(11,400) if l%12==11 and len(set(factor(l)))==len(factor(l))][:12]
for l in samples:
    fs=factor(l)
    goodps=[p for p in [5,7,11,13,17,19,23] if (6*l)%p][:2]
    cands=sqfree_divs([2,3]+fs+goodps[:1])
    for a in cands:
        for b in cands:
            n+=1
            r=(loc_inf(l,a,b) == (a>0))
            r2=(loc_p(l,a,b,2) == (a%2==1 and b%4==1))
            r3=(loc_p(l,a,b,3) == (b%3==1))
            rq=True
            for q in fs:
                span=set()
                for e1 in (0,1):
                    for e2 in (0,1):
                        A=(0,0);B=(0,0)
                        if e1: A=add(A,cls_q(l,q))
                        if e2: A=add(A,cls_q(3,q)); B=add(B,cls_q(-l,q))
                        span.add((A,B))
                rq = rq and (loc_p(l,a,b,q) == ((cls_q(a,q),cls_q(b,q)) in span))
            p=goodps[0]
            rg=(loc_p(l,a,b,p) == (a%p!=0 and b%p!=0))
            if not (r and r2 and r3 and rq and rg):
                bad+=1; print("MISMATCH",l,a,b,r,r2,r3,rq,rg)
print("samples",len(samples),"pairs",n,"mismatches",bad)
